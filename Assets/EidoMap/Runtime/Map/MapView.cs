// Assets/EidoMap/Runtime/Maps/MapView.cs
using System.Collections;
using System.Collections.Generic;
using UnityEngine;
using UnityEngine.EventSystems;
using UnityEngine.Networking;
using UnityEngine.UI;
using TMPro;
using EidoMap.Web;
using System;

namespace EidoMap
{
    [Serializable]
    public struct AoiBounds
    {
        public float minLat, maxLat, minLon, maxLon;

        public override string ToString()
        {
            return $"lat[{minLat:F6},{maxLat:F6}] lon[{minLon:F6},{maxLon:F6}]";
        }
    }

    [Serializable]
    public struct TerrainRequest
    {
        public AoiBounds bounds;
        public int zoom;
        public int imageryResolution; // e.g. 1024, 2048
    }


    /// <summary>
    /// EidoMap.MapView — lightweight slippy-map UI with AOI selection & Mapbox tiles.
    /// - Pan: drag
    /// - AOI: hold Shift (WebGL) or Alt/Shift (Editor/Desktop) and drag
    /// - Zoom: mouse wheel (cursor-centric), '=' / '-' keys
    /// Includes:
    ///   • Coroutine loader with concurrency cap (no threading issues)
    ///   • Cross-zoom LRU cache
    ///   • Parent-tile UV fallback while children stream
    ///   • Deferred trim to avoid “holes” on zoom
    /// </summary>
    public partial class MapView : MonoBehaviour,
        IDragHandler, IEndDragHandler, IScrollHandler
    {
        /* ---------------- Config: Map ---------------- */
        [Header("Map")]
        public RectTransform mapRoot;           // Fullscreen RectTransform under Canvas
        public RectTransform tilesParent;       // Child of mapRoot; tiles are placed here
        [Range(1, 20)] public int zoom = 14;
        public double centerLat = 37.305373;
        public double centerLon = -80.611872;
        [Tooltip("2 → 5x5 grid")]
        [Range(1, 6)]
        public int halfTiles = 2;

        [Header("Tiles (fallback template if not using Mapbox)")]
        [TextArea] public string imageryUrlTemplate = "https://tile.openstreetmap.org/{z}/{x}/{y}.png";

        [Header("Mapbox (recommended)")]
        public bool useMapbox = false;
        public string mapboxStyleId = "mapbox/satellite-streets-v12"; // e.g., mapbox/satellite-v9, streets-v12
        [TextArea] public string mapboxAccessToken = "<YOUR_MAPBOX_TOKEN>";
        [Tooltip("UI display size per tile; 512 is crisper, 256 is faster")]
        [Range(256, 512)] public int displayTilePixels = 512;

        [Header("AOI")]
        public RectTransform aoiRect;           // Center frame (Raycast Target = Off recommended)
        public bool debugAoiBounds = false;     // logs AOI bounds when requested

        [Header("AOI Debug UI")]
        public TextMeshProUGUI aoiReadoutText; // drag AOIReadout Text here

        [Header("Terrain Preview Target")]
        public Terrain targetTerrain;

        [Tooltip("Optional: keep and reuse a single layer asset at runtime")]
        public bool reuseTerrainLayer = true;


        [Header("Static Imagery Capture")]
        public int captureResolution = 1024;
        public bool captureHiDpi = false; // @2x, optional
        public bool debugStaticUrl = false;


        [Header("Rendering")]
        public bool pixelSnap = true;           // Snap tile positions to whole pixels

        [Header("Zoom")]
        public int minZoom = 2;
        public int maxZoom = 19;
        public int wheelZoomStep = 1;
        public bool zoomTowardCursor = true;    // keep the point under the cursor stable
        public KeyCode zoomInKey = KeyCode.Equals;     // (= / + with Shift)
        public KeyCode zoomOutKey = KeyCode.Minus;     // (-)

        [Header("Layout")]
        public bool autoAlignTilesParent = true;
        public bool logRectTransforms = true;

        [Header("Streaming")]
        public int maxConcurrent = 8;           // simultaneous downloads
        public bool prefetchRing = true;        // request one extra ring around view
        public bool keepTilesOnZoom = true;     // keep old tiles; swap when new arrive
        [Tooltip("Prefer 256px server tiles briefly while interacting to reduce stall")]
        public bool speedWhileInteracting = true;
        public float interactHoldSeconds = 0.25f;

        [Header("Caching")]
        [Tooltip("Max tiles kept in RAM across all zooms (LRU)")]
        public int maxCachedTiles = 256;
        [Tooltip("Use a parent tile quadrant while the higher-zoom child streams")]
        public int parentFallbackDepth = 0;     // 0=off, 1=parent, 2=grandparent

        [Header("Trimming")]
        public bool deferredTrim = true;        // delay trimming to avoid flicker
        public float trimDelaySeconds = 0.35f;

        [Header("Segmentation")]
        [SerializeField] private bool runSegmentationOnCapture = true;
        [SerializeField] private EidoMap.Runtime.Terrain.Ai.SegmentationRunner segmentationRunner;


        private Canvas _rootCanvas;
        private Camera _uiCam;
        private TileViewPool _tilePool;
        private TileMath.Vector2d _centerPx;
        private Vector2 _dragStart;

        private Diagnostics.MapDebugOverlay _dbg;

        private bool _interacting;
        private float _lastInteractTime;

        private struct TileJob { public int x, y, z, epoch; public RawImage img; }

        void Awake()
        {
            _rootCanvas = mapRoot ? mapRoot.GetComponentInParent<Canvas>() : GetComponentInParent<Canvas>();
            if (_rootCanvas != null)
                _uiCam = (_rootCanvas.renderMode == RenderMode.ScreenSpaceOverlay) ? null : _rootCanvas.worldCamera;

        }

        void Start()
        {
            // Initialize centerPx ONCE from inspector values
            _centerPx = TileMath.LatLonToPixel(centerLat, centerLon, zoom);

            if (autoAlignTilesParent && tilesParent && mapRoot)
            {
                AlignToParentRect(tilesParent, mapRoot);
            }

            _tilePool = new TileViewPool(tilesParent, displayTilePixels);
            _streamer = new TileStreamer(this, maxConcurrent);

            RebuildTiles();
        }

        void Update()
        {
            // Keyboard zoom fallback
            int d = 0;
            if (Input.GetKeyDown(zoomInKey) || Input.GetKeyDown(KeyCode.KeypadPlus)) d++;
            if (Input.GetKeyDown(zoomOutKey) || Input.GetKeyDown(KeyCode.KeypadMinus)) d--;
            if (d != 0) ZoomBy(d, null);

            MaybeEndInteracting();
            UpdateAoiReadout();

        }

        public void SetCenter(double lat, double lon, int? newZoom = null)
        {
            if (newZoom.HasValue) zoom = Mathf.Clamp(newZoom.Value, minZoom, maxZoom);
            centerLat = lat; centerLon = lon;
            _centerPx = TileMath.LatLonToPixel(centerLat, centerLon, zoom);
            RebuildTiles();
        }


    }
}
