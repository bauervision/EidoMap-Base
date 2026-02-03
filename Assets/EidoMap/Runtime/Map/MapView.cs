// Assets/EidoMap/Runtime/Maps/MapView.cs
using System.Collections;
using System.Collections.Generic;
using UnityEngine;
using UnityEngine.EventSystems;
using UnityEngine.Networking;
using UnityEngine.UI;
using EidoMap.Core;
using EidoMap.Web;

namespace EidoMap
{

    [System.Serializable]
    public struct AoiBounds
    {
        public float minLat, maxLat, minLon, maxLon;
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
        IBeginDragHandler, IDragHandler, IEndDragHandler, IScrollHandler
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
        public RectTransform aoiRect;           // Semi-transparent Image (Raycast Target = Off)

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

        [Header("Debug")]
        public bool debugCrosshair = true;
        public bool debugZoomLogs = true;
        public Color preColor = new Color(1f, 0f, 0f, 0.95f);
        public Color postColor = new Color(0f, 1f, 0f, 0.95f);
        public bool debugMouseCross = true;

        public Color mouseColor = new Color(0.2f, 0.6f, 1f, 0.95f); // blue
        public float crosshairSize = 14f;





        private Canvas _rootCanvas;
        private Camera _uiCam;

        private TileViewPool _tilePool;
        private TileMath.Vector2d _centerPx;
        private Vector2 _dragStart;
        private bool _aoiActive;
        private Vector2 _aoiStartLocal;
        private AoiBounds _lastAoi;

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
            if (!mapRoot || !tilesParent)
                Debug.LogWarning("MapView: Assign mapRoot and tilesParent in the inspector.");

            if (aoiRect)
            {
                // AOI math assumes bottom-left pivot, raycast off
                aoiRect.pivot = new Vector2(0f, 0f);
                var aoiImg = aoiRect.GetComponent<Graphic>();
                if (aoiImg) aoiImg.raycastTarget = false;
                aoiRect.gameObject.SetActive(false);
            }

            // Initialize centerPx ONCE from inspector values
            _centerPx = TileMath.LatLonToPixel(centerLat, centerLon, zoom);

            var (tx, ty) = TileMath.PixelToTile(_centerPx.x, _centerPx.y);
            Debug.Log($"[EidoMap] inferred tileSize ~= {_centerPx.x / tx:0.###} px/tile (should be ~{WORLD_TILE_PX})");

            if (autoAlignTilesParent && tilesParent && mapRoot)
            {
                AlignToParentRect(tilesParent, mapRoot);
            }
            if (logRectTransforms)
            {
                Debug.Log(RTInfo("mapRoot", mapRoot));
                Debug.Log(RTInfo("tilesParent", tilesParent));
            }

            _tilePool = new TileViewPool(tilesParent, displayTilePixels);
            _streamer = new TileStreamer(this, maxConcurrent);

            RebuildTiles();
            if (debugCrosshair && tilesParent != null)
            {
                _dbg = new Diagnostics.MapDebugOverlay(tilesParent, mapRoot, crosshairSize);
                _dbg.Ensure(preColor, postColor, debugMouseCross, mouseColor);
            }

            Debug.Log($"[EidoMap] canvas.scaleFactor={_rootCanvas?.scaleFactor ?? 1f:0.###} displayTilePixels={displayTilePixels}");

        }

        void Update()
        {
            // Keyboard zoom fallback
            int d = 0;
            if (Input.GetKeyDown(zoomInKey) || Input.GetKeyDown(KeyCode.KeypadPlus)) d++;
            if (Input.GetKeyDown(zoomOutKey) || Input.GetKeyDown(KeyCode.KeypadMinus)) d--;
            if (d != 0) ZoomBy(d, null);

            MaybeEndInteracting();
        }

        /* ---------------- Public API ---------------- */

        public AoiBounds GetLastAoi() => _lastAoi;

        public void SetCenter(double lat, double lon, int? newZoom = null)
        {
            if (newZoom.HasValue) zoom = Mathf.Clamp(newZoom.Value, minZoom, maxZoom);
            centerLat = lat; centerLon = lon;
            _centerPx = TileMath.LatLonToPixel(centerLat, centerLon, zoom);
            RebuildTiles();
        }




    }



}
