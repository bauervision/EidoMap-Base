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
    [System.Serializable]
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

        private TerrainLayer _runtimeLayer;
        private Texture2D _lastCapturedAoiTexture;

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

        /* ---------------- AOI -> Lat/Lon Bounds ---------------- */

        public AoiBounds GetAoiBounds()
        {
            if (!mapRoot || !aoiRect)
                return default;

            // AOI rect world corners: 0=BL, 1=TL, 2=TR, 3=BR
            var wc = new Vector3[4];
            aoiRect.GetWorldCorners(wc);

            Vector2 bl = RectTransformUtility.WorldToScreenPoint(_uiCam, wc[0]);
            Vector2 tl = RectTransformUtility.WorldToScreenPoint(_uiCam, wc[1]);
            Vector2 tr = RectTransformUtility.WorldToScreenPoint(_uiCam, wc[2]);
            Vector2 br = RectTransformUtility.WorldToScreenPoint(_uiCam, wc[3]);

            // Map viewport center in screen px
            Vector2 mapCenterScreen = GetMapRootScreenCenter();

            // Convert each corner: screen px -> world px -> lat/lon
            var ll_bl = ScreenToLatLon(bl, mapCenterScreen);
            var ll_tl = ScreenToLatLon(tl, mapCenterScreen);
            var ll_tr = ScreenToLatLon(tr, mapCenterScreen);
            var ll_br = ScreenToLatLon(br, mapCenterScreen);

            float minLat = Mathf.Min((float)ll_bl.lat, (float)ll_tl.lat, (float)ll_tr.lat, (float)ll_br.lat);
            float maxLat = Mathf.Max((float)ll_bl.lat, (float)ll_tl.lat, (float)ll_tr.lat, (float)ll_br.lat);
            float minLon = Mathf.Min((float)ll_bl.lon, (float)ll_tl.lon, (float)ll_tr.lon, (float)ll_br.lon);
            float maxLon = Mathf.Max((float)ll_bl.lon, (float)ll_tl.lon, (float)ll_tr.lon, (float)ll_br.lon);

            var b = new AoiBounds { minLat = minLat, maxLat = maxLat, minLon = minLon, maxLon = maxLon };

            if (debugAoiBounds)
                Debug.Log($"[EidoMap] AOI bounds z={zoom} {b}");

            return b;
        }

        private Vector2 GetMapRootScreenCenter()
        {
            // mapRoot is the viewport rect we are rendering into
            var wc = new Vector3[4];
            mapRoot.GetWorldCorners(wc);

            Vector2 bl = RectTransformUtility.WorldToScreenPoint(_uiCam, wc[0]);
            Vector2 tr = RectTransformUtility.WorldToScreenPoint(_uiCam, wc[2]);
            return (bl + tr) * 0.5f;
        }

        private (double lat, double lon) ScreenToLatLon(Vector2 screenPx, Vector2 mapCenterScreen)
        {
            // UI pixel delta from center of mapRoot
            double dxUi = screenPx.x - mapCenterScreen.x;
            double dyUi = screenPx.y - mapCenterScreen.y;

            // Convert UI pixels to world pixels using current zoom + displayTilePixels.
            double uiToWorldScale = WORLD_TILE_PX / displayTilePixels;


            // UI +Y is up; world/tile +Y is down -> subtract dy
            double worldX = _centerPx.x + dxUi * uiToWorldScale;
            double worldY = _centerPx.y - dyUi * uiToWorldScale;

            var ll = TileMath.PixelToLatLon(worldX, worldY, zoom);

            return (ll.lat, ll.lon);
        }

        private void UpdateAoiReadout()
        {
            if (!aoiReadoutText || !aoiRect || !mapRoot) return;

            AoiBounds b = GetAoiBounds();

            // width: distance west->east at mid-lat
            double midLat = (b.minLat + b.maxLat) * 0.5;
            double widthM = HaversineMeters(midLat, b.minLon, midLat, b.maxLon);

            // height: distance south->north at mid-lon
            double midLon = (b.minLon + b.maxLon) * 0.5;
            double heightM = HaversineMeters(b.minLat, midLon, b.maxLat, midLon);

            aoiReadoutText.text =
                $"AOI (z={zoom})\n" +
                $"N {b.maxLat:F6}\n" +
                $"S {b.minLat:F6}\n" +
                $"W {b.minLon:F6}\n" +
                $"E {b.maxLon:F6}\n" +
                $"Size {(widthM / 1000.0):F2} km x {(heightM / 1000.0):F2} km";
        }


        private static double HaversineMeters(double lat1, double lon1, double lat2, double lon2)
        {
            const double R = 6371000.0; // meters
            double dLat = (lat2 - lat1) * Mathf.Deg2Rad;
            double dLon = (lon2 - lon1) * Mathf.Deg2Rad;

            double a =
                Math.Sin(dLat * 0.5) * Math.Sin(dLat * 0.5) +
                Math.Cos(lat1 * Mathf.Deg2Rad) * Math.Cos(lat2 * Mathf.Deg2Rad) *
                Math.Sin(dLon * 0.5) * Math.Sin(dLon * 0.5);

            double c = 2.0 * Math.Atan2(Math.Sqrt(a), Math.Sqrt(1.0 - a));
            return R * c;
        }


        public void CaptureAoiStaticImagery()
        {
            if (!useMapbox)
            {
                Debug.LogWarning("[EidoMap] CaptureAoiStaticImagery requires useMapbox=true.");
                return;
            }

            var b = GetAoiBounds(); // your existing AOI bounds (lat/lon)

            string url = BuildMapboxStaticImageUrl(b, captureResolution, captureResolution, captureHiDpi);
            if (debugStaticUrl) Debug.Log($"[EidoMap] Static URL: {url}");

            StartCoroutine(DownloadTexture(url, tex =>
            {
                if (!tex)
                {
                    Debug.LogWarning("[EidoMap] Static imagery download returned null texture.");
                    return;
                }

                Debug.Log($"[EidoMap] Static imagery OK: {tex.width}x{tex.height}");

                // v1: just keep it around; next step we’ll apply to Terrain.
                _lastCapturedAoiTexture = tex;
                ApplyCapturedTextureToTerrain(tex);

            }));
        }



        private string BuildMapboxStaticImageUrl(AoiBounds b, int w, int h, bool hidpi)
        {
            // Mapbox wants [minLon,minLat,maxLon,maxLat]
            string bbox = $"[{b.minLon.ToString(System.Globalization.CultureInfo.InvariantCulture)}," +
                          $"{b.minLat.ToString(System.Globalization.CultureInfo.InvariantCulture)}," +
                          $"{b.maxLon.ToString(System.Globalization.CultureInfo.InvariantCulture)}," +
                          $"{b.maxLat.ToString(System.Globalization.CultureInfo.InvariantCulture)}]";

            string size = $"{w}x{h}" + (hidpi ? "@2x" : "");

            // styleId in your project is like "mapbox/satellite-streets-v12"
            // Static Images expects styles/v1/{styleId}/static/...
            return $"https://api.mapbox.com/styles/v1/{mapboxStyleId}/static/{bbox}/{size}?access_token={mapboxAccessToken}";
        }

        private IEnumerator DownloadTexture(string url, System.Action<Texture2D> onDone)
        {
            using (var req = UnityWebRequestTexture.GetTexture(url))
            {
                yield return req.SendWebRequest();

                if (req.result != UnityWebRequest.Result.Success)
                {
                    Debug.LogWarning($"[EidoMap] Static imagery download failed: {req.error}");
                    onDone?.Invoke(null);
                    yield break;
                }

                var tex = DownloadHandlerTexture.GetContent(req);
                onDone?.Invoke(tex);
            }
        }


        private void ApplyCapturedTextureToTerrain(Texture2D tex)
        {
            if (!tex) return;

            if (!targetTerrain)
            {
                Debug.LogWarning("[EidoMap] No targetTerrain assigned. Drag a Terrain into MapView.targetTerrain.");
                return;
            }

            var td = targetTerrain.terrainData;
            if (!td)
            {
                Debug.LogWarning("[EidoMap] targetTerrain has no TerrainData.");
                return;
            }

            TerrainLayer layer = null;

            if (reuseTerrainLayer)
            {
                if (_runtimeLayer == null)
                {
                    _runtimeLayer = new TerrainLayer();
                    _runtimeLayer.name = "AOI Runtime Layer";
                }
                layer = _runtimeLayer;
            }
            else
            {
                layer = new TerrainLayer();
                layer.name = "AOI Runtime Layer";
            }

            layer.diffuseTexture = tex;

            // Make the texture map across the whole terrain. We’ll refine this once heightmap + bounds mapping lands.
            layer.tileSize = new Vector2(td.size.x, td.size.z);
            layer.tileOffset = Vector2.zero;

            td.terrainLayers = new TerrainLayer[] { layer };

            // Nudge Unity to refresh
            td.SetBaseMapDirty();
            targetTerrain.Flush();

            Debug.Log($"[EidoMap] Applied AOI imagery to Terrain. tex={tex.width}x{tex.height} tileSize={layer.tileSize}");
        }


    }
}
