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
    public class MapView : MonoBehaviour,
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
        public int parentFallbackDepth = 2;     // 0=off, 1=parent, 2=grandparent

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




        /* ---------------- Internals ---------------- */

        // Convert screen position to tilesParent *world* point, then to its exact local.
        // This path avoids subtle biases from nested RectTransforms.
        bool ScreenToTilesLocal(Vector2 screen, out Vector2 local)
        {
            local = default;
            if (!tilesParent) return false;
            // Canonical: converts screen to *tilesParent local* directly
            return RectTransformUtility.ScreenPointToLocalPointInRectangle(
                tilesParent, screen, _uiCam, out local);
        }


        // UI px -> Mercator "world px" (256px per tile)
        double UiToWorldScale()
        {
            // PointerEventData.position is in SCREEN PIXELS.
            // Your tiles are sized in CANVAS UNITS (sizeDelta).
            // CanvasScaler makes 1 canvas unit = scaleFactor screen pixels.
            // We need WORLD px per SCREEN px:
            //   worldPxPerScreenPx = worldPxPerCanvasUnit / screenPxPerCanvasUnit
            //   = (256 / displayTilePixels) / scaleFactor
            double sf = (_rootCanvas != null) ? _rootCanvas.scaleFactor : 1.0;
            if (sf <= 0.0001) sf = 1.0;
            return WORLD_TILE_PX / (displayTilePixels * sf);
        }

        double CanvasToScreenScale()
        {
            double sf = (_rootCanvas != null) ? _rootCanvas.scaleFactor : 1.0;
            if (sf <= 0.0001) sf = 1.0;
            return sf;
        }


        private Canvas _rootCanvas;
        private Camera _uiCam;

        const int WORLD_TILE_PX = 256;          // Slippy math uses 256px “world” tiles

        private TileViewPool _tilePool;
        private TileMath.Vector2d _centerPx;
        private Vector2 _dragStart;
        private bool _aoiActive;
        private Vector2 _aoiStartLocal;
        private AoiBounds _lastAoi;

        private Diagnostics.MapDebugOverlay _dbg;



        private int _epoch;                  // bump to cancel stale loads after zoom
        private bool _interacting;
        private float _lastInteractTime;
        private readonly HashSet<TileKey> _loading = new();

        // Cross-zoom LRU cache
        private readonly Dictionary<TileKey, Texture2D> _cache = new();
        private readonly LinkedList<TileKey> _lru = new();
        // most-recent at front

        private TileStreamer _streamer;


        // Deferred trim
        private HashSet<TileKey> _lastNeededForTrim;
        private Coroutine _deferredTrimCo;

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

        /* ---------------- Slippy core ---------------- */

        void RebuildTiles()
        {
            // Determine center tile at current zoom
            var (cTileX, cTileY) = TileMath.PixelToTile(_centerPx.x, _centerPx.y);

            // Plan which tiles we need (view grid + optional prefetch ring)
            var needed = new HashSet<TileKey>();
            TilePlanner.ComputeNeeded(
                zoom,
                cTileX,
                cTileY,
                halfTiles,
                prefetchRing,
                needed
            );

            // Ensure each needed tile exists, is positioned, and is either shown from cache or enqueued
            foreach (var tk in needed)
            {
                int tx = tk.x;
                int ty = tk.y;

                // Ensure UI view exists
                var img = _tilePool.GetOrCreate(tx, ty);

                // Ensure size matches current setting (pool also enforces this)
                img.rectTransform.sizeDelta = new Vector2(displayTilePixels, displayTilePixels);

                PositionTile(img.rectTransform, tx, ty);

                // Try cache first
                if (TryGetFromCache(tx, ty, zoom, out var cached))
                {
                    img.uvRect = new Rect(0, 0, 1, 1);
                    img.texture = cached;
                }
                else
                {
                    // Parent fallback (cropped UV) while child streams
                    if (parentFallbackDepth > 0)
                        TrySetParentFallback(img, tx, ty, zoom, parentFallbackDepth);

                    RequestTile(tx, ty, zoom, img);
                }
            }

            // Save needed set for trimming
            _lastNeededForTrim = needed;

            // Trim strategy
            if (deferredTrim)
            {
                if (_deferredTrimCo != null) StopCoroutine(_deferredTrimCo);
                _deferredTrimCo = StartCoroutine(DeferredTrimAfterSettled());
            }
            else
            {
                TrimTiles(needed);
            }

            if (debugCrosshair && _dbg != null) _dbg.BringToFront();
        }



        void TrimTiles(HashSet<TileKey> needed)
        {
            if (_tilePool == null) return;
            _tilePool.Trim(needed, zoom);
        }


        IEnumerator DeferredTrimAfterSettled()
        {
            yield return new WaitForSeconds(trimDelaySeconds);
            while (_streamer != null && _streamer.ActiveLoads > 0) yield return null;
            if (_lastNeededForTrim != null) TrimTiles(_lastNeededForTrim);
            _deferredTrimCo = null;
        }

        void PositionTile(RectTransform rt, int tx, int ty)
        {
            int n = 1 << zoom;

            // continuous center in tile units
            double cx = _centerPx.x / WORLD_TILE_PX;
            double cy = _centerPx.y / WORLD_TILE_PX;

            // center tile integer (for wrap-relative deltas)
            int cTileX = (int)System.Math.Floor(cx);
            int cTileY = (int)System.Math.Floor(cy);

            // shortest wrapped dx,dy in tile units (integer tiles)
            int dxTiles = WrapDelta(tx - cTileX, n);
            int dyTiles = WrapDelta(ty - cTileY, n);

            // now incorporate the *fractional* center offset within the tile
            double fracX = cx - cTileX;
            double fracY = cy - cTileY;

            // desired position in UI pixels
            double ox = (dxTiles - fracX) * displayTilePixels;
            double oy = (dyTiles - fracY) * displayTilePixels;

            // invert Y (UI up, tile down)
            double px = ox;
            double py = -oy;

            if (pixelSnap)
            {
                px = System.Math.Round(px);
                py = System.Math.Round(py);
            }

            rt.anchoredPosition = new Vector2((float)px, (float)py);
        }

        // returns delta in [-n/2, +n/2] range
        static int WrapDelta(int d, int n)
        {
            d %= n;
            if (d > n / 2) d -= n;
            if (d < -n / 2) d += n;
            return d;
        }


        /* ---------------- Loader (queue + coroutines) ---------------- */
        string GetTileUrl(int tx, int ty, int z)
        {
            if (useMapbox)
            {
                int serverTileSize =
                    (speedWhileInteracting && _interacting) ? 256 :
                    (displayTilePixels >= 512 ? 512 : 256);

                return TileUrlBuilder.BuildMapboxStyleUrl(
                    mapboxStyleId,
                    mapboxAccessToken,
                    tx, ty, z,
                    serverTileSize
                );
            }

            return TileUrlBuilder.BuildTemplateUrl(imageryUrlTemplate, tx, ty, z);
        }


        void RequestTile(int tx, int ty, int z, RawImage img)
        {
            var key = new TileKey(z, tx, ty);

            // Avoid requesting if already cached (extra guard)
            if (TryGetFromCache(tx, ty, z, out var cached))
            {
                img.uvRect = new Rect(0, 0, 1, 1);
                img.texture = cached;
                return;
            }

            // Build URL (same logic you already validated)
            string url = GetTileUrl(tx, ty, z);

            if (useMapbox)
            {
                int serverTileSize =
                    (speedWhileInteracting && _interacting) ? 256 :
                    (displayTilePixels >= 512 ? 512 : 256);

                url = TileUrlBuilder.BuildMapboxStyleUrl(
                    mapboxStyleId,
                    mapboxAccessToken,
                    tx, ty, z,
                    serverTileSize
                );
            }
            else
            {
                url = TileUrlBuilder.BuildTemplateUrl(imageryUrlTemplate, tx, ty, z);
            }

            // Mark as in-flight (mirror old behavior)
            if (_loading.Contains(key)) return;
            _loading.Add(key);

            var localEpoch = _epoch;

            _streamer.RequestTile(new EidoMap.Web.TileStreamer.Request
            {
                key = key,
                epoch = localEpoch,
                url = url,
                onSuccess = tex =>
                {
                    if (localEpoch != _epoch) return;
                    if (!img) return;

                    img.uvRect = new Rect(0, 0, 1, 1);
                    img.texture = tex;

                    PutInCache(tx, ty, z, tex);
                    _loading.Remove(key);
                },
                onFail = err =>
                {
                    Debug.LogWarning($"Tile load failed {url}: {err}");
                    _loading.Remove(key);
                }
            });

        }



        /* ---------------- Input: pan, zoom, AOI ---------------- */

        public void OnBeginDrag(PointerEventData e)
        {
            if (!RectTransformUtility.RectangleContainsScreenPoint(mapRoot, e.position))
                return;

            _dragStart = e.position;

            if (ModKeyDown() && aoiRect)
            {
                _aoiActive = true;
                RectTransformUtility.ScreenPointToWorldPointInRectangle(mapRoot, e.position, _uiCam, out var w);
                _aoiStartLocal = mapRoot.InverseTransformPoint(w);
                aoiRect.gameObject.SetActive(true);
                aoiRect.anchoredPosition = _aoiStartLocal;
                aoiRect.sizeDelta = Vector2.zero;
            }
        }

        public void OnDrag(PointerEventData e)
        {
            MarkInteracting();

            if (_aoiActive && aoiRect)
            {
                RectTransformUtility.ScreenPointToWorldPointInRectangle(mapRoot, e.position, _uiCam, out var w);
                var now = (Vector2)mapRoot.InverseTransformPoint(w);
                Vector2 min = Vector2.Min(_aoiStartLocal, now);
                Vector2 max = Vector2.Max(_aoiStartLocal, now);
                aoiRect.anchoredPosition = min;
                aoiRect.sizeDelta = max - min;
                return;
            }

            // Pan map: UI +Y up, tile-space +Y down → flip Y once here
            var delta = (Vector2)e.position - _dragStart;
            _dragStart = e.position;

            double s = UiToWorldScale();
            _centerPx = MapViewportMath.PanCenterPx(_centerPx, delta.x, delta.y, s);


            var (lat, lon) = TileMath.PixelToLatLon(_centerPx.x, _centerPx.y, zoom);
            centerLat = lat; centerLon = lon;

            // Reposition currently-present tiles (cheap)
            if (_tilePool != null)
            {
                foreach (var kv in _tilePool.Enumerate())
                {
                    var (tx, ty) = kv.Key;
                    var img = kv.Value;
                    if (!img) continue;
                    PositionTile(img.rectTransform, tx, ty);
                }
            }

        }

        public void OnEndDrag(PointerEventData e)
        {
            if (_aoiActive)
            {
                _aoiActive = false;

                var rect = aoiRect;
                // Top-left & bottom-right in mapRoot local
                Vector2 tlLocal = rect.anchoredPosition + new Vector2(0, rect.sizeDelta.y);
                Vector2 brLocal = rect.anchoredPosition + rect.sizeDelta;

                double s = UiToWorldScale();

                var aoi = AoiMath.ComputeBoundsFromLocalCorners(
                    _centerPx,
                    zoom,
                    tlLocal,
                    brLocal,
                    s
                );

                // Keep MapView's public API struct in sync
                _lastAoi = new AoiBounds
                {
                    minLat = aoi.minLat,
                    maxLat = aoi.maxLat,
                    minLon = aoi.minLon,
                    maxLon = aoi.maxLon
                };

                Debug.Log($"AOI: lat[{_lastAoi.minLat:F6},{_lastAoi.maxLat:F6}] lon[{_lastAoi.minLon:F6},{_lastAoi.maxLon:F6}]");
                rect.gameObject.SetActive(false); // optional
            }

            // Snap-refresh grid around new center/zoom
            RebuildTiles();
        }

        public void OnScroll(PointerEventData e)
        {
            float dy = e.scrollDelta.y;
            if (Mathf.Abs(dy) < 0.01f) return;

            int delta = dy > 0 ? +wheelZoomStep : -wheelZoomStep;

            // Screen -> tilesParent local (canvas units)
            Vector2 local;
            bool haveLocal = ScreenToTilesLocal(e.position, out local);

            // Debug overlay (pre)
            if (debugCrosshair && _dbg != null)
            {
                _dbg.HideAll();
                if (haveLocal) _dbg.SetPre(local);
                _dbg.BringToFront();
            }

            // --- PRE: geo under cursor (lat/lon) at OLD zoom ---
            int zOld = zoom;

            double s = UiToWorldScale(); // world px per UI px (since scaleFactor=1, UI px == screen px)
            double cxOld = _centerPx.x / WORLD_TILE_PX;
            double cyOld = _centerPx.y / WORLD_TILE_PX;

            // local UI -> tile units
            double lx = haveLocal ? (local.x * s) / WORLD_TILE_PX : 0.0;
            double ly = haveLocal ? (local.y * s) / WORLD_TILE_PX : 0.0;

            // geo point under cursor in TILE units (old zoom)
            double uOld = cxOld + lx;
            double vOld = cyOld - ly;

            double pxOld = uOld * WORLD_TILE_PX;
            double pyOld = vOld * WORLD_TILE_PX;

            if (haveLocal)
            {
                var (latOld, lonOld) = TileMath.PixelToLatLon(pxOld, pyOld, zOld);
                UnityEngine.Debug.Log($"[EidoMap:CursorGeo PRE] z={zOld} lat={latOld:0.000000} lon={lonOld:0.000000}");
                if (debugZoomLogs) UnityEngine.Debug.Log($"[EidoMap:OnScroll:local]{local}");
            }

            // --- ZOOM ---
            ZoomBy(delta, e.position, haveLocal ? (Vector2?)local : null);

            // --- POST: geo under cursor (lat/lon) at NEW zoom ---
            int zNew = zoom;

            double cxNew = _centerPx.x / WORLD_TILE_PX;
            double cyNew = _centerPx.y / WORLD_TILE_PX;

            // recompute local -> tile units at new zoom using same local & same s
            double lxPost = haveLocal ? (local.x * s) / WORLD_TILE_PX : 0.0;
            double lyPost = haveLocal ? (local.y * s) / WORLD_TILE_PX : 0.0;

            double uPost = cxNew + lxPost;
            double vPost = cyNew - lyPost;

            double pxNew = uPost * WORLD_TILE_PX;
            double pyNew = vPost * WORLD_TILE_PX;

            if (haveLocal)
            {
                var (latNew, lonNew) = TileMath.PixelToLatLon(pxNew, pyNew, zNew);
                UnityEngine.Debug.Log($"[EidoMap:CursorGeo POST] z={zNew} lat={latNew:0.000000} lon={lonNew:0.000000}");
            }

            // Debug overlay (post) — show where the *old* geo point would land after zoom
            if (debugCrosshair && _dbg != null && haveLocal)
            {
                // Where that same geo ends up after zoom (tile units scale with zoom)
                double f = System.Math.Pow(2.0, zNew - zOld);
                double uScaled = uOld * f;
                double vScaled = vOld * f;

                float lxNew = (float)((uScaled - cxNew) * WORLD_TILE_PX / s);
                float lyNew = (float)((cyNew - vScaled) * WORLD_TILE_PX / s);

                _dbg.SetPost(new Vector2(lxNew, lyNew));
                _dbg.BringToFront();
            }

            // Optional: zoom calc dump (unchanged format)
            if (debugZoomLogs && haveLocal)
            {
                DumpZoomCalc("OnScroll",
                    zOld, zNew,
                    cxOld, cyOld,
                    local.x, local.y, lx, ly,
                    uOld, vOld, uOld * System.Math.Pow(2.0, zNew - zOld), vOld * System.Math.Pow(2.0, zNew - zOld),
                    cxNew, cyNew);
            }
        }




        // Back-compat wrapper: callers that don't pass tilesLocalOverride still work
        void ZoomBy(int delta, Vector2? screenPos)
        {
            ZoomBy(delta, screenPos, null);
        }

        void ZoomBy(int delta, Vector2? screenPos, Vector2? tilesLocalOverride)
        {
            MarkInteracting();

            int oldZ = zoom;
            int newZ = Mathf.Clamp(zoom + delta, minZoom, maxZoom);
            if (newZ == oldZ) return;

            // current center in continuous TILE units (not pixels)
            double cx = _centerPx.x / WORLD_TILE_PX;
            double cy = _centerPx.y / WORLD_TILE_PX;

            // Always initialize; set via override or ScreenToTilesLocal
            Vector2 local = default;
            bool haveLocal = false;

            if (tilesLocalOverride.HasValue)
            {
                local = tilesLocalOverride.Value;
                haveLocal = true;
            }
            else if (screenPos.HasValue && ScreenToTilesLocal(screenPos.Value, out local))
            {
                haveLocal = true;
            }

            if (zoomTowardCursor && haveLocal)
            {
                // UI local -> world px -> TILE units (match pan math)
                double sf = CanvasToScreenScale();

                _centerPx = MapViewportMath.ZoomCenterPxTowardCursor(
                    _centerPx,
                    oldZ,
                    newZ,
                    (float)(local.x * sf),   // convert canvas units -> screen px
                    (float)(local.y * sf),
                    WORLD_TILE_PX,
                    UiToWorldScale()         // now truly world px per screen px
                );

                if (debugZoomLogs)
                {
                    var (errX, errY) = MapViewportMath.CursorLockErrorUiPx(
                        // old/new centers
                        new TileMath.Vector2d(cx * WORLD_TILE_PX, cy * WORLD_TILE_PX), // old center in px
                        _centerPx,
                        oldZ, newZ,
                        local.x, local.y,
                        WORLD_TILE_PX,
                        sf
                    );

                    Debug.Log($"[EidoMap:ZoomLockErr UIpx] ({errX:0.###}, {errY:0.###})");
                }

            }
            else
            {
                // Keep current geo center (no cursor lock)
                var pNewCenter = TileMath.LatLonToPixel(centerLat, centerLon, newZ);
                _centerPx = pNewCenter;

                if (debugZoomLogs)
                    Debug.Log("[EidoMap:ZoomBy] no cursor-lock (no local)");
            }

            zoom = newZ;


            // Keep Inspector in sync (optional; doesn’t affect placement)
            var (latC, lonC) = TileMath.PixelToLatLon(_centerPx.x, _centerPx.y, zoom);
            centerLat = latC; centerLon = lonC;

            // Invalidate in-flight loads from previous zoom and request new tiles
            _epoch++;
            // IMPORTANT: tile views are keyed by (x,y) only; on zoom change those represent different tiles.
            // Clearing prevents old-zoom textures from being shown in new-zoom positions.
            if (_tilePool != null)
                _tilePool.Clear();

            RebuildTiles();
        }





        /* ---------------- Cache & helpers ---------------- */

        private static bool ModKeyDown()
        {
#if UNITY_WEBGL && !UNITY_EDITOR
            // Browsers often intercept Alt — use Shift in WebGL
            return Input.GetKey(KeyCode.LeftShift) || Input.GetKey(KeyCode.RightShift);
#else
            // In Editor/Desktop, allow Alt or Shift to start AOI draw
            return Input.GetKey(KeyCode.LeftAlt) || Input.GetKey(KeyCode.RightAlt)
                || Input.GetKey(KeyCode.LeftShift) || Input.GetKey(KeyCode.RightShift);
#endif
        }

        void MarkInteracting() { _interacting = true; _lastInteractTime = Time.time; }
        void MaybeEndInteracting()
        {
            if (_interacting && Time.time - _lastInteractTime > interactHoldSeconds)
                _interacting = false;
        }


        bool TryGetFromCache(int x, int y, int z, out Texture2D tex)
        {
            var k = new TileKey(z, x, y);
            if (_cache.TryGetValue(k, out tex))
            {
                _lru.Remove(k);
                _lru.AddFirst(k);
                return true;
            }
            return false;
        }

        void PutInCache(int x, int y, int z, Texture2D tex)
        {
            var k = new TileKey(z, x, y);

            if (_cache.ContainsKey(k))
            {
                _cache[k] = tex;
                _lru.Remove(k);
                _lru.AddFirst(k);
                return;
            }

            _cache[k] = tex;
            _lru.AddFirst(k);

            while (_lru.Count > maxCachedTiles)
            {
                var tail = _lru.Last.Value;
                _lru.RemoveLast();
                _cache.Remove(tail);
                // Don't Destroy() here — RawImages may still reference it.
            }
        }




        // Parent fallback: show lower-zoom tile quadrant while child streams
        bool TrySetParentFallback(RawImage img, int x, int y, int z, int maxDepth = 2)
        {
            var child = new TileKey(z, x, y);

            for (int d = 1; d <= maxDepth; d++)
            {
                if (!ParentFallbackResolver.TryResolve(child, d, minZoom, out var res))
                    break;

                // Cache lookup is still owned by MapView (textures live here)
                if (_cache.TryGetValue(res.parentKey, out var parentTex) && parentTex != null)
                {
                    // Touch LRU (same behavior as TryGetFromCache)
                    _lru.Remove(res.parentKey);
                    _lru.AddFirst(res.parentKey);

                    img.texture = parentTex;
                    img.uvRect = res.uv;
                    return true;
                }
            }

            return false;
        }


        /* ---------------- Types ---------------- */

        [System.Serializable]
        public struct AoiBounds
        {
            public float minLat, maxLat, minLon, maxLon;
        }





        // small helper for clean logs
        [System.Diagnostics.Conditional("UNITY_EDITOR")]
        void DumpZoomCalc(
    string tag,
    int zOld, int zNew,
    double cxOld, double cyOld,
    double localX, double localY, double lx, double ly,
    double uOld, double vOld, double uNew, double vNew,
    double cxNew, double cyNew)
        {
            Debug.Log(
        $@"[EidoMap:{tag}]
  zoom: {zOld} → {zNew}  scale f=2^(Δz)={System.Math.Pow(2.0, zNew - zOld):0.########}
  center OLD tiles: cx={cxOld:0.######}  cy={cyOld:0.######}
  local UI px: x={localX:0.##}  y={localY:0.##}
  local UI → tiles: lx={lx:0.######}  ly={ly:0.######}
  geo under cursor (OLD tiles): uOld={uOld:0.######}  vOld={vOld:0.######}
  geo under cursor (NEW tiles): uNew={uNew:0.######}  vNew={vNew:0.######}
  center NEW tiles (computed):   cxNew={cxNew:0.######}  cyNew={cyNew:0.######}
  expected post local (tiles):   (uNew-cxNew)={(uNew - cxNew):0.######} , (cyNew-vNew)={(cyNew - vNew):0.######}
  expected post local (UI px):   x={(uNew - cxNew) * displayTilePixels:0.##} , y={(cyNew - vNew) * displayTilePixels:0.##}
");
        }



        static void AlignToParentRect(RectTransform child, RectTransform parent)
        {
            if (!child || !parent) return;
            child.anchorMin = Vector2.zero;
            child.anchorMax = Vector2.one;
            child.pivot = new Vector2(0.5f, 0.5f);
            child.anchoredPosition = Vector2.zero;
            child.sizeDelta = Vector2.zero;
            child.localScale = Vector3.one;
        }

        static string RTInfo(string label, RectTransform rt)
        {
            if (!rt) return $"{label}: <null>";
            var r = rt.rect;
            return $"{label}: pos={rt.anchoredPosition} sizeΔ={rt.sizeDelta} " +
                   $"anch=({rt.anchorMin}->{rt.anchorMax}) pivot={rt.pivot} " +
                   $"rect(w={r.width:0.##},h={r.height:0.##}) scale={rt.localScale}";
        }




    }


}
