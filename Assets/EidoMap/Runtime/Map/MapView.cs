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




        /* ---------------- Internals ---------------- */

        // Convert screen position to tilesParent *world* point, then to its exact local.
        // This path avoids subtle biases from nested RectTransforms.
        bool ScreenToTilesLocal(Vector2 screenPos, out Vector2 local)
        {
            local = default;
            if (!tilesParent) return false;

            // For ScreenSpaceOverlay: cam must be null.
            // For ScreenSpaceCamera / WorldSpace: use the canvas' worldCamera.
            Camera cam = null;
            if (_rootCanvas != null && _rootCanvas.renderMode != RenderMode.ScreenSpaceOverlay)
                cam = _uiCam;

            return RectTransformUtility.ScreenPointToLocalPointInRectangle(
                tilesParent,
                screenPos,
                cam,
                out local
            );
        }



        // TileMath is clearly operating in 512px-per-tile pixel space (based on your logs).
        const int WORLD_TILE_PX = 512; // IMPORTANT: must match TileMath pixel space

        double UiToWorldScale()
        {
            double sf = (_rootCanvas != null) ? _rootCanvas.scaleFactor : 1.0;
            if (sf <= 0.0001) sf = 1.0;

            // world px per screen px
            return WORLD_TILE_PX / (displayTilePixels * sf);
        }


        private Canvas _rootCanvas;
        private Camera _uiCam;



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
        private readonly HashSet<(int epoch, TileKey key)> _loading = new();

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

        /* ---------------- Slippy core ---------------- */

        void RebuildTiles()
        {
            var (cTileX, cTileY) = TileMath.PixelToTile(_centerPx.x, _centerPx.y);
            Debug.Log($"[EidoMap] centerTile z={zoom} ({cTileX},{cTileY}) centerPx=({_centerPx.x:0.##},{_centerPx.y:0.##})");

            var needed = new HashSet<TileKey>();
            TilePlanner.ComputeNeeded(zoom, cTileX, cTileY, halfTiles, prefetchRing, needed);

            foreach (var tk in needed)
            {
                int tx = tk.x;
                int ty = tk.y;

                var img = _tilePool.GetOrCreate(tx, ty);
                img.rectTransform.sizeDelta = new Vector2(displayTilePixels, displayTilePixels);

                var tag = img.GetComponent<TileViewTag>();
                if (tag == null) tag = img.gameObject.AddComponent<TileViewTag>();
                tag.Set(tx, ty, zoom, _epoch);

                PositionTile(img.rectTransform, tx, ty);

                if (TryGetFromCache(tx, ty, zoom, out var cached))
                {
                    img.uvRect = new Rect(0, 0, 1, 1);
                    img.texture = cached;
                }
                else
                {
                    if (parentFallbackDepth > 0)
                        TrySetParentFallback(img, tx, ty, zoom, parentFallbackDepth);

                    RequestTile(tx, ty, zoom, img);
                }
            }

            _lastNeededForTrim = needed;

            if (deferredTrim)
            {
                if (_deferredTrimCo != null) StopCoroutine(_deferredTrimCo);
                _deferredTrimCo = StartCoroutine(DeferredTrimAfterSettled());
            }
            else TrimTiles(needed);

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

            // continuous center in tile units (MUST match TileMath’s pixel basis)
            double cx = _centerPx.x / WORLD_TILE_PX;
            double cy = _centerPx.y / WORLD_TILE_PX;

            int cTileX = (int)System.Math.Floor(cx);
            int cTileY = (int)System.Math.Floor(cy);

            double fracX = cx - cTileX;
            double fracY = cy - cTileY;

            int dxTiles = WrapDelta(tx - cTileX, n);
            int dyTiles = WrapDelta(ty - cTileY, n);

            // tile centers: (tx+0.5, ty+0.5)
            double ox = (dxTiles + 0.5 - fracX) * displayTilePixels;
            double oy = (dyTiles + 0.5 - fracY) * displayTilePixels;

            double px = ox;
            double py = -oy;

            if (pixelSnap)
            {
                px = System.Math.Round(px);
                py = System.Math.Round(py);
            }

            rt.anchoredPosition = new Vector2((float)px, (float)py);
        }



        static int WrapDelta(int d, int n)
        {
            d %= n;
            if (d > n / 2) d -= n;
            if (d < -n / 2) d += n;
            return d;
        }



        void RequestTile(int tx, int ty, int z, RawImage img)
        {
            if (!img) return;

            int localEpoch = _epoch;

            int n = 1 << z;
            int xReq = Mod(tx, n);
            int yReq = Mod(ty, n);

            var key = new TileKey(z, xReq, yReq);

            var tag = img.GetComponent<TileViewTag>();
            if (tag == null) tag = img.gameObject.AddComponent<TileViewTag>();
            tag.Set(tx, ty, z, localEpoch); // NOTE: keep tag in *view* coords (tx/ty)

            if (TryGetFromCache(xReq, yReq, z, out var cached))
            {
                img.uvRect = new Rect(0, 0, 1, 1);
                img.texture = cached;
                return;
            }

            string url = useMapbox
                ? EidoMap.Web.TileUrlBuilder.BuildMapboxStyleUrl(
                    mapboxStyleId, mapboxAccessToken, xReq, yReq, z,
                    (speedWhileInteracting && _interacting) ? 256 : (displayTilePixels >= 512 ? 512 : 256)
                  )
                : EidoMap.Web.TileUrlBuilder.BuildTemplateUrl(imageryUrlTemplate, xReq, yReq, z);

            if (debugZoomLogs)
            {
                var (cTx, cTy) = TileMath.PixelToTile(_centerPx.x, _centerPx.y);
                if (z == zoom && tx == cTx && ty == cTy)
                    Debug.Log($"[EidoMap] CENTER TILE z={z} x={xReq} y={yReq} url={url}");
            }

            var loadKey = (localEpoch, key);
            if (_loading.Contains(loadKey)) return;
            _loading.Add(loadKey);

            _streamer.RequestTile(new EidoMap.Web.TileStreamer.Request
            {
                key = key,
                epoch = localEpoch,
                url = url,

                onSuccess = tex =>
                {
                    if (localEpoch != _epoch) { _loading.Remove(loadKey); return; }
                    if (!img) { _loading.Remove(loadKey); return; }

                    var liveTag = img.GetComponent<TileViewTag>();
                    if (liveTag == null || !liveTag.Matches(tx, ty, z, localEpoch))
                    {
                        _loading.Remove(loadKey);
                        return;
                    }

                    img.uvRect = new Rect(0, 0, 1, 1);
                    img.texture = tex;

                    PutInCache(xReq, yReq, z, tex);
                    _loading.Remove(loadKey);
                },

                onFail = err =>
                {
                    Debug.LogWarning($"Tile load failed {url}: {err}");
                    _loading.Remove(loadKey);
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

            if (haveLocal)
            {
                var cursorPxOld = CursorPixelFromCenterPx(_centerPx, zOld, local);
                var (latOld, lonOld) = TileMath.PixelToLatLon(cursorPxOld.x, cursorPxOld.y, zOld);
                Debug.Log($"[EidoMap:CursorGeo PRE] z={zOld} lat={latOld:0.000000} lon={lonOld:0.000000}");
                if (debugZoomLogs) Debug.Log($"[EidoMap:OnScroll:local]{local}");
            }

            // --- ZOOM ---
            ZoomBy(delta, e.position, haveLocal ? (Vector2?)local : null);

            // --- POST: geo under cursor (lat/lon) at NEW zoom ---
            int zNew = zoom;

            if (haveLocal)
            {
                var cursorPxNew = CursorPixelFromCenterPx(_centerPx, zNew, local);
                var (latNew, lonNew) = TileMath.PixelToLatLon(cursorPxNew.x, cursorPxNew.y, zNew);
                Debug.Log($"[EidoMap:CursorGeo POST] z={zNew} lat={latNew:0.000000} lon={lonNew:0.000000}");
            }

            // Debug overlay (post) — show where the *old* geo point would land after zoom
            if (debugCrosshair && _dbg != null && haveLocal)
            {
                // Recompute "old cursor geo" then project it at new zoom to show where it lands
                var cursorPxOld = CursorPixelFromCenterPx(_centerPx, zNew, local); // NOTE: center already updated
                                                                                   // We want: the pixel that should be under cursor equals cursorPxOld by construction.
                                                                                   // So the post crosshair should land exactly where the cursor local point is (same local).
                                                                                   // Still, keep this for visual confirmation:
                _dbg.SetPost(local);
                _dbg.BringToFront();
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
                // 1) Geo under cursor at OLD zoom
                var cursorPxOld = CursorPixelFromCenterPx(_centerPx, oldZ, local);
                var (latUnder, lonUnder) = TileMath.PixelToLatLon(cursorPxOld.x, cursorPxOld.y, oldZ);

                // 2) That same geo at NEW zoom
                var geoPxNew = TileMath.LatLonToPixel(latUnder, lonUnder, newZ);

                // 3) Recenter so the cursor stays on that geo
                var off = CursorOffsetWorldPx(local);
                _centerPx = new TileMath.Vector2d(
                    geoPxNew.x - off.x,
                    geoPxNew.y + off.y
                );
            }
            else
            {
                _centerPx = TileMath.LatLonToPixel(centerLat, centerLon, newZ);
            }

            zoom = newZ;

            var (latC, lonC) = TileMath.PixelToLatLon(_centerPx.x, _centerPx.y, zoom);
            centerLat = latC;
            centerLon = lonC;

            _epoch++;
            if (_tilePool != null) _tilePool.Clear();

            RebuildTiles();
        }




        // -----------------------------
        // Helpers (drop-in)
        // -----------------------------

        // Returns cursor offset from center in WORLD PIXELS.
        // localCanvas is tilesParent local in CANVAS UNITS.
        TileMath.Vector2d CursorOffsetWorldPx(Vector2 local)
        {
            double worldPerUi = WORLD_TILE_PX / displayTilePixels; // NO scaleFactor
            return new TileMath.Vector2d(local.x * worldPerUi, local.y * worldPerUi);
        }


        // Computes the world pixel coordinate under the cursor given a centerPx.
        // World pixel +Y is down; UI local +Y is up, so subtract Y offset.
        TileMath.Vector2d CursorPixelFromCenterPx(TileMath.Vector2d centerPx, int z, Vector2 localCanvas)
        {
            var off = CursorOffsetWorldPx(localCanvas);
            return new TileMath.Vector2d(
                centerPx.x + off.x,
                centerPx.y - off.y
            );
        }

        // Measures screen-pixel error between where the locked geo should be and where it is after zoom.
        Vector2 CursorLockErrorScreenPx(double latLocked, double lonLocked, TileMath.Vector2d centerPxNew, int zNew, Vector2 localCanvas)
        {
            // Desired pixel under cursor at new zoom
            var desiredPx = TileMath.LatLonToPixel(latLocked, lonLocked, zNew);

            // Actual pixel under cursor produced by current center
            var actualPx = CursorPixelFromCenterPx(centerPxNew, zNew, localCanvas);

            // Convert world-pixel delta -> screen px
            double uiToWorld = UiToWorldScale(); // world per screen px
            double dxScreen = (desiredPx.x - actualPx.x) / uiToWorld;
            double dyScreen = (desiredPx.y - actualPx.y) / uiToWorld;

            return new Vector2((float)dxScreen, (float)dyScreen);
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
            int n = 1 << z;
            x = Mod(x, n);
            y = Mod(y, n);

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

        static int Mod(int a, int n)
        {
            int r = a % n;
            return r < 0 ? r + n : r;
        }

        // a,b must already be canonical [0..n-1]
        static int ShortestDelta(int a, int b, int n)
        {
            int d = a - b;
            if (d > n / 2) d -= n;
            if (d < -n / 2) d += n;
            return d;
        }





    }



}
