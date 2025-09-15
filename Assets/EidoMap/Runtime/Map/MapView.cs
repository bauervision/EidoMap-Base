// Assets/EidoMap/Runtime/Maps/MapView.cs
using System.Collections;
using System.Collections.Generic;
using UnityEngine;
using UnityEngine.EventSystems;
using UnityEngine.Networking;
using UnityEngine.UI;

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
        public bool useMapbox = true;
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

        /* ---------------- Internals ---------------- */
        const int WORLD_TILE_PX = 256;          // Slippy math uses 256px “world” tiles

        private readonly Dictionary<(int, int), RawImage> _tiles = new();
        private TileMath.Vector2d _centerPx;
        private Vector2 _dragStart;
        private bool _aoiActive;
        private Vector2 _aoiStartLocal;
        private AoiBounds _lastAoi;

        // Loader queue (main-thread only via coroutines)
        private readonly Queue<TileJob> _loadQueue = new();
        private readonly HashSet<string> _loading = new();
        private Coroutine _pumpCo;
        private int _activeLoads;
        private int _epoch;                  // bump to cancel stale loads after zoom
        private bool _interacting;
        private float _lastInteractTime;

        // Cross-zoom LRU cache
        private readonly Dictionary<string, Texture2D> _cache = new(); // key: "z/x/y"
        private readonly LinkedList<string> _lru = new();              // most-recent at front

        // Deferred trim
        private HashSet<string> _lastNeededForTrim;
        private Coroutine _deferredTrimCo;

        private struct TileJob { public int x, y, z, epoch; public RawImage img; }

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
            _centerPx = TileMath.LatLonToPixel(centerLat, centerLon, zoom);
            int n = 1 << zoom;

            var (cTileX, cTileY) = TileMath.PixelToTile(_centerPx.x, _centerPx.y);
            var needed = new HashSet<string>();

            int ring = prefetchRing ? 1 : 0;
            for (int dx = -halfTiles - ring; dx <= halfTiles + ring; dx++)
                for (int dy = -halfTiles - ring; dy <= halfTiles + ring; dy++)
                {
                    int tx = Mod(cTileX + dx, n);
                    int ty = Mod(cTileY + dy, n);
                    string kstr = Key(tx, ty, zoom);
                    needed.Add(kstr);

                    if (!_tiles.TryGetValue((tx, ty), out var img) || img == null)
                    {
                        var go = new GameObject($"t_{tx}_{ty}", typeof(RectTransform), typeof(RawImage));
                        var rt = go.GetComponent<RectTransform>();
                        rt.SetParent(tilesParent, false);
                        rt.sizeDelta = new Vector2(displayTilePixels, displayTilePixels);

                        img = go.GetComponent<RawImage>();
                        img.texture = img.texture != null ? img.texture : Texture2D.blackTexture;
                        img.raycastTarget = false; // reduce UI raycast cost
                        _tiles[(tx, ty)] = img;
                    }
                    else
                    {
                        img.rectTransform.sizeDelta = new Vector2(displayTilePixels, displayTilePixels);
                    }

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

                        EnqueueTile(tx, ty, zoom, img);
                    }
                }

            _lastNeededForTrim = needed;
            if (deferredTrim)
            {
                if (_deferredTrimCo != null) StopCoroutine(_deferredTrimCo);
                _deferredTrimCo = StartCoroutine(DeferredTrimAfterSettled());
            }
            else
            {
                TrimTiles(needed);
            }
        }

        void TrimTiles(HashSet<string> needed)
        {
            var toRemove = new List<(int, int)>();
            foreach (var kv in _tiles)
                if (!needed.Contains(Key(kv.Key.Item1, kv.Key.Item2, zoom)))
                    toRemove.Add(kv.Key);

            foreach (var k in toRemove)
            {
                if (_tiles.TryGetValue(k, out var img) && img) Destroy(img.gameObject);
                _tiles.Remove(k);
            }
        }

        IEnumerator DeferredTrimAfterSettled()
        {
            yield return new WaitForSeconds(trimDelaySeconds);
            while (_activeLoads > 0) yield return null; // avoid holes during active loads
            if (_lastNeededForTrim != null) TrimTiles(_lastNeededForTrim);
            _deferredTrimCo = null;
        }

        void PositionTile(RectTransform rt, int tx, int ty)
        {
            Vector2 centerInTiles = new((float)(_centerPx.x / WORLD_TILE_PX),
                                        (float)(_centerPx.y / WORLD_TILE_PX));

            float ox = (tx - centerInTiles.x) * displayTilePixels;
            float oy = (ty - centerInTiles.y) * displayTilePixels;

            // Invert Y for UI space (up is +Y, but tiles count +Y downward)
            Vector2 pos = new Vector2(ox, -oy);
            if (pixelSnap) pos = new Vector2(Mathf.Round(pos.x), Mathf.Round(pos.y));
            rt.anchoredPosition = pos;
        }

        /* ---------------- Loader (queue + coroutines) ---------------- */

        void EnqueueTile(int tx, int ty, int z, RawImage img)
        {
            var k = Key(tx, ty, z);
            if (_loading.Contains(k)) return; // already in-flight
            _loadQueue.Enqueue(new TileJob { x = tx, y = ty, z = z, img = img, epoch = _epoch });
            if (_pumpCo == null) _pumpCo = StartCoroutine(LoaderPump());
        }

        IEnumerator LoaderPump()
        {
            while (_loadQueue.Count > 0 || _activeLoads > 0)
            {
                while (_activeLoads < maxConcurrent && _loadQueue.Count > 0)
                {
                    var job = _loadQueue.Dequeue();
                    var key = Key(job.x, job.y, job.z);
                    if (_loading.Contains(key)) continue;

                    _loading.Add(key);
                    _activeLoads++;
                    StartCoroutine(LoadTileCo(job, key));
                }
                yield return null;
            }
            _pumpCo = null;
        }

        IEnumerator LoadTileCo(TileJob job, string key)
        {
            string url = useMapbox
                ? BuildMapboxUrl(job.x, job.y, job.z)
                : imageryUrlTemplate.Replace("{z}", job.z.ToString())
                                    .Replace("{x}", job.x.ToString())
                                    .Replace("{y}", job.y.ToString());

            using var req = UnityWebRequestTexture.GetTexture(url, true); // nonReadable=true
#if UNITY_WEBGL
            req.SetRequestHeader("Cache-Control", "max-age=3600");
#endif
            yield return req.SendWebRequest();

            if (req.result == UnityWebRequest.Result.Success)
            {
                if (job.epoch == _epoch && job.img) // discard stale zoom loads
                {
                    var tex = DownloadHandlerTexture.GetContent(req);
                    tex.wrapMode = TextureWrapMode.Clamp;
                    tex.filterMode = FilterMode.Bilinear;
                    job.img.uvRect = new Rect(0, 0, 1, 1);   // reset if parent UV was used
                    job.img.texture = tex;
                    PutInCache(job.x, job.y, job.z, tex);
                }
            }
            else
            {
                Debug.LogWarning($"Tile load failed {url}: {req.error}");
            }

            _loading.Remove(key);
            _activeLoads--;
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
                RectTransformUtility.ScreenPointToLocalPointInRectangle(mapRoot, e.position, e.pressEventCamera, out _aoiStartLocal);
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
                RectTransformUtility.ScreenPointToLocalPointInRectangle(mapRoot, e.position, e.pressEventCamera, out var now);
                Vector2 min = Vector2.Min(_aoiStartLocal, now);
                Vector2 max = Vector2.Max(_aoiStartLocal, now);
                aoiRect.anchoredPosition = min;
                aoiRect.sizeDelta = max - min;
                return;
            }

            // Pan map: UI +Y up, tile-space +Y down → flip Y once here
            var delta = (Vector2)e.position - _dragStart;
            _dragStart = e.position;

            _centerPx = new TileMath.Vector2d(_centerPx.x - delta.x, _centerPx.y + delta.y);

            var (lat, lon) = TileMath.PixelToLatLon(_centerPx.x, _centerPx.y, zoom);
            centerLat = lat; centerLon = lon;

            // Reposition currently-present tiles (cheap)
            foreach (var kv in _tiles)
            {
                var img = kv.Value;
                var parts = img.name.Split('_'); // t_x_y
                int tx = int.Parse(parts[1]);
                int ty = int.Parse(parts[2]);
                PositionTile(img.rectTransform, tx, ty);
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

                // Convert to pixel coords relative to center
                double pxTL = _centerPx.x + tlLocal.x;
                double pyTL = _centerPx.y - tlLocal.y;
                double pxBR = _centerPx.x + brLocal.x;
                double pyBR = _centerPx.y - brLocal.y;

                var (lat1, lon1) = TileMath.PixelToLatLon(pxTL, pyTL, zoom);
                var (lat2, lon2) = TileMath.PixelToLatLon(pxBR, pyBR, zoom);

                _lastAoi = new AoiBounds
                {
                    minLat = Mathf.Min((float)lat1, (float)lat2),
                    maxLat = Mathf.Max((float)lat1, (float)lat2),
                    minLon = Mathf.Min((float)lon1, (float)lon2),
                    maxLon = Mathf.Max((float)lon1, (float)lon2)
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
            ZoomBy(delta, e.position); // cursor-centric
        }

        void ZoomBy(int delta, Vector2? screenPos)
        {
            MarkInteracting();

            int oldZ = zoom;
            int newZ = Mathf.Clamp(zoom + delta, minZoom, maxZoom);
            if (newZ == oldZ) return;

            if (zoomTowardCursor && screenPos.HasValue)
            {
                RectTransformUtility.ScreenPointToLocalPointInRectangle(mapRoot, screenPos.Value, null, out var local);
                double pxOld = _centerPx.x + local.x;
                double pyOld = _centerPx.y - local.y;

                var (lat, lon) = TileMath.PixelToLatLon(pxOld, pyOld, oldZ);
                var pNew = TileMath.LatLonToPixel(lat, lon, newZ);

                // New center so that pNew remains under the cursor local point
                _centerPx = new TileMath.Vector2d(pNew.x - local.x, pNew.y + local.y);
            }
            else
            {
                // Keep current geo center
                var pNewCenter = TileMath.LatLonToPixel(centerLat, centerLon, newZ);
                _centerPx = pNewCenter;
            }

            zoom = newZ;

            // Keep Inspector in sync
            var (latC, lonC) = TileMath.PixelToLatLon(_centerPx.x, _centerPx.y, zoom);
            centerLat = latC; centerLon = lonC;

            // Invalidate in-flight loads from previous zoom
            _epoch++;

            // Keep old tiles (visual fallback), request new ones
            RebuildTiles();
        }

        /* ---------------- Cache & helpers ---------------- */

        string BuildMapboxUrl(int x, int y, int z)
        {
            int serverTileSize =
                (speedWhileInteracting && _interacting) ? 256 :
                (displayTilePixels >= 512 ? 512 : 256);

            return $"https://api.mapbox.com/styles/v1/{mapboxStyleId}/tiles/{serverTileSize}/{z}/{x}/{y}?access_token={mapboxAccessToken}";
        }

        string Key(int x, int y, int z) => $"{z}/{x}/{y}";

        static int Mod(int x, int m) { int r = x % m; return r < 0 ? r + m : r; }

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

        // LRU cache
        string CacheKey(int x, int y, int z) => $"{z}/{x}/{y}";

        bool TryGetFromCache(int x, int y, int z, out Texture2D tex)
        {
            string k = CacheKey(x, y, z);
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
            string k = CacheKey(x, y, z);
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
                string tail = _lru.Last.Value;
                _lru.RemoveLast();
                _cache.Remove(tail);
                // Don’t Destroy() texture here—RawImages may still reference it
            }
        }

        // Parent fallback: show lower-zoom tile quadrant while child streams
        bool TrySetParentFallback(RawImage img, int x, int y, int z, int maxDepth = 2)
        {
            for (int d = 1; d <= maxDepth; d++)
            {
                int pz = z - d;
                if (pz < minZoom) break;

                int denom = 1 << d;
                int px = x >> d;
                int py = y >> d;

                if (TryGetFromCache(px, py, pz, out var parent))
                {
                    int cx = x & (denom - 1);
                    int cy = y & (denom - 1);

                    float subW = 1f / denom;
                    float subH = 1f / denom;
                    float u = cx * subW;
                    // RawImage UV origin bottom-left; tiles +y downward → invert Y
                    float v = 1f - (cy + 1) * subH;

                    img.texture = parent;
                    img.uvRect = new Rect(u, v, subW, subH);
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
    }
}
