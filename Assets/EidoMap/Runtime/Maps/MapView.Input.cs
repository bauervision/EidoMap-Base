// Assets/EidoMap/Runtime/Maps/MapView.Input.cs
using UnityEngine;
using UnityEngine.EventSystems;
using UnityEngine.UI;
using EidoMap.Core;

namespace EidoMap
{
    public partial class MapView :
        IBeginDragHandler, IDragHandler, IEndDragHandler, IScrollHandler
    {

        /* ---------------- Input: AOI / Pan / Zoom ---------------- */

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

        private void MarkInteracting()
        {
            _interacting = true;
            _lastInteractTime = Time.time;
        }

        private void MaybeEndInteracting()
        {
            if (_interacting && Time.time - _lastInteractTime > interactHoldSeconds)
                _interacting = false;
        }

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
            centerLat = lat;
            centerLon = lon;

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

                _lastAoi = new AoiBounds
                {
                    minLat = aoi.minLat,
                    maxLat = aoi.maxLat,
                    minLon = aoi.minLon,
                    maxLon = aoi.maxLon
                };

                Debug.Log($"AOI: lat[{_lastAoi.minLat:F6},{_lastAoi.maxLat:F6}] lon[{_lastAoi.minLon:F6},{_lastAoi.maxLon:F6}]");

                rect.gameObject.SetActive(false);
            }

            // Snap-refresh grid around new center
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
                var cursorPxOld = CursorPixelFromCenterPx(_centerPx, local);
                var (latOld, lonOld) = TileMath.PixelToLatLon(cursorPxOld.x, cursorPxOld.y, zOld);
                Debug.Log($"[EidoMap:CursorGeo PRE] z={zOld} lat={latOld:0.000000} lon={lonOld:0.000000}");
                if (debugZoomLogs) Debug.Log($"[EidoMap:OnScroll:local]{local}");
            }

            // --- ZOOM ---
            ZoomBy(delta, haveLocal ? (Vector2?)local : null);

            // --- POST: geo under cursor (lat/lon) at NEW zoom ---
            int zNew = zoom;
            if (haveLocal)
            {
                var cursorPxNew = CursorPixelFromCenterPx(_centerPx, local);
                var (latNew, lonNew) = TileMath.PixelToLatLon(cursorPxNew.x, cursorPxNew.y, zNew);
                Debug.Log($"[EidoMap:CursorGeo POST] z={zNew} lat={latNew:0.000000} lon={lonNew:0.000000}");
            }

            if (debugCrosshair && _dbg != null && haveLocal)
            {
                _dbg.SetPost(local);
                _dbg.BringToFront();
            }
        }

        /* ---------------- Zoom core ---------------- */

        private void ZoomBy(int delta, Vector2? tilesLocalOverride)
        {
            MarkInteracting();

            int oldZ = zoom;
            int newZ = Mathf.Clamp(zoom + delta, minZoom, maxZoom);
            if (newZ == oldZ) return;

            Vector2 local = default;
            bool haveLocal = tilesLocalOverride.HasValue;

            if (haveLocal) local = tilesLocalOverride.Value;

            if (zoomTowardCursor && haveLocal)
            {
                // 1) Geo under cursor at OLD zoom
                var cursorPxOld = CursorPixelFromCenterPx(_centerPx, local);
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

        /* ---------------- Cursor math helpers ---------------- */

        // Returns cursor offset from center in WORLD PIXELS.
        // local is tilesParent local in CANVAS UNITS.
        private TileMath.Vector2d CursorOffsetWorldPx(Vector2 local)
        {
            double worldPerUi = (double)WORLD_TILE_PX / displayTilePixels; // no scaleFactor (local already in canvas units)
            return new TileMath.Vector2d(local.x * worldPerUi, local.y * worldPerUi);
        }

        // World pixel +Y is down; UI local +Y is up, so subtract Y offset.
        private TileMath.Vector2d CursorPixelFromCenterPx(TileMath.Vector2d centerPx, Vector2 local)
        {
            var off = CursorOffsetWorldPx(local);
            return new TileMath.Vector2d(
                centerPx.x + off.x,
                centerPx.y - off.y
            );
        }
    }
}
