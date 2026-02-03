using System.Collections;
using System.Collections.Generic;
using UnityEngine;
using EidoMap.Core;


namespace EidoMap
{
    public partial class MapView
    {
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

    }
}
