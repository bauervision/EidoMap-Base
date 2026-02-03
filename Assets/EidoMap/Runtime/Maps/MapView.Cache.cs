// Assets/EidoMap/Runtime/Maps/MapView.Cache.cs
using System.Collections.Generic;
using UnityEngine;
using UnityEngine.UI;
using EidoMap.Core;

namespace EidoMap
{
    public partial class MapView
    {
        // Cross-zoom LRU cache (most-recent at front)
        private readonly Dictionary<TileKey, Texture2D> _cache = new();
        private readonly LinkedList<TileKey> _lru = new();

        private bool TryGetFromCache(int x, int y, int z, out Texture2D tex)
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

        private void PutInCache(int x, int y, int z, Texture2D tex)
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
        private bool TrySetParentFallback(RawImage img, int x, int y, int z, int maxDepth = 2)
        {
            var child = new TileKey(z, x, y);

            for (int d = 1; d <= maxDepth; d++)
            {
                if (!ParentFallbackResolver.TryResolve(child, d, minZoom, out var res))
                    break;

                if (_cache.TryGetValue(res.parentKey, out var parentTex) && parentTex != null)
                {
                    _lru.Remove(res.parentKey);
                    _lru.AddFirst(res.parentKey);

                    img.texture = parentTex;
                    img.uvRect = res.uv;
                    return true;
                }
            }

            return false;
        }
    }
}
