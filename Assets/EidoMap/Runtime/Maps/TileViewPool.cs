// Assets/EidoMap/Runtime/Maps/TileViewPool.cs
using System.Collections.Generic;
using UnityEngine;
using UnityEngine.UI;
using EidoMap.Core;

namespace EidoMap
{
    /// <summary>
    /// TileViewPool
    /// Owns the UI objects (RawImage tiles) for the current zoom.
    /// MapView provides positioning and assigns textures / uvRect.
    /// </summary>
    public sealed class TileViewPool
    {
        private readonly RectTransform _tilesParent;
        private readonly Dictionary<(int x, int y), RawImage> _tiles = new();

        private int _tilePixels;

        public TileViewPool(RectTransform tilesParent, int tilePixels)
        {
            _tilesParent = tilesParent;
            _tilePixels = tilePixels;
        }

        public void SetTilePixels(int tilePixels)
        {
            if (tilePixels <= 0) return;
            _tilePixels = tilePixels;

            // Update existing tiles to match
            foreach (var kv in _tiles)
            {
                if (kv.Value)
                    kv.Value.rectTransform.sizeDelta = new Vector2(_tilePixels, _tilePixels);
            }
        }

        public RawImage GetOrCreate(int x, int y)
        {
            if (_tiles.TryGetValue((x, y), out var img) && img != null)
            {
                img.rectTransform.sizeDelta = new Vector2(_tilePixels, _tilePixels);
                return img;
            }

            var go = new GameObject($"t_{x}_{y}", typeof(RectTransform), typeof(RawImage));
            var rt = go.GetComponent<RectTransform>();
            rt.SetParent(_tilesParent, false);
            rt.sizeDelta = new Vector2(_tilePixels, _tilePixels);

            img = go.GetComponent<RawImage>();
            img.texture = img.texture != null ? img.texture : Texture2D.blackTexture;
            img.raycastTarget = false; // reduce UI raycast cost

            _tiles[(x, y)] = img;
            return img;
        }

        public IEnumerable<KeyValuePair<(int x, int y), RawImage>> Enumerate()
        {
            return _tiles;
        }

        public void Trim(HashSet<TileKey> needed, int zoom)
        {
            // Convert needed -> xy set for this zoom (tile views are zoom-local)
            var neededXY = new HashSet<(int x, int y)>();
            foreach (var tk in needed)
            {
                if (tk.z == zoom)
                    neededXY.Add((tk.x, tk.y));
            }

            var toRemove = new List<(int x, int y)>();
            foreach (var kv in _tiles)
            {
                if (!neededXY.Contains(kv.Key))
                    toRemove.Add(kv.Key);
            }

            foreach (var k in toRemove)
            {
                if (_tiles.TryGetValue(k, out var img) && img)
                    Object.Destroy(img.gameObject);

                _tiles.Remove(k);
            }
        }

        public void Clear()
        {
            foreach (var kv in _tiles)
            {
                if (kv.Value) Object.Destroy(kv.Value.gameObject);
            }
            _tiles.Clear();
        }


    }
}
