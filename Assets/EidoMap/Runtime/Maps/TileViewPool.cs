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
                var rt0 = img.rectTransform;
                rt0.sizeDelta = new Vector2(_tilePixels, _tilePixels);
                rt0.localScale = Vector3.one;
                rt0.localRotation = Quaternion.identity;

                img.uvRect = new Rect(0, 0, 1, 1);
                img.enabled = true;
                img.color = Color.white;
                img.gameObject.SetActive(true);

                var cr0 = img.GetComponent<CanvasRenderer>();
                if (cr0) cr0.cullTransparentMesh = false;

                return img;
            }

            var go = new GameObject($"t_{x}_{y}", typeof(RectTransform), typeof(RawImage), typeof(TileViewTag));
            go.SetActive(true);

            var rt = go.GetComponent<RectTransform>();
            rt.SetParent(_tilesParent, false);

            rt.anchorMin = rt.anchorMax = new Vector2(0.5f, 0.5f);
            rt.pivot = new Vector2(0.5f, 0.5f);
            rt.localScale = Vector3.one;
            rt.localRotation = Quaternion.identity;

            rt.sizeDelta = new Vector2(_tilePixels, _tilePixels);
            rt.anchoredPosition = Vector2.zero;

            img = go.GetComponent<RawImage>();
            img.texture = Texture2D.blackTexture;
            img.uvRect = new Rect(0, 0, 1, 1);
            img.raycastTarget = false;
            img.enabled = true;
            img.color = Color.white;

            var cr = go.GetComponent<CanvasRenderer>();
            if (cr) cr.cullTransparentMesh = false;

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
