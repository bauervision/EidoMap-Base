// Assets/EidoMap/Runtime/Debug/MapDebugOverlay.cs
using UnityEngine;
using UnityEngine.UI;

namespace EidoMap.Diagnostics
{
    /// <summary>
    /// Lightweight crosshair overlay manager. Purely UI; no map math.
    /// Ensures all Image raycasts are off so it never blocks scroll/drag.
    /// </summary>
    public sealed class MapDebugOverlay
    {
        private readonly RectTransform _tilesParent;
        private readonly RectTransform _mapRoot;
        private readonly float _crosshairSize;

        private RectTransform _preCH;
        private RectTransform _postCH;
        private RectTransform _mouseCH;

        public MapDebugOverlay(RectTransform tilesParent, RectTransform mapRoot, float crosshairSize)
        {
            _tilesParent = tilesParent;
            _mapRoot = mapRoot;
            _crosshairSize = crosshairSize;
        }

        public void Ensure(Color preColor, Color postColor, bool enableMouse, Color mouseColor)
        {
            if (_tilesParent == null) return;

            if (_preCH == null) _preCH = MakeCrosshairUnder(_tilesParent, preColor, "Cross_PRE", _crosshairSize);
            if (_postCH == null) _postCH = MakeCrosshairUnder(_tilesParent, postColor, "Cross_POST", _crosshairSize);

            _preCH.gameObject.SetActive(false);
            _postCH.gameObject.SetActive(false);

            if (enableMouse && _mouseCH == null && _mapRoot != null)
                _mouseCH = MakeCrosshairUnder(_mapRoot, mouseColor, "Cross_MOUSE", _crosshairSize);

            if (_mouseCH) _mouseCH.gameObject.SetActive(false);
        }

        public void HideAll()
        {
            if (_preCH) _preCH.gameObject.SetActive(false);
            if (_postCH) _postCH.gameObject.SetActive(false);
            if (_mouseCH) _mouseCH.gameObject.SetActive(false);
        }

        public void SetPre(Vector2 anchoredPos)
        {
            if (!_preCH) return;
            _preCH.anchoredPosition = anchoredPos;
            _preCH.gameObject.SetActive(true);
        }

        public void SetPost(Vector2 anchoredPos)
        {
            if (!_postCH) return;
            _postCH.anchoredPosition = anchoredPos;
            _postCH.gameObject.SetActive(true);
        }

        public void SetMouse(Vector2 anchoredPos)
        {
            if (!_mouseCH) return;
            _mouseCH.anchoredPosition = anchoredPos;
            _mouseCH.gameObject.SetActive(true);
        }

        public void BringToFront()
        {
            if (_preCH) _preCH.SetAsLastSibling();
            if (_postCH) _postCH.SetAsLastSibling();
            if (_mouseCH) _mouseCH.SetAsLastSibling();
        }

        private static RectTransform MakeCrosshairUnder(RectTransform parent, Color col, string name, float crosshairSize)
        {
            var go = new GameObject(name, typeof(RectTransform));
            var rt = go.GetComponent<RectTransform>();
            rt.SetParent(parent, false);
            rt.anchorMin = rt.anchorMax = rt.pivot = new Vector2(0.5f, 0.5f);
            rt.anchoredPosition = Vector2.zero;
            rt.sizeDelta = Vector2.zero;

            RectTransform H(string n)
            {
                var h = new GameObject(n, typeof(RectTransform), typeof(Image));
                var r = h.GetComponent<RectTransform>();
                r.SetParent(rt, false);
                r.anchorMin = r.anchorMax = r.pivot = new Vector2(0.5f, 0.5f);
                r.sizeDelta = new Vector2(crosshairSize, 2f);
                var img = h.GetComponent<Image>();
                img.color = col;
                img.raycastTarget = false;
                return r;
            }

            RectTransform V(string n)
            {
                var v = new GameObject(n, typeof(RectTransform), typeof(Image));
                var r = v.GetComponent<RectTransform>();
                r.SetParent(rt, false);
                r.anchorMin = r.anchorMax = r.pivot = new Vector2(0.5f, 0.5f);
                r.sizeDelta = new Vector2(2f, crosshairSize);
                var img = v.GetComponent<Image>();
                img.color = col;
                img.raycastTarget = false;
                return r;
            }

            H("H");
            V("V");
            return rt;
        }
    }
}
