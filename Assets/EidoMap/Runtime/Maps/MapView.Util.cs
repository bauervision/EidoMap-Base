// Assets/EidoMap/Runtime/Maps/MapView.Util.cs
using UnityEngine;

namespace EidoMap
{
    public partial class MapView
    {
        // TileMath is clearly operating in 512px-per-tile pixel space (based on your logs).
        // Keep this here so all math uses the same source of truth.
        private const int WORLD_TILE_PX = 512;

        private static void AlignToParentRect(RectTransform child, RectTransform parent)
        {
            if (!child || !parent) return;
            child.anchorMin = Vector2.zero;
            child.anchorMax = Vector2.one;
            child.pivot = new Vector2(0.5f, 0.5f);
            child.anchoredPosition = Vector2.zero;
            child.sizeDelta = Vector2.zero;
            child.localScale = Vector3.one;
        }

        private static string RTInfo(string label, RectTransform rt)
        {
            if (!rt) return $"{label}: <null>";
            var r = rt.rect;
            return $"{label}: pos={rt.anchoredPosition} sizeΔ={rt.sizeDelta} " +
                   $"anch=({rt.anchorMin}->{rt.anchorMax}) pivot={rt.pivot} " +
                   $"rect(w={r.width:0.##},h={r.height:0.##}) scale={rt.localScale}";
        }

        private static int Mod(int a, int n)
        {
            int r = a % n;
            return r < 0 ? r + n : r;
        }

        // Wrap any delta into [-n/2, +n/2]
        private static int WrapDelta(int d, int n)
        {
            d %= n;
            if (d > n / 2) d -= n;
            if (d < -n / 2) d += n;
            return d;
        }

        // a,b must already be canonical [0..n-1]
        private static int ShortestDelta(int a, int b, int n)
        {
            int d = a - b;
            if (d > n / 2) d -= n;
            if (d < -n / 2) d += n;
            return d;
        }



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


    }
}
