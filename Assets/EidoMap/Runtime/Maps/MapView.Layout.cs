// Assets/EidoMap/Runtime/Maps/MapView.Layout.cs
using System.Collections;
using System.Collections.Generic;
using UnityEngine;
using UnityEngine.UI;
using EidoMap.Core;

namespace EidoMap
{
    public partial class MapView
    {


        private void PositionTile(RectTransform rt, int tx, int ty)
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
            double py = -oy; // UI Y up, tile Y down

            if (pixelSnap)
            {
                px = System.Math.Round(px);
                py = System.Math.Round(py);
            }

            rt.anchoredPosition = new Vector2((float)px, (float)py);
        }
    }
}
