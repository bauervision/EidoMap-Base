// Assets/EidoMap/Runtime/Core/AoiMath.cs
using UnityEngine;

namespace EidoMap.Core
{
    public static class AoiMath
    {
        public struct AoiBounds
        {
            public float minLat, maxLat, minLon, maxLon;
        }

        /// <summary>
        /// Computes AOI bounds from:
        /// - current center in world px (256px per tile)
        /// - UI-local TL/BR corners in mapRoot local space
        /// - uiToWorldScale (WORLD_TILE_PX / displayTilePixels)
        /// </summary>
        public static AoiBounds ComputeBoundsFromLocalCorners(
            TileMath.Vector2d centerPx,
            int zoom,
            Vector2 tlLocal,
            Vector2 brLocal,
            double uiToWorldScale)
        {
            // Convert UI local offsets to world px relative to center.
            // UI local +X right matches world +X, but UI +Y up is world -Y (tiles count downward).
            double pxTL = centerPx.x + tlLocal.x * uiToWorldScale;
            double pyTL = centerPx.y - tlLocal.y * uiToWorldScale;

            double pxBR = centerPx.x + brLocal.x * uiToWorldScale;
            double pyBR = centerPx.y - brLocal.y * uiToWorldScale;

            var (lat1, lon1) = TileMath.PixelToLatLon(pxTL, pyTL, zoom);
            var (lat2, lon2) = TileMath.PixelToLatLon(pxBR, pyBR, zoom);

            return new AoiBounds
            {
                minLat = Mathf.Min((float)lat1, (float)lat2),
                maxLat = Mathf.Max((float)lat1, (float)lat2),
                minLon = Mathf.Min((float)lon1, (float)lon2),
                maxLon = Mathf.Max((float)lon1, (float)lon2),
            };
        }
    }
}
