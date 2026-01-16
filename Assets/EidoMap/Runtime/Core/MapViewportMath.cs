using System;

namespace EidoMap.Core
{
    public static class MapViewportMath
    {
        /// <summary>
        /// Pan center in world px given UI delta.
        /// (You already have this; leaving here just for context.)
        /// </summary>
        public static TileMath.Vector2d PanCenterPx(TileMath.Vector2d centerPx, float deltaUiX, float deltaUiY, double uiToWorldScale)
        {
            // UI +Y up, tiles/world +Y down => add deltaUiY * scale to world Y
            return new TileMath.Vector2d(
                centerPx.x - deltaUiX * uiToWorldScale,
                centerPx.y + deltaUiY * uiToWorldScale
            );
        }

        /// <summary>
        /// Computes new centerPx (world px, 256px-per-tile space) such that the geo point under the cursor
        /// remains under the same UI-local point after a zoom change.
        ///
        /// Inputs:
        /// - centerPx: current world px center (256px-per-tile space)
        /// - oldZ/newZ: zoom levels
        /// - localUiX/localUiY: tilesParent local UI coords of the cursor (pixels, origin at tilesParent pivot)
        /// - worldTilePx: usually 256
        /// - uiToWorldScale: WORLD_TILE_PX / displayTilePixels  (maps UI px -> world px)
        /// </summary>
        public static TileMath.Vector2d ZoomCenterPxTowardCursor(
            TileMath.Vector2d centerPx,
            int oldZ,
            int newZ,
            float localUiX,
            float localUiY,
            int worldTilePx,
            double uiToWorldScale)
        {
            if (newZ == oldZ) return centerPx;

            // Center in continuous tile units at old zoom
            double cxOld = centerPx.x / worldTilePx;
            double cyOld = centerPx.y / worldTilePx;

            // Convert UI-local px to world px to tile units
            double lx = (localUiX * uiToWorldScale) / worldTilePx;
            double ly = (localUiY * uiToWorldScale) / worldTilePx;

            // Geo point under cursor in tile units (old zoom)
            // UI +Y up, tile +Y down => subtract ly from cy
            double uOld = cxOld + lx;
            double vOld = cyOld - ly;

            // Scale factor between zoom levels
            double f = Pow2(newZ - oldZ);

            // Same geo point in tile units (new zoom)
            double uNew = uOld * f;
            double vNew = vOld * f;

            // Choose new center so that the same local offset (lx,ly) hits the same geo point
            double cxNew = uNew - lx;
            double cyNew = vNew + ly; // invert back (because v = cy - ly)

            // Return in world px space
            return new TileMath.Vector2d(cxNew * worldTilePx, cyNew * worldTilePx);
        }

        private static double Pow2(int dz)
        {
            // exact-ish powers of 2; avoids Math.Pow inaccuracies for integer exponents
            if (dz == 0) return 1.0;
            if (dz > 0) return 1 << dz;
            return 1.0 / (1 << (-dz));
        }

        /// <summary>
        /// Optional: compute post-zoom local error in UI px (should be near 0,0).
        /// Useful for debugging.
        /// </summary>
        public static (double errUiX, double errUiY) CursorLockErrorUiPx(
            TileMath.Vector2d centerPxOld,
            TileMath.Vector2d centerPxNew,
            int oldZ,
            int newZ,
            float localUiX,
            float localUiY,
            int worldTilePx,
            double uiToWorldScale)
        {
            double cxOld = centerPxOld.x / worldTilePx;
            double cyOld = centerPxOld.y / worldTilePx;

            double lx = (localUiX * uiToWorldScale) / worldTilePx;
            double ly = (localUiY * uiToWorldScale) / worldTilePx;

            double uOld = cxOld + lx;
            double vOld = cyOld - ly;

            double f = Pow2(newZ - oldZ);
            double uNew = uOld * f;
            double vNew = vOld * f;

            double cxNew = centerPxNew.x / worldTilePx;
            double cyNew = centerPxNew.y / worldTilePx;

            // expected local (tile units) after zoom: lx, ly
            double postLx = uNew - cxNew;
            double postLy = cyNew - vNew;

            double errTilesX = postLx - lx;
            double errTilesY = postLy - ly;

            // convert tile-units error back to UI px error
            double errUiX = (errTilesX * worldTilePx) / uiToWorldScale;
            double errUiY = (errTilesY * worldTilePx) / uiToWorldScale;

            return (errUiX, errUiY);
        }
    }
}
