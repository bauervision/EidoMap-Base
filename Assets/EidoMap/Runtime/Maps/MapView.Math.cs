// Assets/EidoMap/Runtime/Maps/MapView.Math.cs
using UnityEngine;

namespace EidoMap
{
    public partial class MapView
    {
        // Convert screen position to tilesParent local point (in canvas units).
        // Uses the correct camera depending on canvas render mode.
        private bool ScreenToTilesLocal(Vector2 screenPos, out Vector2 local)
        {
            local = default;
            if (!tilesParent) return false;

            Camera cam = null;
            if (_rootCanvas != null && _rootCanvas.renderMode != RenderMode.ScreenSpaceOverlay)
                cam = _uiCam;

            return RectTransformUtility.ScreenPointToLocalPointInRectangle(
                tilesParent,
                screenPos,
                cam,
                out local
            );
        }

        // WORLD px per SCREEN px (TileMath pixel basis / display pixels / scale factor).
        // WORLD_TILE_PX must match TileMath’s internal pixel space (we found 512).
        private double UiToWorldScale()
        {
            double sf = (_rootCanvas != null) ? _rootCanvas.scaleFactor : 1.0;
            if (sf <= 0.0001) sf = 1.0;

            return WORLD_TILE_PX / (displayTilePixels * sf);
        }


    }
}
