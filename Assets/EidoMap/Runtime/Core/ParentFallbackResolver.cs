// Assets/EidoMap/Runtime/Core/ParentFallbackResolver.cs
using UnityEngine;

namespace EidoMap.Core
{
    public static class ParentFallbackResolver
    {
        public struct Result
        {
            public TileKey parentKey; // z is the parent zoom
            public Rect uv;           // RawImage uvRect to crop the parent tile
        }

        /// <summary>
        /// Given a child tile (z/x/y), finds the parent tile key at depth d and the UV rect
        /// that corresponds to the child's quadrant within that parent.
        /// Returns false if the depth would go below minZoom or params are invalid.
        ///
        /// Note: This does not check cache/network. It's just math.
        /// </summary>
        public static bool TryResolve(TileKey child, int depth, int minZoom, out Result result)
        {
            result = default;

            if (depth <= 0) return false;

            int pz = child.z - depth;
            if (pz < minZoom) return false;

            int denom = 1 << depth;

            // Parent coords (bitshift)
            int px = child.x >> depth;
            int py = child.y >> depth;

            // Child quadrant inside the parent (bitmask)
            int cx = child.x & (denom - 1);
            int cy = child.y & (denom - 1);

            float subW = 1f / denom;
            float subH = 1f / denom;

            // RawImage UV origin is bottom-left.
            // Tile y increases downward, so invert y to pick the correct quadrant.
            float u = cx * subW;
            float v = 1f - (cy + 1) * subH;

            result = new Result
            {
                parentKey = new TileKey(pz, px, py),
                uv = new Rect(u, v, subW, subH)
            };
            return true;
        }
    }
}
