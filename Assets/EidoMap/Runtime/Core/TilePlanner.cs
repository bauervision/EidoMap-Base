// Assets/EidoMap/Runtime/Core/TilePlanner.cs
using System.Collections.Generic;

namespace EidoMap.Core
{
    public static class TilePlanner
    {
        /// <summary>
        /// Computes needed tiles around a center tile (wraps X/Y by n = 2^z).
        /// halfTiles=2 => 5x5, ring adds one extra border when enabled.
        /// </summary>
        public static void ComputeNeeded(
            int z,
            int centerTileX,
            int centerTileY,
            int halfTiles,
            bool prefetchRing,
            HashSet<TileKey> outNeeded)
        {
            outNeeded.Clear();

            int n = 1 << z;
            int ring = prefetchRing ? 1 : 0;

            for (int dx = -halfTiles - ring; dx <= halfTiles + ring; dx++)
            {
                for (int dy = -halfTiles - ring; dy <= halfTiles + ring; dy++)
                {
                    int tx = TileMathHelpers.Mod(centerTileX + dx, n);
                    int ty = TileMathHelpers.Mod(centerTileY + dy, n);
                    outNeeded.Add(new TileKey(z, tx, ty));
                }
            }
        }
    }
}
