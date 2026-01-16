// Assets/EidoMap/Runtime/Core/TileKey.cs
using System;

namespace EidoMap.Core
{
    /// <summary>
    /// Canonical tile identity for slippy maps.
    /// </summary>
    public readonly struct TileKey : IEquatable<TileKey>
    {
        public readonly int z;
        public readonly int x;
        public readonly int y;

        public TileKey(int z, int x, int y)
        {
            this.z = z;
            this.x = x;
            this.y = y;
        }

        public override string ToString() => $"{z}/{x}/{y}";

        public bool Equals(TileKey other) => z == other.z && x == other.x && y == other.y;
        public override bool Equals(object obj) => obj is TileKey other && Equals(other);

        public override int GetHashCode()
        {
            unchecked
            {
                int h = 17;
                h = (h * 31) + z;
                h = (h * 31) + x;
                h = (h * 31) + y;
                return h;
            }
        }

        public static bool operator ==(TileKey a, TileKey b) => a.Equals(b);
        public static bool operator !=(TileKey a, TileKey b) => !a.Equals(b);
    }
}
