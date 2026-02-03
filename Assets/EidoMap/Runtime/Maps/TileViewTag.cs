using UnityEngine;

namespace EidoMap
{
    public sealed class TileViewTag : MonoBehaviour
    {
        public int x;
        public int y;
        public int z;
        public int epoch;

        public void Set(int x, int y, int z, int epoch)
        {
            this.x = x;
            this.y = y;
            this.z = z;
            this.epoch = epoch;
        }

        public bool Matches(int x, int y, int z, int epoch)
        {
            return this.x == x && this.y == y && this.z == z && this.epoch == epoch;
        }
    }
}
