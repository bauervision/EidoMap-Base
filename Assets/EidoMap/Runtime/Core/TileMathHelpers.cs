// Assets/EidoMap/Runtime/Core/TileMathHelpers.cs
namespace EidoMap.Core
{
    public static class TileMathHelpers
    {
        public static int Mod(int x, int m)
        {
            int r = x % m;
            return r < 0 ? r + m : r;
        }
    }
}
