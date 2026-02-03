using System;

namespace EidoMap
{
    public static class TileMath
    {
        const double MinLat = -85.05112878;
        const double MaxLat = 85.05112878;

        // IMPORTANT:
        // This must match MapView.WORLD_TILE_PX (your "world pixels per tile").
        // If WORLD_TILE_PX is 512 in MapView, set this to 512 as well.
        public static int WorldTilePx = 512;

        public static double ClampLat(double lat) => Math.Max(MinLat, Math.Min(MaxLat, lat));

        public static double WrapLon(double lon)
        {
            lon %= 360.0;
            if (lon > 180) lon -= 360;
            if (lon < -180) lon += 360;
            return lon;
        }

        // lon/lat -> pixel coords at zoom (world pixel space, 0..WorldTilePx*2^z)
        public static Vector2d LatLonToPixel(double lat, double lon, int z)
        {
            lat = ClampLat(lat);
            lon = WrapLon(lon);

            double s = (double)WorldTilePx * (1 << z);

            double x = (lon + 180.0) / 360.0 * s;

            double sinLat = Math.Sin(lat * Math.PI / 180.0);
            double y = (0.5 - Math.Log((1 + sinLat) / (1 - sinLat)) / (4 * Math.PI)) * s;

            return new Vector2d(x, y);
        }

        // pixel -> lon/lat at zoom (world pixel space)
        public static (double lat, double lon) PixelToLatLon(double px, double py, int z)
        {
            double s = (double)WorldTilePx * (1 << z);

            double lon = px / s * 360.0 - 180.0;

            double n = Math.PI - 2.0 * Math.PI * py / s;
            double lat = 180.0 / Math.PI * Math.Atan(0.5 * (Math.Exp(n) - Math.Exp(-n)));

            return (ClampLat(lat), WrapLon(lon));
        }

        // pixel -> tile index in world pixel space
        public static (int tx, int ty) PixelToTile(double px, double py) =>
            ((int)Math.Floor(px / WorldTilePx), (int)Math.Floor(py / WorldTilePx));

        // tile bounds in lon/lat
        public static (double minLat, double minLon, double maxLat, double maxLon) TileBounds(int tx, int ty, int z)
        {
            double xMin = tx * (double)WorldTilePx;
            double yMin = ty * (double)WorldTilePx;

            var (minLat, minLon) = PixelToLatLon(xMin, yMin + WorldTilePx, z);
            var (maxLat, maxLon) = PixelToLatLon(xMin + WorldTilePx, yMin, z);

            return (minLat, minLon, maxLat, maxLon);
        }

        public readonly struct Vector2d
        {
            public readonly double x, y;
            public Vector2d(double x, double y) { this.x = x; this.y = y; }
        }
    }
}
