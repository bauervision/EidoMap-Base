using System;
using UnityEngine;

namespace EidoMap
{
    public static class TileMath
    {
        const double MinLat = -85.05112878;
        const double MaxLat = 85.05112878;
        const double MinLon = -180;
        const double MaxLon = 180;
        const int TileSize = 256;

        public static double ClampLat(double lat) => Math.Max(MinLat, Math.Min(MaxLat, lat));
        public static double WrapLon(double lon)
        {
            lon %= 360.0;
            if (lon > 180) lon -= 360;
            if (lon < -180) lon += 360;
            return lon;
        }

        // lon/lat -> pixel coords at zoom
        public static Vector2d LatLonToPixel(double lat, double lon, int z)
        {
            lat = ClampLat(lat); lon = WrapLon(lon);
            double s = TileSize * (1 << z);
            double x = (lon + 180.0) / 360.0 * s;
            double sinLat = Math.Sin(lat * Math.PI / 180.0);
            double y = (0.5 - Math.Log((1 + sinLat) / (1 - sinLat)) / (4 * Math.PI)) * s;
            return new Vector2d(x, y);
        }

        // pixel -> lon/lat at zoom
        public static (double lat, double lon) PixelToLatLon(double px, double py, int z)
        {
            double s = TileSize * (1 << z);
            double lon = px / s * 360.0 - 180.0;
            double n = Math.PI - 2.0 * Math.PI * py / s;
            double lat = 180.0 / Math.PI * Math.Atan(0.5 * (Math.Exp(n) - Math.Exp(-n)));
            return (ClampLat(lat), WrapLon(lon));
        }

        // pixel -> tile index
        public static (int tx, int ty) PixelToTile(double px, double py) =>
            ((int)Math.Floor(px / TileSize), (int)Math.Floor(py / TileSize));

        // tile bounds in lon/lat
        public static (double minLat, double minLon, double maxLat, double maxLon) TileBounds(int tx, int ty, int z)
        {
            double s = TileSize * (1 << z);
            double xMin = tx * TileSize;
            double yMin = ty * TileSize;
            var (minLat, minLon) = PixelToLatLon(xMin, yMin + TileSize, z);
            var (maxLat, maxLon) = PixelToLatLon(xMin + TileSize, yMin, z);
            return (minLat, minLon, maxLat, maxLon);
        }

        // helper for big coords
        public readonly struct Vector2d { public readonly double x, y; public Vector2d(double x, double y) { this.x = x; this.y = y; } }
    }

}