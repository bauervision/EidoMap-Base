// Assets/EidoMap/Runtime/Maps/MapView.AoiBounds.cs
using System;
using TMPro;
using UnityEngine;

namespace EidoMap
{
    public partial class MapView
    {
        public AoiBounds GetAoiBounds()
        {
            if (!mapRoot || !aoiRect)
                return default;

            // AOI rect world corners: 0=BL, 1=TL, 2=TR, 3=BR
            var wc = new Vector3[4];
            aoiRect.GetWorldCorners(wc);

            Vector2 bl = RectTransformUtility.WorldToScreenPoint(_uiCam, wc[0]);
            Vector2 tl = RectTransformUtility.WorldToScreenPoint(_uiCam, wc[1]);
            Vector2 tr = RectTransformUtility.WorldToScreenPoint(_uiCam, wc[2]);
            Vector2 br = RectTransformUtility.WorldToScreenPoint(_uiCam, wc[3]);

            Vector2 mapCenterScreen = GetMapRootScreenCenter();

            var ll_bl = ScreenToLatLon(bl, mapCenterScreen);
            var ll_tl = ScreenToLatLon(tl, mapCenterScreen);
            var ll_tr = ScreenToLatLon(tr, mapCenterScreen);
            var ll_br = ScreenToLatLon(br, mapCenterScreen);

            float minLat = Mathf.Min((float)ll_bl.lat, (float)ll_tl.lat, (float)ll_tr.lat, (float)ll_br.lat);
            float maxLat = Mathf.Max((float)ll_bl.lat, (float)ll_tl.lat, (float)ll_tr.lat, (float)ll_br.lat);
            float minLon = Mathf.Min((float)ll_bl.lon, (float)ll_tl.lon, (float)ll_tr.lon, (float)ll_br.lon);
            float maxLon = Mathf.Max((float)ll_bl.lon, (float)ll_tl.lon, (float)ll_tr.lon, (float)ll_br.lon);

            return new AoiBounds { minLat = minLat, maxLat = maxLat, minLon = minLon, maxLon = maxLon };
        }

        private Vector2 GetMapRootScreenCenter()
        {
            var wc = new Vector3[4];
            mapRoot.GetWorldCorners(wc);

            Vector2 bl = RectTransformUtility.WorldToScreenPoint(_uiCam, wc[0]);
            Vector2 tr = RectTransformUtility.WorldToScreenPoint(_uiCam, wc[2]);
            return (bl + tr) * 0.5f;
        }

        private (double lat, double lon) ScreenToLatLon(Vector2 screenPx, Vector2 mapCenterScreen)
        {
            double dxUi = screenPx.x - mapCenterScreen.x;
            double dyUi = screenPx.y - mapCenterScreen.y;

            // IMPORTANT: WORLD_TILE_PX is the ground truth world pixel size per tile (512).
            // Convert UI pixels to world pixels in the same space as _centerPx.
            double uiToWorldScale = (double)WORLD_TILE_PX / (double)displayTilePixels;

            // UI +Y is up; world/tile +Y is down -> subtract dy
            double worldX = _centerPx.x + dxUi * uiToWorldScale;
            double worldY = _centerPx.y - dyUi * uiToWorldScale;

            var ll = TileMath.PixelToLatLon(worldX, worldY, zoom);
            return (ll.lat, ll.lon);
        }

        private void UpdateAoiReadout()
        {
            if (!aoiRect || !mapRoot)
                return;

            AoiBounds b = GetAoiBounds();

            // Update foot-training UI (mask state, capture enabled, max walk time, etc.)
            UpdateTrainingUiForAoi(b);

            if (!aoiReadoutText)
                return;

            double midLat = (b.minLat + b.maxLat) * 0.5;
            double midLon = (b.minLon + b.maxLon) * 0.5;

            double widthM = HaversineMeters(midLat, b.minLon, midLat, b.maxLon);
            double heightM = HaversineMeters(b.minLat, midLon, b.maxLat, midLon);

            aoiReadoutText.text =
                $"<b>AOI</b> (z={zoom})\n" +
                $"N {b.maxLat:F6}\n" +
                $"S {b.minLat:F6}\n" +
                $"W {b.minLon:F6}\n" +
                $"E {b.maxLon:F6}\n" +
                $"Size {(widthM / 1000.0):F2} km x {(heightM / 1000.0):F2} km";
        }

        private static double HaversineMeters(double lat1, double lon1, double lat2, double lon2)
        {
            const double R = 6371000.0; // meters
            double dLat = (lat2 - lat1) * Mathf.Deg2Rad;
            double dLon = (lon2 - lon1) * Mathf.Deg2Rad;

            double a =
                Math.Sin(dLat * 0.5) * Math.Sin(dLat * 0.5) +
                Math.Cos(lat1 * Mathf.Deg2Rad) * Math.Cos(lat2 * Mathf.Deg2Rad) *
                Math.Sin(dLon * 0.5) * Math.Sin(dLon * 0.5);

            double c = 2.0 * Math.Atan2(Math.Sqrt(a), Math.Sqrt(1.0 - a));
            return R * c;
        }
    }
}
