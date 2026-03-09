// Assets/EidoMap/Runtime/Maps/MapView.StaticCapture.cs
using System.Collections;
using System.Globalization;
using UnityEngine;
using UnityEngine.Networking;

namespace EidoMap
{
    public partial class MapView
    {
        private Texture2D _lastCapturedAoiTexture;

        //Called from the Capture button on the UI
        public void CaptureAoiStaticImagery()
        {
            if (!useMapbox)
            {
                Debug.LogWarning("[EidoMap] CaptureAoiStaticImagery requires useMapbox=true.");
                return;
            }

            var b = GetAoiBounds();

            string url = BuildMapboxStaticImageUrl(b, captureResolution, captureResolution, captureHiDpi);
            if (debugStaticUrl) Debug.Log($"[EidoMap] Static URL: {url}");

            StartCoroutine(DownloadTexture(url, tex =>
            {
                if (!tex)
                {
                    Debug.LogWarning("[EidoMap] Static imagery download returned null texture.");
                    return;
                }

                _lastCapturedAoiTexture = tex;

                if (runSegmentationOnCapture && segmentationRunner != null)
                {
                    segmentationRunner.RunPreview(tex);
                }

                // Apply to Terrain if assigned.
                ApplyCapturedTextureToTerrain(tex);

                // Chain: Terrain-RGB → apply height (if enabled + terrain assigned).
                CaptureAoiTerrainHeight(b);


                // Apply to Terrain if assigned.
                ApplyCapturedTextureToTerrain(tex);

                // Chain: Terrain-RGB → apply height (if enabled + terrain assigned).
                CaptureAoiTerrainHeight(b);
            }));
        }

        private string BuildMapboxStaticImageUrl(AoiBounds b, int w, int h, bool hidpi)
        {
            return BuildMapboxStaticImageUrlWithStyle(mapboxStyleId, b, w, h, hidpi);
        }

        private string BuildMapboxStaticImageUrlWithStyle(string styleId, AoiBounds b, int w, int h, bool hidpi)
        {
            // Mapbox wants [minLon,minLat,maxLon,maxLat] using invariant culture.
            string minLon = b.minLon.ToString(CultureInfo.InvariantCulture);
            string minLat = b.minLat.ToString(CultureInfo.InvariantCulture);
            string maxLon = b.maxLon.ToString(CultureInfo.InvariantCulture);
            string maxLat = b.maxLat.ToString(CultureInfo.InvariantCulture);

            string bbox = $"[{minLon},{minLat},{maxLon},{maxLat}]";
            string size = $"{w}x{h}" + (hidpi ? "@2x" : "");

            return $"https://api.mapbox.com/styles/v1/{styleId}/static/{bbox}/{size}?access_token={mapboxAccessToken}";
        }

        private IEnumerator DownloadTexture(string url, System.Action<Texture2D> onDone)
        {
            using (var req = UnityWebRequestTexture.GetTexture(url))
            {
                yield return req.SendWebRequest();

                if (req.result != UnityWebRequest.Result.Success)
                {
                    Debug.LogWarning($"[EidoMap] Static imagery download failed: {req.error}");
                    onDone?.Invoke(null);
                    yield break;
                }

                var tex = DownloadHandlerTexture.GetContent(req);
                onDone?.Invoke(tex);
            }
        }
    }
}
