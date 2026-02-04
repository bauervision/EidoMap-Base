// Assets/EidoMap/Runtime/Maps/MapView.TerrainRgbTiles.cs
using System;
using System.Collections;
using System.Collections.Generic;
using System.Globalization;
using UnityEngine;
using UnityEngine.Networking;

namespace EidoMap
{
    public partial class MapView
    {
        [Header("Terrain Height (Terrain-RGB Tiles)")]
        [SerializeField] private bool applyHeightAfterSatellite = true;

        // Good starting point. Terrain-RGB has real detail up to ~z15; higher zooms won’t add detail. :contentReference[oaicite:4]{index=4}
        [SerializeField] private int terrainRgbZoom = 14;

        // Request 512px tiles to reduce tile count.
        [SerializeField] private bool terrainRgbUse2xTiles = true;

        // Must be 2^n + 1
        [SerializeField] private int terrainHeightmapResolution = 513;

        [SerializeField] private float heightRangePaddingMeters = 25f;

        // Orientation knobs (change one at a time if mirrored)
        [SerializeField] private bool flipHeightX = false;
        [SerializeField] private bool flipHeightZ = true;

        [SerializeField] private Terrain heightTargetTerrain;

        [Header("Runtime Safety")]
        [SerializeField] private bool cloneTerrainDataAtRuntime = true;

        private TerrainData _originalTerrainData;
        private TerrainData _runtimeTerrainData;


        private void CaptureAoiTerrainHeight(AoiBounds b)
        {
            if (!applyHeightAfterSatellite) return;

            if (!useMapbox)
            {
                Debug.LogWarning("[EidoMap] Height capture requires useMapbox=true.");
                return;
            }

            if (!heightTargetTerrain)
            {
                Debug.LogWarning("[EidoMap] Height capture enabled but no heightTargetTerrain assigned.");
                return;
            }

            StartCoroutine(DownloadTerrainRgbMosaic(b, terrainRgbZoom, terrainRgbUse2xTiles, mosaic =>
            {
                if (!mosaic)
                {
                    Debug.LogWarning("[EidoMap] Terrain-RGB mosaic download returned null.");
                    return;
                }

                ApplyTerrainHeightsFromTerrainRgb(heightTargetTerrain, mosaic, b);
            }));
        }

        private IEnumerator DownloadTerrainRgbMosaic(
            AoiBounds b,
            int z,
            bool use2x,
            Action<Texture2D> onDone)
        {
            int tilePx = use2x ? 512 : 256;

            int xMin = LonToTileX(b.minLon, z);
            int xMax = LonToTileX(b.maxLon, z);
            int yMin = LatToTileY(b.maxLat, z); // north
            int yMax = LatToTileY(b.minLat, z); // south

            // Ensure ordering
            if (xMax < xMin) { int t = xMin; xMin = xMax; xMax = t; }
            if (yMax < yMin) { int t = yMin; yMin = yMax; yMax = t; }

            int tilesW = (xMax - xMin + 1);
            int tilesH = (yMax - yMin + 1);

            int outW = tilesW * tilePx;
            int outH = tilesH * tilePx;

            // We'll stitch into a big texture (RGBA32 is fine).
            var mosaic = new Texture2D(outW, outH, TextureFormat.RGBA32, false, true);
            mosaic.wrapMode = TextureWrapMode.Clamp;
            mosaic.filterMode = FilterMode.Point;

            // Download tiles sequentially first (safe). We can optimize later.
            for (int ty = yMin; ty <= yMax; ty++)
            {
                for (int tx = xMin; tx <= xMax; tx++)
                {
                    string url = BuildTerrainRgbTileUrl(z, tx, ty, use2x);
                    if (debugStaticUrl) Debug.Log($"[EidoMap] Terrain-RGB tile URL: {url}");

                    using (var req = UnityWebRequestTexture.GetTexture(url))
                    {
                        yield return req.SendWebRequest();

                        if (req.result != UnityWebRequest.Result.Success)
                        {
                            Debug.LogWarning($"[EidoMap] Terrain-RGB tile failed z{z}/{tx}/{ty}: {req.error}");
                            onDone?.Invoke(null);
                            yield break;
                        }

                        var tileTex = DownloadHandlerTexture.GetContent(req);
                        if (!tileTex)
                        {
                            Debug.LogWarning($"[EidoMap] Terrain-RGB tile null z{z}/{tx}/{ty}");
                            onDone?.Invoke(null);
                            yield break;
                        }

                        // Copy pixels into mosaic. Unity's textures are bottom-left origin.
                        // We’ll place north at top in mosaic coordinates.
                        int px = (tx - xMin) * tilePx;
                        int pyFromTop = (ty - yMin) * tilePx;
                        int py = outH - tilePx - pyFromTop;

                        var pixels = tileTex.GetPixels32();
                        mosaic.SetPixels32(px, py, tilePx, tilePx, pixels);
                    }
                }
            }

            mosaic.Apply(false, false);
            onDone?.Invoke(mosaic);
        }

        private string BuildTerrainRgbTileUrl(int z, int x, int y, bool use2x)
        {
            // Raster Tiles API for Terrain-RGB. :contentReference[oaicite:5]{index=5}
            string scale = use2x ? "@2x" : "";
            // pngraw is the common format used for terrain-rgb encoded tiles
            return $"https://api.mapbox.com/v4/mapbox.terrain-rgb/{z}/{x}/{y}{scale}.pngraw?access_token={mapboxAccessToken}";
        }

        private static int LonToTileX(double lon, int z)
        {
            double n = Math.Pow(2.0, z);
            return (int)Math.Floor((lon + 180.0) / 360.0 * n);
        }

        private static int LatToTileY(double lat, int z)
        {
            double latRad = lat * Math.PI / 180.0;
            double n = Math.Pow(2.0, z);
            double y = (1.0 - Math.Log(Math.Tan(latRad) + 1.0 / Math.Cos(latRad)) / Math.PI) / 2.0 * n;
            return (int)Math.Floor(y);
        }

        // --- Existing decode + apply pipeline (same as before), included here so this compiles standalone. ---

        private static float DecodeTerrainRgbMeters(Color32 c)
        {
            return (c.r * 256f * 256f + c.g * 256f + c.b) * 0.1f - 10000f;
        }

        private static int ClampPow2Plus1(int v)
        {
            v = Mathf.Max(v, 33);
            int pow = 1;
            while (pow + 1 < v) pow <<= 1;
            return pow + 1;
        }

        private static void MetersPerDegree(double latDeg, out double mPerDegLat, out double mPerDegLon)
        {
            double latRad = latDeg * Math.PI / 180.0;

            double cos1 = Math.Cos(latRad);
            double cos2 = Math.Cos(2.0 * latRad);
            double cos3 = Math.Cos(3.0 * latRad);
            double cos4 = Math.Cos(4.0 * latRad);
            double cos5 = Math.Cos(5.0 * latRad);
            double cos6 = Math.Cos(6.0 * latRad);

            mPerDegLat = 111132.92 - 559.82 * cos2 + 1.175 * cos4 - 0.0023 * cos6;
            mPerDegLon = 111412.84 * cos1 - 93.5 * cos3 + 0.118 * cos5;
        }

        private static void ComputeAoiMeters(AoiBounds b, out float widthMeters, out float heightMeters)
        {
            double midLat = (b.minLat + b.maxLat) * 0.5;
            MetersPerDegree(midLat, out double mPerDegLat, out double mPerDegLon);

            double dLon = (b.maxLon - b.minLon);
            double dLat = (b.maxLat - b.minLat);

            widthMeters = (float)(Math.Abs(dLon) * mPerDegLon);
            heightMeters = (float)(Math.Abs(dLat) * mPerDegLat);
        }

        private void EnsureTerrainSizedToAoiMeters(Terrain t, float aoiWidthMeters, float aoiHeightMeters, float terrainY)
        {
            if (!t || !t.terrainData) return;

            var td = t.terrainData;
            td.size = new Vector3(aoiWidthMeters, terrainY, aoiHeightMeters);

            int targetRes = ClampPow2Plus1(terrainHeightmapResolution);
            if (td.heightmapResolution != targetRes)
                td.heightmapResolution = targetRes;
        }

        private void EnsureRuntimeTerrainData(Terrain t)
        {
            if (!cloneTerrainDataAtRuntime) return;
            if (!t) return;

            if (_runtimeTerrainData) return;

            _originalTerrainData = t.terrainData;
            if (!_originalTerrainData)
            {
                Debug.LogWarning("[EidoMap] Terrain has no TerrainData to clone.");
                return;
            }

            _runtimeTerrainData = Instantiate(_originalTerrainData);
            _runtimeTerrainData.name = _originalTerrainData.name + " (Runtime)";
            t.terrainData = _runtimeTerrainData;
        }


        private void ApplyTerrainHeightsFromTerrainRgb(Terrain t, Texture2D terrainRgb, AoiBounds b)
        {
            if (!t || !t.terrainData || !terrainRgb) return;

            EnsureRuntimeTerrainData(t);
            terrainRgb.wrapMode = TextureWrapMode.Clamp;
            terrainRgb.filterMode = FilterMode.Bilinear;

            ComputeAoiMeters(b, out float aoiWidthMeters, out float aoiHeightMeters);

            int hmRes = ClampPow2Plus1(terrainHeightmapResolution);

            float minM = float.PositiveInfinity;
            float maxM = float.NegativeInfinity;

            for (int z = 0; z < hmRes; z++)
            {
                float vz = (hmRes <= 1) ? 0f : (z / (float)(hmRes - 1));
                if (flipHeightZ) vz = 1f - vz;

                for (int x = 0; x < hmRes; x++)
                {
                    float vx = (hmRes <= 1) ? 0f : (x / (float)(hmRes - 1));
                    if (flipHeightX) vx = 1f - vx;

                    Color c = terrainRgb.GetPixelBilinear(vx, vz);
                    float m = DecodeTerrainRgbMeters((Color32)c);

                    if (m < minM) minM = m;
                    if (m > maxM) maxM = m;
                }
            }

            if (!float.IsFinite(minM) || !float.IsFinite(maxM) || maxM <= minM)
            {
                Debug.LogWarning("[EidoMap] Terrain-RGB decode produced invalid min/max. Skipping SetHeights.");
                return;
            }

            float range = (maxM - minM) + Mathf.Max(0f, heightRangePaddingMeters);

            EnsureTerrainSizedToAoiMeters(t, aoiWidthMeters, aoiHeightMeters, range);

            float[,] heights = new float[hmRes, hmRes];

            for (int z = 0; z < hmRes; z++)
            {
                float vz = (hmRes <= 1) ? 0f : (z / (float)(hmRes - 1));
                if (flipHeightZ) vz = 1f - vz;

                for (int x = 0; x < hmRes; x++)
                {
                    float vx = (hmRes <= 1) ? 0f : (x / (float)(hmRes - 1));
                    if (flipHeightX) vx = 1f - vx;

                    Color c = terrainRgb.GetPixelBilinear(vx, vz);
                    float m = DecodeTerrainRgbMeters((Color32)c);

                    heights[z, x] = Mathf.Clamp01((m - minM) / range);
                }
            }

            t.terrainData.SetHeights(0, 0, heights);

            Debug.Log($"[EidoMap] Height OK. AOI meters: {aoiWidthMeters:0.0} x {aoiHeightMeters:0.0}, min/max: {minM:0.0}..{maxM:0.0}, hmRes: {hmRes}");
        }

        private void OnDisable()
        {
#if UNITY_EDITOR
            if (_originalTerrainData && heightTargetTerrain)
                heightTargetTerrain.terrainData = _originalTerrainData;

            _runtimeTerrainData = null;
            _originalTerrainData = null;
#endif
        }

    }
}
