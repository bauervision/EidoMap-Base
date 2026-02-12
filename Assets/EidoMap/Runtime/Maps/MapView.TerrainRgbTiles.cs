// Assets/EidoMap/Runtime/Maps/MapView.TerrainRgbTiles.cs
using System;
using System.Collections;
using UnityEngine;
using UnityEngine.Networking;

namespace EidoMap
{
    public partial class MapView
    {
        [Header("Terrain Height (Terrain-RGB Tiles)")]
        [SerializeField] private bool applyHeightAfterSatellite = true;

        [Tooltip("Terrain-RGB zoom level. Real detail tops out around ~15.")]
        [SerializeField] private int terrainRgbZoom = 14;

        [Tooltip("Request 512px tiles (@2x). Reduces tile count for the same coverage.")]
        [SerializeField] private bool terrainRgbUse2xTiles = true;

        [Tooltip("Must be 2^n + 1")]
        [SerializeField] private int terrainHeightmapResolution = 513;

        [SerializeField] private float heightRangePaddingMeters = 25f;

        [Header("Orientation (change one at a time if mirrored)")]
        [SerializeField] private bool flipHeightX = false;
        [SerializeField] private bool flipHeightZ = true;

        [Header("Runtime Safety")]
        [SerializeField] private bool cloneTerrainDataAtRuntime = true;

        [Header("Terrain Fresh Start (Runtime Terrain Creation)")]
        [Tooltip("If true and no targetTerrain exists, we will create a runtime terrain automatically.")]
        [SerializeField] private bool createTerrainIfMissing = true;

        [Tooltip("Parent under which runtime terrain will be created. If null, we create next to this MapView.")]
        [SerializeField] private Transform runtimeTerrainRoot;

        [Tooltip("Name for the runtime-created terrain GameObject.")]
        [SerializeField] private string runtimeTerrainName = "Terrain (Runtime)";

        [Tooltip("If true, we destroy any existing runtime terrain (same name) under runtimeTerrainRoot before creating a new one.")]
        [SerializeField] private bool destroyExistingRuntimeTerrain = true;

        [Tooltip("Initial terrain Y size in meters before we know AOI. (It will be resized after height decode.)")]
        [SerializeField] private float initialTerrainYSizeMeters = 50f;

        [Tooltip("Initial terrain X/Z size in meters before we know AOI. (It will be resized after height decode.)")]
        [SerializeField] private float initialTerrainXZSizeMeters = 200f;

        [Header("Sampling / Debug")]
        [Tooltip("Adds a 1-tile guard band around the AOI tile coverage. Prevents edge clamping artifacts (recommended).")]
        [SerializeField] private bool terrainRgbGuardBandTiles = true;

        [Tooltip("Logs how many height samples landed outside the mosaic before clamping (should be 0 with guard band).")]
        [SerializeField] private bool debugTerrainRgbClampCounts = false;

        [Tooltip("If true, sample height from raw mosaic pixels (byte-accurate) instead of Texture2D GetPixel/Bilinear.")]
        [SerializeField] private bool sampleHeightFromRawPixels = true;

        private TerrainData _originalTerrainData;
        private TerrainData _runtimeTerrainData;
        private Terrain _createdRuntimeTerrain;

        private struct TerrainRgbMosaic
        {
            public Texture2D tex;
            public Color32[] pixels;
            public int width;
            public int height;

            public int z;
            public int tilePx;
            public int xMin;
            public int yMin; // north-most tile index used for mosaic
        }

        // --------------------------------------------------------------------
        // Terrain lifecycle helpers
        // --------------------------------------------------------------------

        private Terrain GetOrCreatePipelineTerrain()
        {
            if (targetTerrain) return targetTerrain;

            if (!createTerrainIfMissing)
                return null;

            targetTerrain = CreateFreshRuntimeTerrain();
            return targetTerrain;
        }

        private Terrain CreateFreshRuntimeTerrain()
        {
            Transform root = runtimeTerrainRoot ? runtimeTerrainRoot : transform;

            if (destroyExistingRuntimeTerrain)
            {
                for (int i = root.childCount - 1; i >= 0; i--)
                {
                    Transform child = root.GetChild(i);
                    if (child && child.name == runtimeTerrainName)
                        DestroyGameObjectSafe(child.gameObject);
                }
            }

            var td = new TerrainData();
            td.name = $"{runtimeTerrainName} Data";

            int res = ClampPow2Plus1(terrainHeightmapResolution);
            td.heightmapResolution = res;

            td.size = new Vector3(
                Mathf.Max(1f, initialTerrainXZSizeMeters),
                Mathf.Max(1f, initialTerrainYSizeMeters),
                Mathf.Max(1f, initialTerrainXZSizeMeters)
            );

            SetAllHeightsFlat(td, 0f);
            td.terrainLayers = Array.Empty<TerrainLayer>();

            GameObject go = Terrain.CreateTerrainGameObject(td);
            go.name = runtimeTerrainName;
            go.transform.SetParent(root, false);
            go.transform.localPosition = Vector3.zero;
            go.transform.localRotation = Quaternion.identity;
            go.transform.localScale = Vector3.one;

            var t = go.GetComponent<Terrain>();
            _createdRuntimeTerrain = t;

            _originalTerrainData = null;
            _runtimeTerrainData = null;

            Debug.Log("[EidoMap] Created fresh runtime Terrain.");
            return t;
        }

        private static void SetAllHeightsFlat(TerrainData td, float height01)
        {
            if (!td) return;

            int res = Mathf.Max(33, td.heightmapResolution);
            float[,] heights = new float[res, res];

            float h = Mathf.Clamp01(height01);
            if (h != 0f)
            {
                for (int z = 0; z < res; z++)
                    for (int x = 0; x < res; x++)
                        heights[z, x] = h;
            }

            td.SetHeights(0, 0, heights);
        }

        private static void DestroyGameObjectSafe(GameObject go)
        {
            if (!go) return;

#if UNITY_EDITOR
            if (!Application.isPlaying)
                UnityEngine.Object.DestroyImmediate(go);
            else
                UnityEngine.Object.Destroy(go);
#else
            UnityEngine.Object.Destroy(go);
#endif
        }

        // --------------------------------------------------------------------
        // Capture entrypoint
        // --------------------------------------------------------------------

        private void CaptureAoiTerrainHeight(AoiBounds b)
        {
            if (!applyHeightAfterSatellite) return;

            if (!useMapbox)
            {
                Debug.LogWarning("[EidoMap] Height capture requires useMapbox=true.");
                return;
            }

            var t = GetOrCreatePipelineTerrain();
            if (!t)
            {
                Debug.LogWarning("[EidoMap] Height capture enabled but no target Terrain is assigned and createTerrainIfMissing=false.");
                return;
            }

            int z = terrainRgbZoom;
            bool use2x = terrainRgbUse2xTiles;

            StartCoroutine(DownloadTerrainRgbMosaic(b, z, use2x, mosaic =>
            {
                if (!mosaic.HasValue)
                {
                    Debug.LogWarning("[EidoMap] Terrain-RGB mosaic download returned null.");
                    return;
                }

                // 1) Center must resize to true AOI meters first
                ApplyTerrainHeightsFromTerrainRgb(t, mosaic.Value, b);

                // 2) Now neighbors can anchor to center terrain size (no 200x200 collapse)
                TryBuildForegroundNeighbors(b);
            }));
        }


        // --------------------------------------------------------------------
        // Terrain-RGB tile mosaic download
        // --------------------------------------------------------------------

        private IEnumerator DownloadTerrainRgbMosaic(
            AoiBounds b,
            int z,
            bool use2x,
            Action<TerrainRgbMosaic?> onDone)
        {
            int tilePx = use2x ? 512 : 256;

            int xMin = LonToTileX(b.minLon, z);
            int xMax = LonToTileX(b.maxLon, z);
            int yMin = LatToTileY(b.maxLat, z); // north
            int yMax = LatToTileY(b.minLat, z); // south

            // Ensure ordering
            if (xMax < xMin) { int t = xMin; xMin = xMax; xMax = t; }
            if (yMax < yMin) { int t = yMin; yMin = yMax; yMax = t; }

            // Add a 1-tile guard band around the AOI tile coverage so sampling never clamps to mosaic edges.
            int n = 1 << z;
            if (terrainRgbGuardBandTiles)
            {
                xMin -= 1; xMax += 1;
                yMin -= 1; yMax += 1;
            }

            xMin = Mathf.Clamp(xMin, 0, n - 1);
            xMax = Mathf.Clamp(xMax, 0, n - 1);
            yMin = Mathf.Clamp(yMin, 0, n - 1);
            yMax = Mathf.Clamp(yMax, 0, n - 1);

            int tilesW = (xMax - xMin + 1);
            int tilesH = (yMax - yMin + 1);

            int outW = tilesW * tilePx;
            int outH = tilesH * tilePx;

            var mosaic = new Texture2D(outW, outH, TextureFormat.RGBA32, false, true);
            mosaic.wrapMode = TextureWrapMode.Clamp;
            mosaic.filterMode = FilterMode.Point;

            for (int ty = yMin; ty <= yMax; ty++)
            {
                for (int tx = xMin; tx <= xMax; tx++)
                {
                    string url = BuildTerrainRgbTileUrl(z, tx, ty, use2x);
                    if (debugStaticUrl) Debug.Log($"[EidoMap] Terrain-RGB tile URL: {url}");

                    // Prefer a linear data download path when available (Terrain-RGB is data, not imagery).
                    using (var req = new UnityWebRequest(url, UnityWebRequest.kHttpVerbGET))
                    {
#if UNITY_2021_2_OR_NEWER
                        var dh = new DownloadHandlerTexture(new DownloadedTextureParams
                        {
                            readable = true,
                            //mipChain = false,
                            linearColorSpace = true,
                        });
                        req.downloadHandler = dh;
#else
                        req.downloadHandler = new DownloadHandlerTexture();
#endif
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

                        tileTex.wrapMode = TextureWrapMode.Clamp;
                        tileTex.filterMode = FilterMode.Point;

                        // Copy pixels into mosaic. Place north at top.
                        int px = (tx - xMin) * tilePx;
                        int pyFromTop = (ty - yMin) * tilePx;
                        int py = outH - tilePx - pyFromTop;

                        var pixels = tileTex.GetPixels32();
                        mosaic.SetPixels32(px, py, tilePx, tilePx, pixels);
                    }
                }
            }

            mosaic.Apply(false, false);

            Color32[] rawPixels = mosaic.GetPixels32();

            onDone?.Invoke(new TerrainRgbMosaic
            {
                tex = mosaic,
                pixels = rawPixels,
                width = mosaic.width,
                height = mosaic.height,
                z = z,
                tilePx = tilePx,
                xMin = xMin,
                yMin = yMin,
            });
        }

        private string BuildTerrainRgbTileUrl(int z, int x, int y, bool use2x)
        {
            string scale = use2x ? "@2x" : "";
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

        // --------------------------------------------------------------------
        // WebMercator pixel conversion (for correct AOI sampling)
        // --------------------------------------------------------------------

        private static double LonToWorldPx(double lon, int z, int tilePx)
        {
            double n = Math.Pow(2.0, z);
            return ((lon + 180.0) / 360.0) * (n * tilePx);
        }

        private static double LatToWorldPy(double lat, int z, int tilePx)
        {
            double latRad = lat * Math.PI / 180.0;
            double n = Math.Pow(2.0, z);
            double y = (1.0 - Math.Log(Math.Tan(latRad) + 1.0 / Math.Cos(latRad)) / Math.PI) / 2.0;
            return y * (n * tilePx);
        }

        // --------------------------------------------------------------------
        // Byte-accurate sampling helpers (preferred for Terrain-RGB data)
        // --------------------------------------------------------------------

        private static Color32 SampleRgbNearest(Color32[] pixels, int width, int height, float u, float v)
        {
            int x = Mathf.Clamp(Mathf.RoundToInt(u * (width - 1)), 0, width - 1);
            int y = Mathf.Clamp(Mathf.RoundToInt(v * (height - 1)), 0, height - 1);
            return pixels[y * width + x];
        }

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
            double cos4 = Math.Cos(4.0 * latRad);
            double cos6 = Math.Cos(6.0 * latRad);

            double cos3 = Math.Cos(3.0 * latRad);
            double cos5 = Math.Cos(5.0 * latRad);

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


        }

        private void EnsureRuntimeTerrainData(Terrain t)
        {
            if (!cloneTerrainDataAtRuntime) return;
            if (!t) return;

            // If we created the terrain ourselves, it's already runtime data.
            if (_createdRuntimeTerrain && t == _createdRuntimeTerrain) return;

            if (_runtimeTerrainData) return;

            _originalTerrainData = t.terrainData;
            if (!_originalTerrainData)
            {
                Debug.LogWarning("[EidoMap] Terrain has no TerrainData to clone.");
                return;
            }

            _runtimeTerrainData = UnityEngine.Object.Instantiate(_originalTerrainData);
            _runtimeTerrainData.name = _originalTerrainData.name + " (Runtime)";
            t.terrainData = _runtimeTerrainData;
        }

        private void SyncSatelliteLayerTileSizeToTerrain(Terrain t)
        {
            if (!t || !t.terrainData) return;

            var td = t.terrainData;
            var layers = td.terrainLayers;
            if (layers == null || layers.Length == 0 || !layers[0]) return;

            layers[0].tileSize = new Vector2(td.size.x, td.size.z);
            layers[0].tileOffset = Vector2.zero;

            td.terrainLayers = layers;
            td.SetBaseMapDirty();
            t.Flush();
        }

        private static double LerpD(double a, double b, double t)
        {
            return a + (b - a) * t;
        }


        private void ApplyTerrainHeightsFromTerrainRgb(
            Terrain t,
            TerrainRgbMosaic mosaic,
            AoiBounds b,
            float? forceWidthMeters = null,
            float? forceHeightMeters = null,
            bool resizeXZ = true)
        {
            if (!t || !t.terrainData || mosaic.tex == null) return;

            EnsureRuntimeTerrainData(t);

            // Keep the texture sane for any debugging/inspection, but do not rely on it for sampling if sampleHeightFromRawPixels is true.
            mosaic.tex.wrapMode = TextureWrapMode.Clamp;
            mosaic.tex.filterMode = FilterMode.Bilinear;

            // Compute AOI meters, but allow callers (neighbors) to lock all tiles to the center footprint.
            ComputeAoiMeters(b, out float aoiWidthMeters, out float aoiHeightMeters);
            float widthMeters = forceWidthMeters ?? aoiWidthMeters;
            float heightMeters = forceHeightMeters ?? aoiHeightMeters;

            int hmRes = ClampPow2Plus1(terrainHeightmapResolution);

            // Mosaic origin in world pixel space (top-left of the stitched mosaic tile grid).
            int z = mosaic.z;
            int tilePx = mosaic.tilePx;
            double worldX0 = mosaic.xMin * (double)tilePx;
            double worldY0 = mosaic.yMin * (double)tilePx;

            float minM = float.PositiveInfinity;
            float maxM = float.NegativeInfinity;

            int clampCount = 0;
            int totalSamples = hmRes * hmRes;

            bool useRaw = sampleHeightFromRawPixels &&
                          mosaic.pixels != null &&
                          mosaic.pixels.Length == (mosaic.width * mosaic.height);

            // Pass 1: min/max
            for (int zi = 0; zi < hmRes; zi++)
            {
                float tz = (hmRes <= 1) ? 0f : (zi / (float)(hmRes - 1));
                if (flipHeightZ) tz = 1f - tz;

                double lat = LerpD(b.minLat, b.maxLat, tz);

                for (int xi = 0; xi < hmRes; xi++)
                {
                    float tx = (hmRes <= 1) ? 0f : (xi / (float)(hmRes - 1));
                    if (flipHeightX) tx = 1f - tx;

                    double lon = LerpD(b.minLon, b.maxLon, tx);

                    double wx = LonToWorldPx(lon, z, tilePx);
                    double wy = LatToWorldPy(lat, z, tilePx);

                    double mx = wx - worldX0;                 // from left
                    double myTop = wy - worldY0;              // from top
                    double my = (mosaic.height - 1) - myTop;  // convert to bottom-left origin

                    float u = (float)(mx / (mosaic.width - 1));
                    float v = (float)(my / (mosaic.height - 1));

                    if (debugTerrainRgbClampCounts)
                    {
                        if (u < 0f || u > 1f || v < 0f || v > 1f)
                            clampCount++;
                    }

                    u = Mathf.Clamp01(u);
                    v = Mathf.Clamp01(v);

                    float m;
                    if (useRaw)
                    {
                        Color32 c32 = SampleRgbNearest(mosaic.pixels, mosaic.width, mosaic.height, u, v);
                        m = DecodeTerrainRgbMeters(c32);
                    }
                    else
                    {
                        Color c = mosaic.tex.GetPixelBilinear(u, v);
                        m = DecodeTerrainRgbMeters((Color32)c);
                    }

                    if (m < minM) minM = m;
                    if (m > maxM) maxM = m;
                }
            }

            if (debugTerrainRgbClampCounts)
            {
                Debug.Log($"[EidoMap] Terrain-RGB sampling clamps: {clampCount}/{totalSamples} (guardBand={terrainRgbGuardBandTiles})");
            }

            if (!float.IsFinite(minM) || !float.IsFinite(maxM) || maxM <= minM)
            {
                Debug.LogWarning("[EidoMap] Terrain-RGB decode produced invalid min/max. Skipping SetHeights.");
                return;
            }

            float range = (maxM - minM) + Mathf.Max(0f, heightRangePaddingMeters);

            // Phase Charlie: neighbors should not resize X/Z (to prevent drift/overlap). Y can still be updated via range.
            if (resizeXZ)
            {
                EnsureTerrainSizedToAoiMeters(t, widthMeters, heightMeters, range);
            }
            else
            {
                var td0 = t.terrainData;
                EnsureTerrainSizedToAoiMeters(t, td0.size.x, td0.size.z, range);
            }

            // If satellite was applied before we resized, re-sync layer tiling now.
            SyncSatelliteLayerTileSizeToTerrain(t);

            // Helpful debug: meters per sample
            float mPerSampleX = widthMeters / (hmRes - 1);
            float mPerSampleZ = heightMeters / (hmRes - 1);
            Debug.Log($"[EidoMap] meters/sample: {mPerSampleX:0.00} x {mPerSampleZ:0.00}");

            float[,] heights = new float[hmRes, hmRes];

            // Pass 2: fill heights
            for (int zi = 0; zi < hmRes; zi++)
            {
                float tz = (hmRes <= 1) ? 0f : (zi / (float)(hmRes - 1));
                if (flipHeightZ) tz = 1f - tz;

                double lat = LerpD(b.minLat, b.maxLat, tz);

                for (int xi = 0; xi < hmRes; xi++)
                {
                    float tx = (hmRes <= 1) ? 0f : (xi / (float)(hmRes - 1));
                    if (flipHeightX) tx = 1f - tx;

                    double lon = LerpD(b.minLon, b.maxLon, tx);

                    double wx = LonToWorldPx(lon, z, tilePx);
                    double wy = LatToWorldPy(lat, z, tilePx);

                    double mx = wx - worldX0;
                    double myTop = wy - worldY0;
                    double my = (mosaic.height - 1) - myTop;

                    float u = (float)(mx / (mosaic.width - 1));
                    float v = (float)(my / (mosaic.height - 1));

                    u = Mathf.Clamp01(u);
                    v = Mathf.Clamp01(v);

                    float m;
                    if (useRaw)
                    {
                        Color32 c32 = SampleRgbNearest(mosaic.pixels, mosaic.width, mosaic.height, u, v);
                        m = DecodeTerrainRgbMeters(c32);
                    }
                    else
                    {
                        Color c = mosaic.tex.GetPixelBilinear(u, v);
                        m = DecodeTerrainRgbMeters((Color32)c);
                    }

                    heights[zi, xi] = Mathf.Clamp01((m - minM) / range);
                }
            }

            t.terrainData.SetHeights(0, 0, heights);

            Debug.Log(
                $"[EidoMap] Height OK. AOI meters(local): {aoiWidthMeters:0.0} x {aoiHeightMeters:0.0}, " +
                $"AOI meters(used): {widthMeters:0.0} x {heightMeters:0.0}, " +
                $"min/max: {minM:0.0}..{maxM:0.0}, hmRes: {hmRes}, z: {z}, tilePx: {tilePx}, " +
                $"guardBand={terrainRgbGuardBandTiles}, raw={useRaw}, resizeXZ={resizeXZ}"
            );
        }


        private void OnDisable()
        {
#if UNITY_EDITOR
            // Clean up runtime-created terrain so it doesn't linger in the editor between plays.
            if (_createdRuntimeTerrain)
            {
                var go = _createdRuntimeTerrain.gameObject;
                _createdRuntimeTerrain = null;
                DestroyGameObjectSafe(go);
            }

            // Restore original TerrainData if we cloned someone else's TerrainData.
            if (_originalTerrainData && targetTerrain)
                targetTerrain.terrainData = _originalTerrainData;

            _runtimeTerrainData = null;
            _originalTerrainData = null;
#endif
        }
    }
}
