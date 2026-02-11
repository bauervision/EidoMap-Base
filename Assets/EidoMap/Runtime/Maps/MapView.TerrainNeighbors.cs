// Assets/EidoMap/Runtime/Maps/MapView.TerrainNeighbors.cs
using System;
using System.Collections;
using System.Collections.Generic;
using UnityEngine;

namespace EidoMap
{
    public partial class MapView
    {
        [Header("Phase Charlie: Foreground Neighbor Terrains")]
        [Tooltip("If true, build neighboring terrains around the AOI terrain for immersion.")]
        [SerializeField] private bool buildForegroundTerrains = true;

        [Tooltip("1 = 3x3 (center + 8). 2 = 5x5, etc.")]
        [SerializeField] private int foregroundRing = 1;

        [Tooltip("Heightmap resolution for neighbor terrains (must be 2^n + 1).")]
        [SerializeField] private int foregroundNeighborResolution = 257;

        [Tooltip("If true, destroy/rebuild the foreground container each capture.")]
        [SerializeField] private bool rebuildForegroundEachCapture = true;

        [Tooltip("Parent object name under runtimeTerrainRoot that holds all foreground terrains.")]
        [SerializeField] private string foregroundRootName = "ForegroundTerrains";

        [Tooltip("If true, call SetNeighbors after all tiles are generated.")]
        [SerializeField] private bool setNeighborsAfterBuild = true;

        [Tooltip("If true, force shared border heights to match exactly (removes cracks).")]
        [SerializeField] private bool stitchForegroundEdges = true;

        [Tooltip("Neighbor tile Y size (meters). Temporary initial value before decode sets real range.")]
        [SerializeField] private float neighborInitialYSizeMeters = 50f;

        [Tooltip("If true, neighbor terrains get the same TerrainLayer tiling behavior once resized.")]
        [SerializeField] private bool syncNeighborSatelliteTiling = true;

        private struct NeighborKey : IEquatable<NeighborKey>
        {
            public int gx; // west=-, east=+
            public int gz; // south=-, north=+

            public NeighborKey(int gx, int gz) { this.gx = gx; this.gz = gz; }

            public bool Equals(NeighborKey other) => gx == other.gx && gz == other.gz;
            public override bool Equals(object obj) => obj is NeighborKey o && Equals(o);
            public override int GetHashCode() => (gx * 397) ^ gz;
            public override string ToString() => $"({gx},{gz})";
        }

        private void TryBuildForegroundNeighbors(AoiBounds center)
        {
            if (!buildForegroundTerrains) return;
            if (!useMapbox) return;

            var tCenter = GetOrCreatePipelineTerrain();
            if (!tCenter || !tCenter.terrainData) return;

            int ring = Mathf.Clamp(foregroundRing, 0, 4);
            if (ring <= 0) return;

            StartCoroutine(BuildForegroundNeighborsCoroutine(center, ring));
        }

        private IEnumerator BuildForegroundNeighborsCoroutine(AoiBounds center, int ring)
        {
            var root = GetOrCreateForegroundRoot();
            if (!root) yield break;

            if (rebuildForegroundEachCapture)
            {
                for (int i = root.childCount - 1; i >= 0; i--)
                {
                    var child = root.GetChild(i);
                    if (child) DestroyGameObjectSafe(child.gameObject);
                }
            }

            ComputeAoiMeters(center, out float aoiWidthMeters, out float aoiHeightMeters);

            int z = terrainRgbZoom;
            int tilePx = terrainRgbUse2xTiles ? 512 : 256;

            double cx0 = LonToWorldPx(center.minLon, z, tilePx);
            double cx1 = LonToWorldPx(center.maxLon, z, tilePx);

            // WebMercator: worldY increases southward.
            double cyN = LatToWorldPy(center.maxLat, z, tilePx);
            double cyS = LatToWorldPy(center.minLat, z, tilePx);

            double wPx = cx1 - cx0;
            double hPx = cyS - cyN;

            if (!(wPx > 1.0) || !(hPx > 1.0))
            {
                Debug.LogWarning("[EidoMap] Foreground neighbors: AOI pixel width/height invalid.");
                yield break;
            }

            var terrains = new Dictionary<NeighborKey, Terrain>();

            for (int gz = -ring; gz <= ring; gz++)
            {
                for (int gx = -ring; gx <= ring; gx++)
                {
                    if (gx == 0 && gz == 0) continue;

                    var key = new NeighborKey(gx, gz);

                    var existing = root.Find(TileName(key));
                    if (existing)
                    {
                        var et = existing.GetComponent<Terrain>();
                        if (et) terrains[key] = et;
                        continue;
                    }

                    var t = CreateNeighborTerrain(root, key, aoiWidthMeters, aoiHeightMeters);
                    if (t) terrains[key] = t;
                }
            }

            foreach (var kv in terrains)
            {
                NeighborKey key = kv.Key;
                Terrain t = kv.Value;
                if (!t || !t.terrainData) continue;

                double nx0 = cx0 + (key.gx * wPx);
                double nx1 = cx1 + (key.gx * wPx);

                // gz positive means "north" in Unity +Z; north is smaller worldY.
                double nyN = cyN + (-key.gz * hPx);
                double nyS = cyS + (-key.gz * hPx);

                var nb = new AoiBounds
                {
                    minLon = (float)WorldPxToLon(nx0, z, tilePx),
                    maxLon = (float)WorldPxToLon(nx1, z, tilePx),

                    maxLat = (float)WorldPyToLat(nyN, z, tilePx),
                    minLat = (float)WorldPyToLat(nyS, z, tilePx),
                };

                bool done = false;
                bool ok = false;

                yield return DownloadTerrainRgbMosaic(nb, z, terrainRgbUse2xTiles, mosaic =>
                {
                    if (!mosaic.HasValue)
                    {
                        done = true;
                        ok = false;
                        return;
                    }

                    ApplyTerrainHeightsFromTerrainRgb(t, mosaic.Value, nb);

                    if (syncNeighborSatelliteTiling)
                        SyncSatelliteLayerTileSizeToTerrain(t);

                    done = true;
                    ok = true;
                });

                while (!done) yield return null;

                if (!ok)
                {
                    Debug.LogWarning($"[EidoMap] Foreground neighbor {key} failed; stopping neighbor build.");
                    yield break;
                }
            }

            if (setNeighborsAfterBuild)
            {
                ApplyUnityNeighborsForForeground(terrains);
                TrySetCenterNeighbors(terrains);
            }

            if (stitchForegroundEdges)
                StitchForegroundEdges(terrains);

            Debug.Log("[EidoMap] Foreground neighbors complete.");
        }

        private Transform GetOrCreateForegroundRoot()
        {
            Transform parent = runtimeTerrainRoot ? runtimeTerrainRoot : transform;
            var existing = parent.Find(foregroundRootName);
            if (existing) return existing;

            var go = new GameObject(foregroundRootName);
            go.transform.SetParent(parent, false);
            go.transform.localPosition = Vector3.zero;
            go.transform.localRotation = Quaternion.identity;
            go.transform.localScale = Vector3.one;
            return go.transform;
        }

        private static string TileName(NeighborKey k) => $"Tile_{k.gx}_{k.gz}";

        private Terrain CreateNeighborTerrain(Transform root, NeighborKey key, float aoiWidthMeters, float aoiHeightMeters)
        {
            int res = ClampPow2Plus1(foregroundNeighborResolution);

            var td = new TerrainData();
            td.name = $"Terrain {TileName(key)} Data";
            td.heightmapResolution = res;

            td.size = new Vector3(
                Mathf.Max(1f, aoiWidthMeters),
                Mathf.Max(1f, neighborInitialYSizeMeters),
                Mathf.Max(1f, aoiHeightMeters)
            );

            SetAllHeightsFlat(td, 0f);
            td.terrainLayers = Array.Empty<TerrainLayer>();

            var go = Terrain.CreateTerrainGameObject(td);
            go.name = TileName(key);
            go.transform.SetParent(root, false);

            go.transform.localPosition = new Vector3(
                key.gx * aoiWidthMeters,
                0f,
                key.gz * aoiHeightMeters
            );
            go.transform.localRotation = Quaternion.identity;
            go.transform.localScale = Vector3.one;

            var t = go.GetComponent<Terrain>();

            if (targetTerrain && targetTerrain.terrainData)
            {
                var layers = targetTerrain.terrainData.terrainLayers;
                if (layers != null && layers.Length > 0 && layers[0])
                {
                    td.terrainLayers = new[] { layers[0] };
                    td.SetBaseMapDirty();
                    t.Flush();
                }
            }

            return t;
        }

        private void ApplyUnityNeighborsForForeground(Dictionary<NeighborKey, Terrain> terrains)
        {
            foreach (var kv in terrains)
            {
                NeighborKey k = kv.Key;
                Terrain t = kv.Value;
                if (!t) continue;

                terrains.TryGetValue(new NeighborKey(k.gx - 1, k.gz), out Terrain left);
                terrains.TryGetValue(new NeighborKey(k.gx + 1, k.gz), out Terrain right);
                terrains.TryGetValue(new NeighborKey(k.gx, k.gz + 1), out Terrain top);
                terrains.TryGetValue(new NeighborKey(k.gx, k.gz - 1), out Terrain bottom);

                t.SetNeighbors(left, top, right, bottom);
            }
        }

        private void TrySetCenterNeighbors(Dictionary<NeighborKey, Terrain> terrains)
        {
            var c = GetOrCreatePipelineTerrain();
            if (!c) return;

            terrains.TryGetValue(new NeighborKey(-1, 0), out Terrain left);
            terrains.TryGetValue(new NeighborKey(1, 0), out Terrain right);
            terrains.TryGetValue(new NeighborKey(0, 1), out Terrain top);
            terrains.TryGetValue(new NeighborKey(0, -1), out Terrain bottom);

            c.SetNeighbors(left, top, right, bottom);
        }

        private void StitchForegroundEdges(Dictionary<NeighborKey, Terrain> terrains)
        {
            foreach (var kv in terrains)
            {
                NeighborKey k = kv.Key;
                var a = kv.Value;
                if (!a || !a.terrainData) continue;

                if (terrains.TryGetValue(new NeighborKey(k.gx + 1, k.gz), out Terrain east) && east && east.terrainData)
                    CopySharedEdgeEastWest(a.terrainData, east.terrainData);

                if (terrains.TryGetValue(new NeighborKey(k.gx, k.gz + 1), out Terrain north) && north && north.terrainData)
                    CopySharedEdgeNorthSouth(a.terrainData, north.terrainData);
            }
        }

        private static void CopySharedEdgeEastWest(TerrainData west, TerrainData east)
        {
            int rw = west.heightmapResolution;
            int re = east.heightmapResolution;
            if (rw != re) return;

            int r = rw;
            float[,] wEdge = west.GetHeights(r - 1, 0, 1, r);
            float[,] eEdge = east.GetHeights(0, 0, 1, r);

            for (int z = 0; z < r; z++)
                eEdge[z, 0] = wEdge[z, 0];

            east.SetHeights(0, 0, eEdge);
        }

        private static void CopySharedEdgeNorthSouth(TerrainData south, TerrainData north)
        {
            int rs = south.heightmapResolution;
            int rn = north.heightmapResolution;
            if (rs != rn) return;

            int r = rs;
            float[,] sEdge = south.GetHeights(0, r - 1, r, 1);
            float[,] nEdge = north.GetHeights(0, 0, r, 1);

            for (int x = 0; x < r; x++)
                nEdge[0, x] = sEdge[0, x];

            north.SetHeights(0, 0, nEdge);
        }

        private static double WorldPxToLon(double worldX, int z, int tilePx)
        {
            double n = Math.Pow(2.0, z) * tilePx;
            double x = worldX / n;
            return x * 360.0 - 180.0;
        }

        private static double WorldPyToLat(double worldY, int z, int tilePx)
        {
            double n = Math.Pow(2.0, z) * tilePx;
            double y = worldY / n;
            double merc = Math.PI * (1.0 - 2.0 * y);
            double latRad = Math.Atan(Math.Sinh(merc));
            return latRad * 180.0 / Math.PI;
        }
    }
}
