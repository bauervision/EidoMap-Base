using UnityEngine;

namespace EidoMap
{
    public class ScaleTestHarness : MonoBehaviour
    {
        [Header("References")]
        [SerializeField] private MapView mapView;

        [Tooltip("Leave null if Terrain is created at runtime; we will find it when you click Spawn.")]
        [SerializeField] private Terrain terrain;

        [Header("Player Prefab")]
        [SerializeField] private GameObject firstPersonControllerPrefab;

        [Tooltip("How high above the sampled terrain to spawn the player.")]
        [SerializeField] private float spawnHeightAboveGroundMeters = 2.0f;

        [Tooltip("Optional offset from terrain center (meters).")]
        [SerializeField] private Vector3 spawnOffset = Vector3.zero;

        [Header("Scale Markers")]
        [SerializeField] private bool spawnScaleMarkers = true;

        [Tooltip("Meters forward from spawn for the 10m and 100m markers.")]
        [SerializeField] private Vector3 markerDirection = new Vector3(0f, 0f, 1f);

        [SerializeField] private float marker10m = 10f;
        [SerializeField] private float marker100m = 100f;

        [Header("Debug")]
        [SerializeField] private bool logScaleSnapshotOnSpawn = true;

        private GameObject _spawnedPlayer;

        private void Reset()
        {
            mapView = FindFirstObjectByType<MapView>();
        }

        private void Awake()
        {
            if (!mapView) mapView = FindFirstObjectByType<MapView>();
        }

        public bool CanSpawnNow()
        {
            var t = ResolveTerrain();
            if (!t || !t.terrainData) return false;

            // Your runtime terrain starts at 200x200; after capture+height it should be AOI-sized.
            // This prevents spawning before capture.
            return (t.terrainData.size.x > 250f || t.terrainData.size.z > 250f);
        }

        // Hook this to your UI button: "Spawn Player"
        public void SpawnPlayerNow()
        {
            if (!firstPersonControllerPrefab)
            {
                Debug.LogWarning("[EidoMap][Scale] No FirstPersonController prefab assigned.");
                return;
            }

            var t = ResolveTerrain();
            if (!t || !t.terrainData)
            {
                Debug.LogWarning("[EidoMap][Scale] No Terrain found yet. Capture terrain first.");
                return;
            }

            if (!CanSpawnNow())
            {
                Debug.LogWarning("[EidoMap][Scale] Terrain exists but still looks like the initial placeholder size. Capture/apply height first.");
                return;
            }

            if (_spawnedPlayer)
            {
                Debug.Log("[EidoMap][Scale] Player already spawned; skipping.");
                return;
            }

            _spawnedPlayer = SpawnPlayerAndMarkers(t);

            if (logScaleSnapshotOnSpawn)
                LogScaleSnapshot(t);
        }

        private Terrain ResolveTerrain()
        {
            if (mapView.targetTerrain && mapView.targetTerrain.terrainData) return mapView.targetTerrain;
            else
            {
                // MapView creates/assigns targetTerrain internally. We can find it by searching.
                // If you expose targetTerrain publicly later, we can switch to a direct reference.
                var ts = FindObjectsByType<Terrain>(FindObjectsSortMode.None);
                if (ts != null && ts.Length > 0)
                {
                    // Heuristic: pick the first active terrain with TerrainData
                    for (int i = 0; i < ts.Length; i++)
                    {
                        if (ts[i] && ts[i].terrainData)
                        {
                            terrain = ts[i];
                            return terrain;
                        }
                    }
                }
            }

            return null;
        }

        private GameObject SpawnPlayerAndMarkers(Terrain t)
        {
            var td = t.terrainData;

            Vector3 centerWorld = t.transform.position + new Vector3(td.size.x * 0.5f, 0f, td.size.z * 0.5f);
            Vector3 spawnWorld = centerWorld + spawnOffset;

            float yGround = t.SampleHeight(spawnWorld) + t.transform.position.y;
            spawnWorld.y = yGround + spawnHeightAboveGroundMeters;

            var player = Instantiate(firstPersonControllerPrefab, spawnWorld, Quaternion.identity);

            // Optional: face “north” (+Z)
            var fpc = player.GetComponent<FirstPersonController>();
            if (fpc) fpc.SnapYaw(0f);

            if (spawnScaleMarkers)
                SpawnMarkers(spawnWorld);

            return player;
        }

        private void SpawnMarkers(Vector3 spawnWorld)
        {
            Vector3 dir = markerDirection.sqrMagnitude < 0.0001f ? Vector3.forward : markerDirection.normalized;

            CreatePillar("Scale_2m_Pillar", spawnWorld + new Vector3(2f, 0f, 2f), 2f);
            CreateMarker("Scale_Start", spawnWorld);
            CreateMarker("Scale_10m", spawnWorld + dir * marker10m);
            CreateMarker("Scale_100m", spawnWorld + dir * marker100m);
        }

        private static void CreateMarker(string name, Vector3 pos)
        {
            var go = GameObject.CreatePrimitive(PrimitiveType.Cylinder);
            go.name = name;
            go.transform.position = new Vector3(pos.x, pos.y + 0.5f, pos.z);
            go.transform.localScale = new Vector3(0.5f, 0.5f, 0.5f);
            Object.Destroy(go.GetComponent<Collider>());
        }

        private static void CreatePillar(string name, Vector3 pos, float heightMeters)
        {
            var go = GameObject.CreatePrimitive(PrimitiveType.Cube);
            go.name = name;
            go.transform.position = new Vector3(pos.x, pos.y + heightMeters * 0.5f, pos.z);
            go.transform.localScale = new Vector3(0.25f, heightMeters, 0.25f);
            Object.Destroy(go.GetComponent<Collider>());
        }

        private void LogScaleSnapshot(Terrain t)
        {
            var td = t.terrainData;
            Debug.Log($"[EidoMap][Scale] TerrainData.size = {td.size} (meters if 1u=1m)");
            Debug.Log($"[EidoMap][Scale] HeightmapRes = {td.heightmapResolution}  meters/sample ~= {td.size.x / (td.heightmapResolution - 1):0.00} x {td.size.z / (td.heightmapResolution - 1):0.00}");

            if (mapView)
            {
                var b = mapView.GetAoiBounds();
                double midLat = (b.minLat + b.maxLat) * 0.5;
                double midLon = (b.minLon + b.maxLon) * 0.5;
                double widthM = HaversineMeters(midLat, b.minLon, midLat, b.maxLon);
                double heightM = HaversineMeters(b.minLat, midLon, b.maxLat, midLon);
                Debug.Log($"[EidoMap][Scale] AOI ~= {widthM:0.0}m x {heightM:0.0}m");
            }
        }

        private static double HaversineMeters(double lat1, double lon1, double lat2, double lon2)
        {
            const double R = 6371000.0;
            double dLat = (lat2 - lat1) * Mathf.Deg2Rad;
            double dLon = (lon2 - lon1) * Mathf.Deg2Rad;

            double a =
                System.Math.Sin(dLat * 0.5) * System.Math.Sin(dLat * 0.5) +
                System.Math.Cos(lat1 * Mathf.Deg2Rad) * System.Math.Cos(lat2 * Mathf.Deg2Rad) *
                System.Math.Sin(dLon * 0.5) * System.Math.Sin(dLon * 0.5);

            double c = 2.0 * System.Math.Atan2(System.Math.Sqrt(a), System.Math.Sqrt(1.0 - a));
            return R * c;
        }
    }
}