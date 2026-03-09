// Assets/EidoMap/Runtime/Maps/MapView.TerrainPreview.cs
using UnityEngine;

namespace EidoMap
{
    public partial class MapView
    {
        private TerrainLayer _runtimeLayer;

        private void ApplyCapturedTextureToTerrain(Texture2D tex)
        {
            if (!tex) return;

            var t = GetOrCreatePipelineTerrain();
            if (!t)
            {
                Debug.LogWarning("[EidoMap] No targetTerrain assigned and createTerrainIfMissing=false.");
                return;
            }

            var td = t.terrainData;
            if (!td)
            {
                Debug.LogWarning("[EidoMap] targetTerrain has no TerrainData.");
                return;
            }

            TerrainLayer layer;

            if (reuseTerrainLayer)
            {
                if (_runtimeLayer == null)
                {
                    _runtimeLayer = new TerrainLayer();
                    _runtimeLayer.name = "AOI Runtime Layer";
                }
                layer = _runtimeLayer;
            }
            else
            {
                layer = new TerrainLayer();
                layer.name = "AOI Runtime Layer";
            }

            tex.wrapMode = TextureWrapMode.Clamp;
            tex.filterMode = FilterMode.Bilinear;
            tex.Apply(false, false);

            layer.diffuseTexture = tex;

            layer.tileSize = new Vector2(td.size.x, td.size.z);
            layer.tileOffset = Vector2.zero;

            td.terrainLayers = new TerrainLayer[] { layer };

            td.SetBaseMapDirty();
            t.Flush();

           // Debug.Log($"[EidoMap] Applied AOI imagery to Terrain. tex={tex.width}x{tex.height} tileSize={layer.tileSize}");
        }
    }
}
