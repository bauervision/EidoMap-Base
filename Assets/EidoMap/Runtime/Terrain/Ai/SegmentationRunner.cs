using UnityEngine;
using Unity.InferenceEngine;
using UnityEngine.UI;

namespace EidoMap.Runtime.Terrain.Ai
{
    public sealed class SegmentationRunner : MonoBehaviour
    {
        [Header("Model")]
        [SerializeField] private ModelAsset modelAsset;

        [Header("Runtime")]
        [SerializeField] private BackendType backend = BackendType.GPUCompute;

        [Header("Debug")]
        [SerializeField] private RawImage debugPreviewImage;
        [SerializeField] private bool showResizedInputPreview = true;
        private Model _runtimeModel;
        private Worker _worker;

        public bool HasModel => modelAsset != null;
        public bool IsReady => _runtimeModel != null && _worker != null;

        private void Awake()
        {
            InitializeWorker();
        }

        private void OnDestroy()
        {
            DisposeWorker();
        }

        public void RunPreview(Texture2D sourceTexture)
        {
            if (sourceTexture == null)
            {
                Debug.LogWarning("[EidoMap] SegmentationRunner.RunPreview called with null texture.");
                return;
            }

            if (!IsReady)
            {
                Debug.LogWarning("[EidoMap] SegmentationRunner is not ready. Worker was not created.");
                return;
            }

            const int modelSize = 520;

            using var input = new Tensor<float>(new TensorShape(1, 3, modelSize, modelSize));

            if (showResizedInputPreview && debugPreviewImage != null)
            {
                var preview = BuildResizedPreviewTexture(sourceTexture, modelSize, modelSize);
                debugPreviewImage.texture = preview;
            }
            
            TextureConverter.ToTensor(sourceTexture, input, new TextureTransform());

            _worker.Schedule(input);

            var rawOutput = _worker.PeekOutput("mask");
            if (rawOutput == null)
            {
                Debug.LogWarning("[EidoMap] PeekOutput(\"mask\") returned null.");
                return;
            }

            var output = rawOutput as Tensor<int>;
            if (output == null)
            {
                Debug.LogWarning($"[EidoMap] Output 'mask' was not Tensor<int>. Actual type: {rawOutput.GetType().FullName}");
                return;
            }

            using var cpuOutput = output.ReadbackAndClone();

            Debug.Log($"[EidoMap] Output shape: {cpuOutput.shape}");

            var maskTexture = BuildDebugMaskTexture(cpuOutput, modelSize, modelSize);

            Debug.Log($"[EidoMap] Debug mask built: {maskTexture.width}x{maskTexture.height}");
        }

        private void InitializeWorker()
        {
            DisposeWorker();

            if (modelAsset == null)
            {
                Debug.LogWarning("[EidoMap] SegmentationRunner has no model asset assigned.");
                return;
            }

            _runtimeModel = ModelLoader.Load(modelAsset);

            Debug.Log($"[EidoMap] Model loaded. inputs={_runtimeModel.inputs.Count}, outputs={_runtimeModel.outputs.Count}");

            for (int i = 0; i < _runtimeModel.outputs.Count; i++)
            {
                var output = _runtimeModel.outputs[i];
                Debug.Log($"[EidoMap] Output[{i}] name={output.name} index={output.index}");
            }

            _worker = new Worker(_runtimeModel, backend);
            Debug.Log($"[EidoMap] SegmentationRunner initialized. backend={backend}");
        }

        private void DisposeWorker()
        {
            _worker?.Dispose();
            _worker = null;
            _runtimeModel = null;
        }

        private Texture2D BuildDebugMaskTexture(Tensor<int> maskTensor, int width, int height)
        {
            var tex = new Texture2D(width, height, TextureFormat.RGBA32, false, false);
            tex.wrapMode = TextureWrapMode.Clamp;
            tex.filterMode = FilterMode.Point;

            var pixels = new Color32[width * height];
            var seen = new System.Collections.Generic.HashSet<int>();

            for (int y = 0; y < height; y++)
            {
                for (int x = 0; x < width; x++)
                {
                    int classId = maskTensor[0, y, x];
                    seen.Add(classId);

                    int i = y * width + x;
                    pixels[i] = ColorForClass(classId);
                }
            }

            tex.SetPixels32(pixels);
            tex.Apply(false, false);

            Debug.Log($"[EidoMap] Classes seen: {string.Join(", ", seen)}");

            return tex;
        }

        private static Color32 ColorForClass(int classId)
        {
            return classId switch
            {
                0 => new Color32(0, 0, 0, 255),
                1 => new Color32(255, 0, 0, 255),
                2 => new Color32(0, 255, 0, 255),
                3 => new Color32(0, 0, 255, 255),
                4 => new Color32(255, 255, 0, 255),
                5 => new Color32(255, 0, 255, 255),
                6 => new Color32(0, 255, 255, 255),
                7 => new Color32(255, 128, 0, 255),
                8 => new Color32(128, 0, 255, 255),
                9 => new Color32(0, 128, 255, 255),
                10 => new Color32(128, 255, 0, 255),
                11 => new Color32(255, 0, 128, 255),
                12 => new Color32(128, 128, 128, 255),
                13 => new Color32(255, 255, 255, 255),
                14 => new Color32(64, 255, 64, 255),
                15 => new Color32(255, 64, 64, 255),
                16 => new Color32(64, 64, 255, 255),
                17 => new Color32(255, 192, 64, 255),
                18 => new Color32(192, 64, 255, 255),
                19 => new Color32(64, 255, 192, 255),
                20 => new Color32(192, 192, 0, 255),
                _ => new Color32(32, 32, 32, 255),
            };
        }

        private Texture2D BuildResizedPreviewTexture(Texture sourceTexture, int width, int height)
        {
            var rt = RenderTexture.GetTemporary(width, height, 0, RenderTextureFormat.ARGB32);
            var previous = RenderTexture.active;

            Graphics.Blit(sourceTexture, rt);

            RenderTexture.active = rt;

            var tex = new Texture2D(width, height, TextureFormat.RGBA32, false, false);
            tex.ReadPixels(new Rect(0, 0, width, height), 0, 0);
            tex.Apply(false, false);

            RenderTexture.active = previous;
            RenderTexture.ReleaseTemporary(rt);

            return tex;
        }
    }
}