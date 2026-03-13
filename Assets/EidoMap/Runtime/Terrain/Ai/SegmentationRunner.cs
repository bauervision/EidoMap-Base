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
        [SerializeField] private bool isolateSingleClass = false;
        [SerializeField][Range(0, 7)] private int isolatedClassId = 4;

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

            const int modelSize = 512;
            const int tileCountPerAxis = 4;
            const int debugPreviewSize = 512;

            int sourceWidth = sourceTexture.width;
            int sourceHeight = sourceTexture.height;

            int tileSourceWidth = sourceWidth / tileCountPerAxis;
            int tileSourceHeight = sourceHeight / tileCountPerAxis;

            if (tileSourceWidth <= 0 || tileSourceHeight <= 0)
            {
                Debug.LogWarning(
                    $"[EidoMap] Invalid tile size from source texture {sourceWidth}x{sourceHeight} " +
                    $"with tileCountPerAxis={tileCountPerAxis}.");
                return;
            }

            Debug.Log(
                $"[EidoMap] RunPreview source={sourceWidth}x{sourceHeight}, " +
                $"tiles={tileCountPerAxis}x{tileCountPerAxis}, " +
                $"tileSource={tileSourceWidth}x{tileSourceHeight}, modelInput={modelSize}x{modelSize}");

            float[] combinedLogits = null;
            float[] combinedWeights = null;
            int classCount = -1;
            int tileMaskWidth = -1;
            int tileMaskHeight = -1;
            int combinedWidth = -1;
            int combinedHeight = -1;

            var allSeen = new System.Collections.Generic.HashSet<int>();

            for (int tileY = 0; tileY < tileCountPerAxis; tileY++)
            {
                for (int tileX = 0; tileX < tileCountPerAxis; tileX++)
                {
                    int cropX = tileX * tileSourceWidth;

                    int cropYTopBased = tileY * tileSourceHeight;
                    int cropY = sourceHeight - cropYTopBased - tileSourceHeight;

                    int cropWidth = (tileX == tileCountPerAxis - 1)
                        ? (sourceWidth - cropX)
                        : tileSourceWidth;

                    int cropHeight = (tileY == tileCountPerAxis - 1)
                        ? (sourceHeight - cropYTopBased)
                        : tileSourceHeight;

                    if (cropWidth <= 0 || cropHeight <= 0)
                    {
                        Debug.LogWarning(
                            $"[EidoMap] Skipping invalid crop for tile ({tileX}, {tileY}) " +
                            $"at ({cropX}, {cropY}) size={cropWidth}x{cropHeight}");
                        continue;
                    }

                    var tileSource = CropTexture(sourceTexture, cropX, cropY, cropWidth, cropHeight);
                    var tileForModel = BuildResizedPreviewTexture(tileSource, modelSize, modelSize);

                    using var input = new Tensor<float>(new TensorShape(1, 3, modelSize, modelSize));
                    FillInputTensorNormalized(tileForModel, input, modelSize, modelSize);

                    _worker.Schedule(input);

                    var rawOutput = _worker.PeekOutput("logits");
                    if (rawOutput == null)
                    {
                        Debug.LogWarning($"[EidoMap] PeekOutput(\"logits\") returned null for tile ({tileX}, {tileY}).");
                        Destroy(tileForModel);
                        Destroy(tileSource);
                        continue;
                    }

                    var output = rawOutput as Tensor<float>;
                    if (output == null)
                    {
                        Debug.LogWarning(
                            $"[EidoMap] Output 'logits' was not Tensor<float> for tile ({tileX}, {tileY}). " +
                            $"Actual type: {rawOutput.GetType().FullName}");
                        Destroy(tileForModel);
                        Destroy(tileSource);
                        continue;
                    }

                    using var cpuOutput = output.ReadbackAndClone();

                    if (tileX == 0 && tileY == 0)
                    {
                        Debug.Log($"[EidoMap] Logits shape: {cpuOutput.shape}");
                    }

                    if (cpuOutput.shape.rank != 4)
                    {
                        Debug.LogWarning(
                            $"[EidoMap] Expected 4D logits tensor, got rank {cpuOutput.shape.rank} " +
                            $"for tile ({tileX}, {tileY}).");
                        Destroy(tileForModel);
                        Destroy(tileSource);
                        continue;
                    }

                    int outputClassCount = cpuOutput.shape[1];
                    int outputHeight = cpuOutput.shape[2];
                    int outputWidth = cpuOutput.shape[3];

                    if (combinedLogits == null)
                    {
                        classCount = outputClassCount;
                        tileMaskWidth = outputWidth;
                        tileMaskHeight = outputHeight;
                        combinedWidth = tileMaskWidth * tileCountPerAxis;
                        combinedHeight = tileMaskHeight * tileCountPerAxis;

                        combinedLogits = new float[classCount * combinedWidth * combinedHeight];
                        combinedWeights = new float[combinedWidth * combinedHeight];

                        Debug.Log(
                            $"[EidoMap] Combined mask initialized. classes={classCount}, " +
                            $"tileMask={tileMaskWidth}x{tileMaskHeight}, combined={combinedWidth}x{combinedHeight}");
                    }
                    else
                    {
                        if (outputClassCount != classCount || outputWidth != tileMaskWidth || outputHeight != tileMaskHeight)
                        {
                            Debug.LogWarning(
                                $"[EidoMap] Output shape mismatch at tile ({tileX}, {tileY}). " +
                                $"Expected classes={classCount}, size={tileMaskWidth}x{tileMaskHeight} but got " +
                                $"classes={outputClassCount}, size={outputWidth}x{outputHeight}");
                            Destroy(tileForModel);
                            Destroy(tileSource);
                            continue;
                        }
                    }

                    int destX = tileX * tileMaskWidth;
                    int destY = (tileCountPerAxis - 1 - tileY) * tileMaskHeight;

                    AccumulateLogits(
                        cpuOutput,
                        combinedLogits,
                        combinedWeights,
                        combinedWidth,
                        combinedHeight,
                        destX,
                        destY);

                    Destroy(tileForModel);
                    Destroy(tileSource);
                }
            }

            if (combinedLogits == null || combinedWeights == null)
            {
                Debug.LogWarning("[EidoMap] No valid logits were accumulated. Debug mask was not built.");
                return;
            }

            var combinedMask = BuildDebugMaskTextureFromCombinedLogits(
                combinedLogits,
                combinedWeights,
                classCount,
                combinedWidth,
                combinedHeight,
                allSeen);

            if (debugPreviewImage != null)
            {
                var preview = BuildResizedPreviewTexture(combinedMask, debugPreviewSize, debugPreviewSize);
                debugPreviewImage.texture = preview;
            }

            Debug.Log($"[EidoMap] Classes seen: {string.Join(", ", allSeen)}");
            Debug.Log($"[EidoMap] Debug mask built: {combinedMask.width}x{combinedMask.height}");

            Destroy(combinedMask);
        }


        private void CollectSeenClassesFromLogits(Tensor<float> logitsTensor, System.Collections.Generic.HashSet<int> seen)
        {
            int classCount = logitsTensor.shape[1];
            int height = logitsTensor.shape[2];
            int width = logitsTensor.shape[3];

            for (int y = 0; y < height; y++)
            {
                for (int x = 0; x < width; x++)
                {
                    int bestClass = 0;
                    float bestScore = logitsTensor[0, 0, y, x];

                    for (int c = 1; c < classCount; c++)
                    {
                        float score = logitsTensor[0, c, y, x];
                        if (score > bestScore)
                        {
                            bestScore = score;
                            bestClass = c;
                        }
                    }

                    seen.Add(bestClass);
                }
            }
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


        private Texture2D CropTexture(Texture2D source, int x, int y, int width, int height)
        {
            var pixels = source.GetPixels(x, y, width, height);

            var tex = new Texture2D(width, height, TextureFormat.RGBA32, false, false);
            tex.SetPixels(pixels);
            tex.Apply(false, false);

            return tex;
        }

        private Texture2D BuildDebugMaskTextureFromLogits(Tensor<float> logitsTensor)
        {
            int classCount = logitsTensor.shape[1];
            int height = logitsTensor.shape[2];
            int width = logitsTensor.shape[3];

            var tex = new Texture2D(width, height, TextureFormat.RGBA32, false, false);
            tex.wrapMode = TextureWrapMode.Clamp;
            tex.filterMode = FilterMode.Point;

            var pixels = new Color32[width * height];
            var seen = new System.Collections.Generic.HashSet<int>();

            for (int y = 0; y < height; y++)
            {
                for (int x = 0; x < width; x++)
                {
                    int bestClass = 0;
                    float bestScore = logitsTensor[0, 0, y, x];

                    for (int c = 1; c < classCount; c++)
                    {
                        float score = logitsTensor[0, c, y, x];
                        if (score > bestScore)
                        {
                            bestScore = score;
                            bestClass = c;
                        }
                    }

                    seen.Add(bestClass);

                    int i = y * width + x;
                    pixels[i] = ColorForClass(bestClass);
                }
            }

            tex.SetPixels32(pixels);
            tex.Apply(false, false);

            Debug.Log($"[EidoMap] Classes seen: {string.Join(", ", seen)}");

            return tex;
        }

        private void FillInputTensorNormalized(Texture sourceTexture, Tensor<float> input, int width, int height)
        {
            var resized = BuildResizedPreviewTexture(sourceTexture, width, height);
            var pixels = resized.GetPixels32();

            const float meanR = 0.485f;
            const float meanG = 0.456f;
            const float meanB = 0.406f;

            const float stdR = 0.229f;
            const float stdG = 0.224f;
            const float stdB = 0.225f;

            for (int y = 0; y < height; y++)
            {
                for (int x = 0; x < width; x++)
                {
                    int i = y * width + x;
                    Color32 p = pixels[i];

                    float r = p.r / 255f;
                    float g = p.g / 255f;
                    float b = p.b / 255f;

                    input[0, 0, y, x] = (r - meanR) / stdR;
                    input[0, 1, y, x] = (g - meanG) / stdG;
                    input[0, 2, y, x] = (b - meanB) / stdB;
                }
            }

            Destroy(resized);
        }
        private static Color32 ColorForClass(int classId)
        {
            return classId switch
            {
                0 => new Color32(24, 24, 24, 255),      // Ignore
                1 => new Color32(110, 110, 110, 255),   // Background
                2 => new Color32(220, 60, 60, 255),     // Building
                3 => new Color32(35, 35, 35, 255),      // Road
                4 => new Color32(70, 150, 255, 255),    // Water
                5 => new Color32(194, 160, 102, 255),   // Barren
                6 => new Color32(34, 139, 34, 255),     // Forest
                7 => new Color32(144, 238, 144, 255),   // Agricultural
                _ => new Color32(255, 0, 255, 255),
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

        private void AccumulateLogits(
    Tensor<float> tileLogits,
    float[] combinedLogits,
    float[] combinedWeights,
    int combinedWidth,
    int combinedHeight,
    int destX,
    int destY)
        {
            int classCount = tileLogits.shape[1];
            int tileHeight = tileLogits.shape[2];
            int tileWidth = tileLogits.shape[3];

            for (int y = 0; y < tileHeight; y++)
            {
                for (int x = 0; x < tileWidth; x++)
                {
                    int outX = destX + x;
                    int outY = destY + y;

                    if (outX < 0 || outX >= combinedWidth || outY < 0 || outY >= combinedHeight)
                    {
                        continue;
                    }

                    int pixelIndex = outY * combinedWidth + outX;
                    combinedWeights[pixelIndex] += 1f;

                    for (int c = 0; c < classCount; c++)
                    {
                        int logitsIndex = ((c * combinedHeight + outY) * combinedWidth) + outX;
                        combinedLogits[logitsIndex] += tileLogits[0, c, y, x];
                    }
                }
            }
        }

        private Texture2D BuildDebugMaskTextureFromCombinedLogits(
    float[] combinedLogits,
    float[] combinedWeights,
    int classCount,
    int width,
    int height,
    System.Collections.Generic.HashSet<int> seen)
        {
            var tex = new Texture2D(width, height, TextureFormat.RGBA32, false, false);
            tex.wrapMode = TextureWrapMode.Clamp;
            tex.filterMode = FilterMode.Point;

            var pixels = new Color32[width * height];

            for (int y = 0; y < height; y++)
            {
                for (int x = 0; x < width; x++)
                {
                    int pixelIndex = y * width + x;
                    float weight = combinedWeights[pixelIndex];

                    int bestClass = 0;
                    float bestScore = float.NegativeInfinity;

                    for (int c = 0; c < classCount; c++)
                    {
                        int logitsIndex = ((c * height + y) * width) + x;
                        float score = weight > 0f
                            ? combinedLogits[logitsIndex] / weight
                            : float.NegativeInfinity;

                        if (score > bestScore)
                        {
                            bestScore = score;
                            bestClass = c;
                        }
                    }

                    seen.Add(bestClass);

                    if (isolateSingleClass)
                    {
                        pixels[pixelIndex] = bestClass == isolatedClassId
                            ? ColorForClass(bestClass)
                            : new Color32(40, 40, 40, 255);
                    }
                    else
                    {
                        pixels[pixelIndex] = ColorForClass(bestClass);
                    }
                }
            }

            tex.SetPixels32(pixels);
            tex.Apply(false, false);

            return tex;
        }


    }
}