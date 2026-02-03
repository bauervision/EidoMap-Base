// Assets/EidoMap/Runtime/Web/TileStreamer.cs
using System;
using System.Collections;
using System.Collections.Generic;
using UnityEngine;
using UnityEngine.Networking;
using EidoMap.Core;

namespace EidoMap.Web
{
    /// <summary>
    /// Coroutine-based tile streaming with:
    /// - request queue
    /// - concurrency cap
    /// - in-flight keyed by (epoch, tile)
    /// </summary>
    public sealed class TileStreamer
    {
        public struct Request
        {
            public TileKey key;         // (z,x,y)
            public int epoch;           // caller epoch at request time
            public string url;

            // Callbacks MUST be safe to invoke after zoom changes.
            public Action<Texture2D> onSuccess;
            public Action<string> onFail;
        }

        private readonly MonoBehaviour _host;
        private readonly int _maxConcurrent;

        private readonly Queue<Request> _queue = new();

        // IMPORTANT: in-flight is per epoch to avoid blocking re-requests after zoom.
        private readonly HashSet<(int epoch, TileKey key)> _inFlight = new();

        private Coroutine _pumpCo;
        private int _active;

        public int ActiveLoads => _active;
        public int QueuedCount => _queue.Count;

        public TileStreamer(MonoBehaviour host, int maxConcurrent)
        {
            _host = host;
            _maxConcurrent = Mathf.Max(1, maxConcurrent);
        }

        public void RequestTile(Request req)
        {
            if (string.IsNullOrEmpty(req.url)) return;

            var inflightKey = (req.epoch, req.key);
            if (_inFlight.Contains(inflightKey)) return;

            _queue.Enqueue(req);
            if (_pumpCo == null)
                _pumpCo = _host.StartCoroutine(Pump());
        }

        private IEnumerator Pump()
        {
            while (_queue.Count > 0 || _active > 0)
            {
                while (_active < _maxConcurrent && _queue.Count > 0)
                {
                    var req = _queue.Dequeue();
                    var inflightKey = (req.epoch, req.key);

                    if (_inFlight.Contains(inflightKey)) continue;

                    _inFlight.Add(inflightKey);
                    _active++;
                    _host.StartCoroutine(LoadOne(req));
                }
                yield return null;
            }

            _pumpCo = null;
        }

        private IEnumerator LoadOne(Request req)
        {
            var inflightKey = (req.epoch, req.key);

            using var uwr = UnityWebRequestTexture.GetTexture(req.url, true);

#if UNITY_WEBGL
            uwr.SetRequestHeader("Cache-Control", "max-age=3600");
#endif

            yield return uwr.SendWebRequest();

            try
            {
                if (uwr.result == UnityWebRequest.Result.Success)
                {
                    var tex = DownloadHandlerTexture.GetContent(uwr);

                    // Reduce edge bleeding; keep crispness configurable from caller if needed.
                    tex.wrapMode = TextureWrapMode.Clamp;
                    tex.filterMode = FilterMode.Point;
                    req.onSuccess?.Invoke(tex);
                }
                else
                {
                    req.onFail?.Invoke(uwr.error);
                }
            }
            finally
            {
                _inFlight.Remove(inflightKey);
                _active--;
            }
        }

        public void ClearQueue()
        {
            _queue.Clear();
        }

        public void ClearInFlight()
        {
            _inFlight.Clear();
        }
    }
}
