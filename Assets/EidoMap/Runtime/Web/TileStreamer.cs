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
    /// - epoch cancel handled by caller via closures (MapView checks epoch)
    /// </summary>
    public sealed class TileStreamer
    {
        public struct Request
        {
            public TileKey key;
            public int epoch;
            public string url;
            public Action<Texture2D> onSuccess;
            public Action<string> onFail;
        }

        private readonly MonoBehaviour _host;
        private readonly int _maxConcurrent;

        private readonly Queue<Request> _queue = new();
        private readonly HashSet<TileKey> _inFlight = new();
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
            if (_inFlight.Contains(req.key)) return;

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
                    if (_inFlight.Contains(req.key)) continue;

                    _inFlight.Add(req.key);
                    _active++;
                    _host.StartCoroutine(LoadOne(req));
                }
                yield return null;
            }

            _pumpCo = null;
        }

        private IEnumerator LoadOne(Request req)
        {
            using var uwr = UnityWebRequestTexture.GetTexture(req.url, true); // nonReadable=true

#if UNITY_WEBGL
            uwr.SetRequestHeader("Cache-Control", "max-age=3600");
#endif

            yield return uwr.SendWebRequest();

            if (uwr.result == UnityWebRequest.Result.Success)
            {
                var tex = DownloadHandlerTexture.GetContent(uwr);
                tex.wrapMode = TextureWrapMode.Clamp;
                tex.filterMode = FilterMode.Bilinear;
                req.onSuccess?.Invoke(tex);
            }
            else
            {
                req.onFail?.Invoke(uwr.error);
            }

            _inFlight.Remove(req.key);
            _active--;
        }

        public void ClearQueue()
        {
            _queue.Clear();
        }
    }
}
