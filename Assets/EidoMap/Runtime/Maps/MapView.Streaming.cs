// Assets/EidoMap/Runtime/Maps/MapView.Streaming.cs
using System.Collections;
using System.Collections.Generic;
using UnityEngine;
using UnityEngine.UI;
using EidoMap.Core;
using EidoMap.Web;

namespace EidoMap
{
    public partial class MapView
    {
        private TileStreamer _streamer;

        private int _epoch; // bump to cancel stale loads after zoom
        private readonly HashSet<(int epoch, TileKey key)> _loading = new();

        // Deferred trim
        private HashSet<TileKey> _lastNeededForTrim;
        private Coroutine _deferredTrimCo;


        private void RequestTile(int tx, int ty, int z, RawImage img)
        {
            if (!img) return;

            int localEpoch = _epoch;

            int n = 1 << z;
            int xReq = Mod(tx, n);
            int yReq = Mod(ty, n);

            var key = new TileKey(z, xReq, yReq);

            // Stamp identity in VIEW coords (tx/ty) so PositionTile + Matches stay consistent.
            var tag = img.GetComponent<TileViewTag>();
            if (tag == null) tag = img.gameObject.AddComponent<TileViewTag>();
            tag.Set(tx, ty, z, localEpoch);

            // Cache fast-path
            if (TryGetFromCache(xReq, yReq, z, out var cached))
            {
                img.uvRect = new Rect(0, 0, 1, 1);
                img.texture = cached;
                return;
            }

            // URL
            int serverTileSize =
                (speedWhileInteracting && _interacting) ? 256 :
                (displayTilePixels >= 512 ? 512 : 256);

            string url = useMapbox
                ? TileUrlBuilder.BuildMapboxStyleUrl(mapboxStyleId, mapboxAccessToken, xReq, yReq, z, serverTileSize)
                : TileUrlBuilder.BuildTemplateUrl(imageryUrlTemplate, xReq, yReq, z);

            var loadKey = (localEpoch, key);
            if (_loading.Contains(loadKey)) return;
            _loading.Add(loadKey);

            _streamer.RequestTile(new TileStreamer.Request
            {
                key = key,
                epoch = localEpoch,
                url = url,

                onSuccess = tex =>
                {
                    if (localEpoch != _epoch) { _loading.Remove(loadKey); return; }
                    if (!img) { _loading.Remove(loadKey); return; }

                    var liveTag = img.GetComponent<TileViewTag>();
                    if (liveTag == null || !liveTag.Matches(tx, ty, z, localEpoch))
                    {
                        _loading.Remove(loadKey);
                        return;
                    }

                    img.uvRect = new Rect(0, 0, 1, 1);
                    img.texture = tex;

                    PutInCache(xReq, yReq, z, tex);
                    _loading.Remove(loadKey);
                },

                onFail = err =>
                {
                    Debug.LogWarning($"Tile load failed {url}: {err}");
                    _loading.Remove(loadKey);
                }
            });
        }
    }
}
