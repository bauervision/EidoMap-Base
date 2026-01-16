// Assets/EidoMap/Runtime/Web/TileUrlBuilder.cs
namespace EidoMap.Web
{
    public static class TileUrlBuilder
    {
        public static string BuildTemplateUrl(string template, int x, int y, int z)
        {
            return template
                .Replace("{z}", z.ToString())
                .Replace("{x}", x.ToString())
                .Replace("{y}", y.ToString());
        }

        public static string BuildMapboxStyleUrl(
            string styleId,
            string accessToken,
            int x,
            int y,
            int z,
            int serverTileSize)
        {
            return
                $"https://api.mapbox.com/styles/v1/{styleId}/tiles/{serverTileSize}/{z}/{x}/{y}?access_token={accessToken}";
        }
    }
}
