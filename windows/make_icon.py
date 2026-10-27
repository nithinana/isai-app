"""Builds windows/isai.ico from the same icon the Android build uses (falls back to a plain tile)."""
import io, os, urllib.request
from PIL import Image, ImageDraw
URL = "https://github.com/nithinana/isai-ytdlp/blob/main/apple-touch-icon.png?raw=true"
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "isai.ico")
try:
    img = Image.open(io.BytesIO(urllib.request.urlopen(URL, timeout=30).read())).convert("RGBA")
except Exception as e:
    print("icon download failed (%s), using a plain tile" % e)
    img = Image.new("RGBA", (256, 256), (10, 10, 11, 255))
    ImageDraw.Draw(img).ellipse((64, 64, 192, 192), fill=(255, 255, 255, 255))
img = img.resize((256, 256), Image.LANCZOS)
img.save(out, sizes=[(16, 16), (32, 32), (48, 48), (64, 64), (128, 128), (256, 256)])
print("wrote", out)
