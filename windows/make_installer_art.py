from PIL import Image, ImageDraw
ico = Image.open("windows/isai.ico").convert("RGBA")

# Welcome/finish dialog: 493x312, dark gradient panel on the left 164px, white elsewhere
W, H = 493, 312
img = Image.new("RGB", (W, H), "white")
px = img.load()
top, bot = (14, 14, 16), (37, 37, 47)
for y in range(H):
    t = y / (H - 1)
    c = tuple(int(top[i] + (bot[i] - top[i]) * t) for i in range(3))
    for x in range(164):
        px[x, y] = c
logo = ico.resize((96, 96), Image.LANCZOS)
img.paste(logo, (34, 100), logo)
img.save("windows/installer/dialog.bmp")

# Banner: 493x58, white with the logo on the right
ban = Image.new("RGB", (493, 58), "white")
small = ico.resize((40, 40), Image.LANCZOS)
ban.paste(small, (493 - 40 - 14, 9), small)
ban.save("windows/installer/banner.bmp")
