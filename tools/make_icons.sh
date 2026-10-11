#!/usr/bin/env bash
# Downloads the Isai icon and generates every launcher size + the web icons.
set -euo pipefail
cd "$(dirname "$0")/.."
URL="https://github.com/nithinana/isai-ytdlp/blob/main/apple-touch-icon.png?raw=true"
curl -fsSL "$URL" -o /tmp/isai-icon.png
RES=app/src/main/res
for pair in mdpi:48 hdpi:72 xhdpi:96 xxhdpi:144 xxxhdpi:192; do
  d=${pair%%:*}; px=${pair##*:}
  mkdir -p "$RES/mipmap-$d"
  convert /tmp/isai-icon.png -resize ${px}x${px} "$RES/mipmap-$d/ic_launcher.png"
  cp "$RES/mipmap-$d/ic_launcher.png" "$RES/mipmap-$d/ic_launcher_round.png"
done
cp /tmp/isai-icon.png app/src/main/assets/apple-touch-icon.png
convert /tmp/isai-icon.png -resize 192x192 app/src/main/assets/favicon.png
# Thirai logo for the startup screen (falls back to the app icon)
mkdir -p app/src/main/res/drawable-nodpi
if curl -fsSL "https://thirai.uk/static/thiraiwhite.png" -o /tmp/thirai-logo.png && convert /tmp/thirai-logo.png PNG32:app/src/main/res/drawable-nodpi/thirai_logo.png; then :; else
  convert /tmp/isai-icon.png PNG32:app/src/main/res/drawable-nodpi/thirai_logo.png
fi
# Notification small icon (the logo shown next to "Phone speaker"): Android needs a white-on-transparent
# silhouette. Drop your own square white-on-transparent PNG at tools/ic_stat_isai.png to override.
SRC="tools/ic_stat_isai.png"
if [ ! -f "$SRC" ]; then
  if [ -f /tmp/thirai-logo.png ]; then SRC=/tmp/thirai-logo.png; else SRC=/tmp/isai-icon.png; fi
fi
OPAQUE=$(identify -format '%[opaque]' "${SRC}[0]" 2>/dev/null || echo True)
for pair in mdpi:24 hdpi:36 xhdpi:48 xxhdpi:72 xxxhdpi:96; do
  d=${pair%%:*}; px=${pair##*:}; inner=$((px*11/12))
  mkdir -p "$RES/drawable-$d"
  if [ "$OPAQUE" = "True" ]; then PRE="-colorspace Gray -alpha copy"; else PRE=""; fi
  convert "${SRC}[0]" $PRE -channel RGB -evaluate set 100% +channel -trim +repage \
    -resize ${inner}x${inner} -background none -gravity center -extent ${px}x${px} "PNG32:$RES/drawable-$d/ic_stat_isai.png"
done
echo "icons ok"
