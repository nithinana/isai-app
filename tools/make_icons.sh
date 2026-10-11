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
echo "icons ok"
