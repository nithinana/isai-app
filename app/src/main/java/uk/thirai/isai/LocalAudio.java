package uk.thirai.isai;

import android.content.ContentResolver;
import android.content.ContentUris;
import android.content.Context;
import android.database.Cursor;
import android.graphics.Bitmap;
import android.media.MediaMetadataRetriever;
import android.net.Uri;
import android.os.Build;
import android.os.ParcelFileDescriptor;
import android.provider.MediaStore;
import android.util.Size;
import android.webkit.WebResourceResponse;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * "Local files": every song on the device, read from MediaStore (only the list + tags; nothing is copied).
 * The page plays them through https://isai.thirai.uk/__lf/{id} (audio, with Range so seeking works) and shows
 * their artwork from /__lfart/{id}. Both are answered here, inside the app, and never leave the device.
 */
final class LocalAudio {
    static final String AUDIO = "/__lf/", ART = "/__lfart/";
    private static final Pattern RANGE = Pattern.compile("bytes=(\\d*)-(\\d*)");

    private LocalAudio() {}

    /** JSON array: [{id,t,a,al,d,s,ts,f,p,x}] (title, artist, album, seconds, bytes, added-epoch-s, file, folder, ext). */
    static String scan(Context ctx) throws Exception {
        JSONArray out = new JSONArray();
        Uri coll = Build.VERSION.SDK_INT >= 29
                ? MediaStore.Audio.Media.getContentUri(MediaStore.VOLUME_EXTERNAL)
                : MediaStore.Audio.Media.EXTERNAL_CONTENT_URI;
        boolean q = Build.VERSION.SDK_INT >= 29;
        String[] proj = {
                MediaStore.Audio.Media._ID, MediaStore.Audio.Media.TITLE, MediaStore.Audio.Media.ARTIST,
                MediaStore.Audio.Media.ALBUM, MediaStore.Audio.Media.DURATION, MediaStore.Audio.Media.SIZE,
                MediaStore.Audio.Media.DATE_ADDED, MediaStore.Audio.Media.DISPLAY_NAME,
                q ? MediaStore.Audio.Media.RELATIVE_PATH : MediaStore.Audio.Media.DATA
        };
        // music only: skip ringtones, notifications, alarms and clips shorter than 20 s
        String sel = MediaStore.Audio.Media.IS_RINGTONE + "=0 AND " + MediaStore.Audio.Media.IS_NOTIFICATION + "=0 AND "
                + MediaStore.Audio.Media.IS_ALARM + "=0 AND " + MediaStore.Audio.Media.DURATION + ">=20000";
        try (Cursor c = ctx.getContentResolver().query(coll, proj, sel, null, MediaStore.Audio.Media.TITLE + " COLLATE NOCASE ASC")) {
            if (c == null) return "[]";
            while (c.moveToNext()) {
                String file = c.getString(7) == null ? "" : c.getString(7);
                String path = c.getString(8) == null ? "" : c.getString(8);
                String folder = path;
                if (!q) { int i = path.lastIndexOf('/'); folder = i > 0 ? path.substring(0, i) : ""; }
                folder = folder.replaceAll("^/storage/emulated/0/", "").replaceAll("/+$", "");
                int dot = file.lastIndexOf('.');
                out.put(new JSONObject()
                        .put("id", c.getLong(0))
                        .put("t", clean(c.getString(1)))
                        .put("a", clean(c.getString(2)))
                        .put("al", clean(c.getString(3)))
                        .put("d", Math.round(c.getLong(4) / 1000.0))
                        .put("s", c.getLong(5))
                        .put("ts", c.getLong(6))
                        .put("f", file)
                        .put("p", folder)
                        .put("x", dot >= 0 ? file.substring(dot + 1).toLowerCase() : ""));
            }
        }
        return out.toString();
    }

    private static String clean(String s) {
        if (s == null) return "";
        s = s.trim();
        return "<unknown>".equalsIgnoreCase(s) ? "" : s;
    }

    /** Answers /__lf/{id} and /__lfart/{id}; null means "not ours". */
    static WebResourceResponse serve(Context ctx, String path, Map<String, String> reqHeaders) {
        boolean art = path.startsWith(ART);
        String idStr = path.substring((art ? ART : AUDIO).length());
        if (!idStr.matches("\\d{1,18}")) return fail(400);
        Uri uri = ContentUris.withAppendedId(MediaStore.Audio.Media.EXTERNAL_CONTENT_URI, Long.parseLong(idStr));
        try {
            return art ? art(ctx, uri) : audio(ctx, uri, reqHeaders);
        } catch (SecurityException e) {
            return fail(403);                       // permission not granted (yet)
        } catch (Exception e) {
            return fail(404);
        }
    }

    private static WebResourceResponse fail(int code) {
        return new WebResourceResponse("text/plain", "utf-8", code, code == 403 ? "Forbidden" : code == 400 ? "Bad Request" : "Not Found",
                new HashMap<String, String>(), new ByteArrayInputStream(new byte[0]));
    }

    private static WebResourceResponse audio(Context ctx, Uri uri, Map<String, String> req) throws IOException {
        ContentResolver cr = ctx.getContentResolver();
        ParcelFileDescriptor pfd = cr.openFileDescriptor(uri, "r");
        if (pfd == null) return fail(404);
        long len = pfd.getStatSize();
        String mime = cr.getType(uri);
        if (mime == null || !mime.startsWith("audio/")) mime = "audio/mpeg";
        long start = 0, end = len - 1;
        boolean partial = false;
        String rh = req == null ? null : (req.get("Range") != null ? req.get("Range") : req.get("range"));
        if (rh != null && len > 0) {
            Matcher m = RANGE.matcher(rh.trim());
            if (m.matches()) {
                try {
                    if (!m.group(1).isEmpty()) {
                        start = Long.parseLong(m.group(1));
                        if (!m.group(2).isEmpty()) end = Math.min(end, Long.parseLong(m.group(2)));
                    } else if (!m.group(2).isEmpty()) {            // "-N": the last N bytes
                        start = Math.max(0, len - Long.parseLong(m.group(2)));
                    }
                    partial = true;
                } catch (NumberFormatException ignored) { start = 0; end = len - 1; partial = false; }
            }
        }
        if (partial && (start >= len || start > end)) {
            try { pfd.close(); } catch (IOException ignored) {}
            Map<String, String> h = new HashMap<>();
            h.put("Content-Range", "bytes */" + len);
            return new WebResourceResponse(mime, null, 416, "Range Not Satisfiable", h, new ByteArrayInputStream(new byte[0]));
        }
        final long count = len > 0 ? end - start + 1 : -1;
        ParcelFileDescriptor.AutoCloseInputStream fis = new ParcelFileDescriptor.AutoCloseInputStream(pfd);   // closing it closes pfd
        try {
            fis.getChannel().position(start);
        } catch (IOException e) {
            fis.close();
            throw e;
        }
        InputStream body = new LimitedStream(fis, count);
        Map<String, String> h = new HashMap<>();
        h.put("Accept-Ranges", "bytes");
        h.put("Access-Control-Allow-Origin", "*");
        h.put("Cache-Control", "no-store");
        if (count >= 0) h.put("Content-Length", String.valueOf(count));
        if (partial) h.put("Content-Range", "bytes " + start + "-" + end + "/" + len);
        return new WebResourceResponse(mime, null, partial ? 206 : 200, partial ? "Partial Content" : "OK", h, body);
    }

    private static WebResourceResponse art(Context ctx, Uri uri) throws IOException {
        byte[] jpg = null;
        if (Build.VERSION.SDK_INT >= 29) {
            try {
                Bitmap b = ctx.getContentResolver().loadThumbnail(uri, new Size(640, 640), null);
                ByteArrayOutputStream bo = new ByteArrayOutputStream();
                b.compress(Bitmap.CompressFormat.JPEG, 88, bo);
                jpg = bo.toByteArray();
            } catch (Exception ignored) {}
        }
        if (jpg == null) {
            MediaMetadataRetriever mr = new MediaMetadataRetriever();
            try {
                mr.setDataSource(ctx, uri);
                jpg = mr.getEmbeddedPicture();
            } catch (Exception ignored) {
            } finally {
                try { mr.release(); } catch (Exception ignored) {}
            }
        }
        if (jpg == null || jpg.length < 200) return fail(404);   // the page falls back to its placeholder
        Map<String, String> h = new HashMap<>();
        h.put("Cache-Control", "max-age=86400");
        h.put("Access-Control-Allow-Origin", "*");
        boolean png = jpg.length > 4 && (jpg[0] & 0xFF) == 0x89 && jpg[1] == 'P';
        return new WebResourceResponse(png ? "image/png" : "image/jpeg", null, 200, "OK", h, new ByteArrayInputStream(jpg));
    }

    /** Reads at most `left` bytes, then closes the file descriptor. */
    private static final class LimitedStream extends InputStream {
        private final InputStream in;
        private long left;

        LimitedStream(InputStream in, long left) { this.in = in; this.left = left; }

        @Override public int read() throws IOException {
            byte[] one = new byte[1];
            int n = read(one, 0, 1);
            return n <= 0 ? -1 : (one[0] & 0xFF);
        }

        @Override public int read(byte[] b, int off, int len) throws IOException {
            if (left == 0) return -1;
            int want = left < 0 ? len : (int) Math.min(len, left);
            int n = in.read(b, off, want);
            if (n > 0 && left > 0) left -= n;
            return n;
        }

        @Override public void close() throws IOException { in.close(); }
    }
}
