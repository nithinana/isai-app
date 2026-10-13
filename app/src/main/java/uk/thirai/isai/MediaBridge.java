package uk.thirai.isai;

import android.app.Activity;
import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.drawable.Icon;
import android.media.MediaMetadata;
import android.media.session.MediaSession;
import android.media.session.PlaybackState;
import android.net.Uri;
import android.os.Build;
import android.os.Handler;
import android.os.Looper;
import android.os.PowerManager;
import android.provider.DocumentsContract;
import android.webkit.JavascriptInterface;
import android.webkit.WebView;

import org.json.JSONObject;

import java.io.OutputStream;
import java.net.HttpURLConnection;
import java.net.URL;

/** Mirrors the page's Media Session (title, artist, cover, play state) into a system media notification. */
public class MediaBridge {
    private static final String CH = "isai_media";
    private static final int NID = 2;
    private static final int DL_ID = 3;
    private static final String CH_DL = "isai_dl";
    static final int REQ_SAVE = 4242;
    private static final String A_PREV = "uk.thirai.isai.PREV", A_PP = "uk.thirai.isai.PP", A_NEXT = "uk.thirai.isai.NEXT";

    private final Activity ctx;
    private final WebView web;
    private final Handler main = new Handler(Looper.getMainLooper());
    private final MediaSession session;
    private final NotificationManager nm;
    private final BroadcastReceiver receiver;

    private String title = "", artist = "", album = "", artUrl = "", state = "none";
    private double dur = 0, pos = 0;
    private float rate = 1f;
    private long posWall = 0;
    private Bitmap art;
    private String lastArtData = "";
    private boolean dlShown = false;
    private int dlIdle = 0;
    private volatile String backendInfo = "";
    private PowerManager.WakeLock wl;
    private final Object saveLock = new Object();
    private String saveWant = null, saveId = null;      // saveWant: waiting on the picker; saveId: file is open for writing
    private OutputStream saveOut = null;
    private Uri saveUri = null;

    MediaBridge(Activity a, WebView w) {
        ctx = a;
        web = w;
        nm = a.getSystemService(NotificationManager.class);
        if (Build.VERSION.SDK_INT >= 26) {
            nm.createNotificationChannel(new NotificationChannel(CH, "Now playing", NotificationManager.IMPORTANCE_LOW));
            nm.createNotificationChannel(new NotificationChannel(CH_DL, "Downloads", NotificationManager.IMPORTANCE_LOW));
        }
        session = new MediaSession(a, "Isai");
        session.setFlags(MediaSession.FLAG_HANDLES_MEDIA_BUTTONS | MediaSession.FLAG_HANDLES_TRANSPORT_CONTROLS);
        session.setCallback(new MediaSession.Callback() {
            @Override public void onPlay() { js("play"); }
            @Override public void onPause() { js("pause"); }
            @Override public void onSkipToNext() { js("nexttrack"); }
            @Override public void onSkipToPrevious() { js("previoustrack"); }
            @Override public void onSeekTo(long p) { js("seekto", "{seekTime:" + (p / 1000.0) + "}"); }
        });
        receiver = new BroadcastReceiver() {
            @Override public void onReceive(Context c, Intent i) {
                String act = i.getAction();
                if (A_PREV.equals(act)) js("previoustrack");
                else if (A_NEXT.equals(act)) js("nexttrack");
                else if (A_PP.equals(act)) js("playing".equals(state) ? "pause" : "play");
            }
        };
        IntentFilter f = new IntentFilter();
        f.addAction(A_PREV); f.addAction(A_PP); f.addAction(A_NEXT);
        if (Build.VERSION.SDK_INT >= 33) a.registerReceiver(receiver, f, Context.RECEIVER_NOT_EXPORTED);
        else a.registerReceiver(receiver, f);
    }

    private void js(String name) { js(name, null); }

    private void js(String name, String arg) {
        final String code = "window.__isaiMedia&&window.__isaiMedia('" + name + "'" + (arg != null ? "," + arg : "") + ")";
        main.post(() -> web.evaluateJavascript(code, null));
    }

    /** JSON like {"url":"http://127.0.0.1:8765","api":0} when the on-device backend is up, else "". */
    @JavascriptInterface
    public String backendInfo() { return backendInfo; }

    void setBackendInfo(String info) { backendInfo = info == null ? "" : info; }

    /** The page's bridge script calls this once it has loaded (proves the page can reach the app). */
    @JavascriptInterface
    public void hello(String info) {
        android.util.Log.d("Isai", "shim hello " + info);
    }

    /** Called from the page (see the shim at the top of index.html). */
    @JavascriptInterface
    public void update(String json) {
        android.util.Log.d("Isai", "media update " + json);
        try {
            JSONObject o = new JSONObject(json);
            final String t = o.optString("t"), ar = o.optString("a"), al = o.optString("al"),
                    au = o.optString("art"), ad = o.optString("artData"), s = o.optString("state", "none");
            final double d = o.optDouble("dur", 0), p = o.optDouble("pos", 0);
            final float r = (float) o.optDouble("rate", 1);
            main.post(() -> apply(t, ar, al, au, ad, s, d, p, r));
        } catch (Exception ignored) {}
    }

    /** Page reports how many downloads are running; hold the CPU awake for them while backgrounded. */
    @JavascriptInterface
    public void downloads(final int n) {
        main.post(() -> {
            if (n > 0) {
                if (wl == null) {
                    wl = ((PowerManager) ctx.getSystemService(Context.POWER_SERVICE)).newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "isai:downloads");
                    wl.setReferenceCounted(false);
                }
                wl.acquire(10 * 60 * 1000L);   // refreshed every 2 s while downloads are active
            } else if (wl != null && wl.isHeld()) {
                wl.release();
            }
        });
    }

    /* ---------- Save a downloaded song to the device ("Save as" popup) ---------- */

    /** Opens Android's system "Save as" dialog; the page hears back via window.__isaiSaved(id, ok, msg). */
    @JavascriptInterface
    public void saveFile(final String id, final String name, final String mime) {
        main.post(() -> {
            synchronized (saveLock) { closeSave(true); saveWant = id; }
            try {
                Intent i = new Intent(Intent.ACTION_CREATE_DOCUMENT)
                        .addCategory(Intent.CATEGORY_OPENABLE)
                        .setType(mime == null || mime.isEmpty() ? "audio/mpeg" : mime)
                        .putExtra(Intent.EXTRA_TITLE, name);
                ctx.startActivityForResult(i, REQ_SAVE);
            } catch (Exception e) {
                synchronized (saveLock) { saveWant = null; }
                saveReply(id, false, "Couldn\u2019t open the save dialog");
            }
        });
    }

    /** Forwarded from MainActivity.onActivityResult. Returns true when the result was ours. */
    boolean onActivityResult(int req, int res, Intent data) {
        if (req != REQ_SAVE) return false;
        final String id;
        synchronized (saveLock) { id = saveWant; saveWant = null; }
        if (id == null) return true;
        if (res != Activity.RESULT_OK || data == null || data.getData() == null) { saveReply(id, false, "cancelled"); return true; }
        try {
            Uri u = data.getData();
            OutputStream o = ctx.getContentResolver().openOutputStream(u, "wt");
            if (o == null) throw new Exception("no stream");
            synchronized (saveLock) { saveUri = u; saveOut = o; saveId = id; }
            saveReply(id, true, "");
        } catch (Exception e) {
            saveReply(id, false, "Couldn\u2019t create the file");
        }
        return true;
    }

    /** One base64 slice of the file, in order. Returns false if the write failed. */
    @JavascriptInterface
    public boolean saveChunk(String id, String b64) {
        synchronized (saveLock) {
            if (saveOut == null || id == null || !id.equals(saveId)) return false;
            try {
                saveOut.write(android.util.Base64.decode(b64, android.util.Base64.DEFAULT));
                return true;
            } catch (Exception e) {
                closeSave(true);
                return false;
            }
        }
    }

    /** ok=true finishes the file; ok=false removes the half-written one. */
    @JavascriptInterface
    public boolean saveEnd(String id, boolean ok) {
        synchronized (saveLock) {
            if (saveOut == null || id == null || !id.equals(saveId)) return false;
            closeSave(!ok);
            return true;
        }
    }

    private void closeSave(boolean discard) {
        synchronized (saveLock) {
            OutputStream o = saveOut; Uri u = saveUri;
            saveOut = null; saveUri = null; saveId = null;
            if (o != null) { try { o.flush(); o.close(); } catch (Exception ignored) {} }
            if (discard && u != null) { try { DocumentsContract.deleteDocument(ctx.getContentResolver(), u); } catch (Exception ignored) {} }
        }
    }

    private void saveReply(String id, boolean ok, String msg) {
        final String code = "window.__isaiSaved&&window.__isaiSaved(" + JSONObject.quote(id) + "," + ok + "," + JSONObject.quote(msg == null ? "" : msg) + ")";
        main.post(() -> web.evaluateJavascript(code, null));
    }

    /** Page reports download progress every 1.5 s; show it as a progress notification. */
    @JavascriptInterface
    public void downloadStatus(final String json) {
        main.post(() -> {
            try {
                JSONObject o = new JSONObject(json);
                boolean busy = o.optBoolean("busy");
                if (busy) {
                    dlIdle = 0; dlShown = true;
                    int n = o.optInt("n"), done = o.optInt("done"), total = o.optInt("total"), pct = o.optInt("pct", -1);
                    String cur = o.optString("title"), label = o.optString("label");
                    String head = total > 1 ? "Downloading " + Math.min(done + 1, total) + " of " + total
                            : (n > 1 ? "Downloading " + n + " songs" : "Downloading song");
                    String text = !cur.isEmpty() ? cur : (!label.isEmpty() ? label : "Preparing\u2026");
                    Notification.Builder b = dlBuilder().setContentTitle(head).setContentText(text)
                            .setOngoing(true).setProgress(100, Math.max(pct, 0), pct < 0);
                    if (pct >= 0) b.setSubText(pct + "%");
                    nm.notify(DL_ID, b.build());
                } else if (dlShown && ++dlIdle >= 2) {
                    dlShown = false;
                    Notification.Builder fb = dlBuilder().setContentTitle("Downloads finished")
                            .setContentText("Saved for offline listening").setAutoCancel(true);
                    if (Build.VERSION.SDK_INT >= 26) fb.setTimeoutAfter(8000);
                    nm.notify(DL_ID, fb.build());
                }
            } catch (Exception ignored) {}
        });
    }

    private Notification.Builder dlBuilder() {
        Notification.Builder b = Build.VERSION.SDK_INT >= 26 ? new Notification.Builder(ctx, CH_DL) : new Notification.Builder(ctx);
        PendingIntent open = PendingIntent.getActivity(ctx, 1,
                new Intent(ctx, MainActivity.class).addFlags(Intent.FLAG_ACTIVITY_SINGLE_TOP | Intent.FLAG_ACTIVITY_REORDER_TO_FRONT),
                PendingIntent.FLAG_IMMUTABLE);
        return b.setSmallIcon(R.drawable.ic_stat_isai).setContentIntent(open).setOnlyAlertOnce(true).setShowWhen(false);
    }

    private void apply(String t, String ar, String al, String au, String ad, String s, double d, double p, float r) {
        boolean changed = !t.equals(title) || !ar.equals(artist) || !al.equals(album) || !s.equals(state)
                || Math.abs(d - dur) > 0.5 || r != rate;
        long now = System.currentTimeMillis();
        double expected = pos + ("playing".equals(state) ? (now - posWall) / 1000.0 * rate : 0);
        if (Math.abs(p - expected) > 1.5) changed = true;   // seek / skip
        title = t; artist = ar; album = al; state = s; dur = d; pos = p; rate = r; posWall = now;
        if (!au.equals(artUrl)) {
            artUrl = au; art = null; changed = true; lastArtData = "";
            fetchArt(au);
        }
        if (!ad.isEmpty() && !ad.equals(lastArtData)) {          // cover sent as image data (downloaded songs)
            lastArtData = ad;
            Bitmap b = decodeDataUrl(ad);
            if (b != null) { art = b; changed = true; }
        }
        if (changed) publish();
    }

    /** Ask the cover endpoint / Google thumbnails for a bigger image than the page's 256 px pick. */
    private static String hiRes(String url) {
        String u = url.replaceAll("([?&]s=)\\d+", "$1640");
        u = u.replaceAll("=w\\d+-h\\d+", "=w640-h640");
        return u;
    }

    private static Bitmap download(String url) throws Exception {
        HttpURLConnection c = (HttpURLConnection) new URL(url).openConnection();
        c.setConnectTimeout(6000); c.setReadTimeout(12000);
        try {
            Bitmap b = BitmapFactory.decodeStream(c.getInputStream());
            if (b != null && Math.max(b.getWidth(), b.getHeight()) > 640) {
                float k = 640f / Math.max(b.getWidth(), b.getHeight());
                b = Bitmap.createScaledBitmap(b, Math.round(b.getWidth() * k), Math.round(b.getHeight() * k), true);
            }
            return b;
        } finally { c.disconnect(); }
    }

    private static Bitmap decodeDataUrl(String d) {
        try {
            byte[] raw = android.util.Base64.decode(d.substring(d.indexOf(',') + 1), android.util.Base64.DEFAULT);
            Bitmap b = BitmapFactory.decodeByteArray(raw, 0, raw.length);
            if (b != null && Math.max(b.getWidth(), b.getHeight()) > 640) {
                float k = 640f / Math.max(b.getWidth(), b.getHeight());
                b = Bitmap.createScaledBitmap(b, Math.round(b.getWidth() * k), Math.round(b.getHeight() * k), true);
            }
            return b;
        } catch (Exception e) {
            return null;
        }
    }

    /** Small LRU of decoded covers + one worker thread, so skipping songs on a slow link never piles up downloads. */
    private final android.util.LruCache<String, Bitmap> artCache = new android.util.LruCache<>(5);
    private final java.util.concurrent.ExecutorService artExec = java.util.concurrent.Executors.newSingleThreadExecutor();
    private volatile int artGen = 0;

    /** true when the connection is too slow to be worth fetching the bigger cover as well. */
    private boolean slowLink() {
        try {
            android.net.ConnectivityManager cm = (android.net.ConnectivityManager) ctx.getSystemService(Context.CONNECTIVITY_SERVICE);
            android.net.Network n = cm.getActiveNetwork();
            android.net.NetworkCapabilities c = n == null ? null : cm.getNetworkCapabilities(n);
            return c != null && c.getLinkDownstreamBandwidthKbps() > 0 && c.getLinkDownstreamBandwidthKbps() < 1500;
        } catch (Exception e) { return false; }
    }

    private void showArt(final String url, final Bitmap bmp) {
        main.post(() -> { if (url.equals(artUrl)) { art = bmp; publish(); } });
    }

    private void fetchArt(final String url) {
        if (url.isEmpty() || url.startsWith("blob:") || url.startsWith("data:")) return;
        final int gen = ++artGen;
        final String hi = hiRes(url);
        Bitmap hit = artCache.get(hi);
        if (hit == null) hit = artCache.get(url);
        if (hit != null) { art = hit; return; }
        artExec.execute(() -> {
            if (gen != artGen) return;                         // the song already changed: skip this one
            Bitmap small = null;
            try { small = download(url); } catch (Exception ignored) {}          // the page's own size first: shows up fast
            if (small != null) { artCache.put(url, small); if (gen == artGen) showArt(url, small); }
            if (gen != artGen || hi.equals(url) || (small != null && slowLink())) return;
            try {
                Bitmap big = download(hi);                                         // then upgrade to the sharper one
                if (big != null) { artCache.put(hi, big); if (gen == artGen) showArt(url, big); }
            } catch (Exception ignored) {}
        });
    }

    private Notification.Action action(int icon, String label, String act) {
        PendingIntent pi = PendingIntent.getBroadcast(ctx, 0, new Intent(act).setPackage(ctx.getPackageName()), PendingIntent.FLAG_IMMUTABLE);
        return new Notification.Action.Builder(Icon.createWithResource(ctx, icon), label, pi).build();
    }

    private void publish() {
        if (title.isEmpty() || "none".equals(state)) {
            nm.cancel(NID);
            session.setActive(false);
            return;
        }
        boolean playing = "playing".equals(state);
        MediaMetadata.Builder mb = new MediaMetadata.Builder()
                .putString(MediaMetadata.METADATA_KEY_TITLE, title)
                .putString(MediaMetadata.METADATA_KEY_ARTIST, artist)
                .putString(MediaMetadata.METADATA_KEY_ALBUM, album)
                .putLong(MediaMetadata.METADATA_KEY_DURATION, (long) (dur * 1000));
        if (art != null) { mb.putBitmap(MediaMetadata.METADATA_KEY_ALBUM_ART, art); mb.putBitmap(MediaMetadata.METADATA_KEY_ART, art); }
        session.setMetadata(mb.build());
        session.setPlaybackState(new PlaybackState.Builder()
                .setActions(PlaybackState.ACTION_PLAY | PlaybackState.ACTION_PAUSE | PlaybackState.ACTION_PLAY_PAUSE
                        | PlaybackState.ACTION_SKIP_TO_NEXT | PlaybackState.ACTION_SKIP_TO_PREVIOUS | PlaybackState.ACTION_SEEK_TO)
                .setState(playing ? PlaybackState.STATE_PLAYING : PlaybackState.STATE_PAUSED, (long) (pos * 1000), playing ? rate : 0f)
                .build());
        session.setActive(true);

        Notification.Builder b = Build.VERSION.SDK_INT >= 26 ? new Notification.Builder(ctx, CH) : new Notification.Builder(ctx);
        PendingIntent open = PendingIntent.getActivity(ctx, 0,
                new Intent(ctx, MainActivity.class).addFlags(Intent.FLAG_ACTIVITY_SINGLE_TOP | Intent.FLAG_ACTIVITY_REORDER_TO_FRONT),
                PendingIntent.FLAG_IMMUTABLE);
        b.setSmallIcon(R.drawable.ic_stat_isai)
                .setContentTitle(title).setContentText(artist)
                .setContentIntent(open).setOngoing(playing).setOnlyAlertOnce(true).setShowWhen(false)
                .setVisibility(Notification.VISIBILITY_PUBLIC)
                .addAction(action(android.R.drawable.ic_media_previous, "Previous", A_PREV))
                .addAction(action(playing ? android.R.drawable.ic_media_pause : android.R.drawable.ic_media_play, playing ? "Pause" : "Play", A_PP))
                .addAction(action(android.R.drawable.ic_media_next, "Next", A_NEXT))
                .setStyle(new Notification.MediaStyle().setMediaSession(session.getSessionToken()).setShowActionsInCompactView(0, 1, 2));
        if (!album.isEmpty()) b.setSubText(album);
        if (art != null) b.setLargeIcon(art);
        nm.notify(NID, b.build());
    }

    void release() {
        try { artExec.shutdownNow(); } catch (Exception ignored) {}
        closeSave(true);
        try { ctx.unregisterReceiver(receiver); } catch (Exception ignored) {}
        if (wl != null && wl.isHeld()) wl.release();
        nm.cancel(NID);
        nm.cancel(DL_ID);
        session.release();
    }
}
