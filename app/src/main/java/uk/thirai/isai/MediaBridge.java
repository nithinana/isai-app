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
import android.os.Build;
import android.os.Handler;
import android.os.Looper;
import android.os.PowerManager;
import android.webkit.JavascriptInterface;
import android.webkit.WebView;

import org.json.JSONObject;

import java.net.HttpURLConnection;
import java.net.URL;

/** Mirrors the page's Media Session (title, artist, cover, play state) into a system media notification. */
public class MediaBridge {
    private static final String CH = "isai_media";
    private static final int NID = 2;
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
    private PowerManager.WakeLock wl;

    MediaBridge(Activity a, WebView w) {
        ctx = a;
        web = w;
        nm = a.getSystemService(NotificationManager.class);
        if (Build.VERSION.SDK_INT >= 26) {
            nm.createNotificationChannel(new NotificationChannel(CH, "Now playing", NotificationManager.IMPORTANCE_LOW));
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
                    au = o.optString("art"), s = o.optString("state", "none");
            final double d = o.optDouble("dur", 0), p = o.optDouble("pos", 0);
            final float r = (float) o.optDouble("rate", 1);
            main.post(() -> apply(t, ar, al, au, s, d, p, r));
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

    private void apply(String t, String ar, String al, String au, String s, double d, double p, float r) {
        boolean changed = !t.equals(title) || !ar.equals(artist) || !al.equals(album) || !s.equals(state)
                || Math.abs(d - dur) > 0.5 || r != rate;
        long now = System.currentTimeMillis();
        double expected = pos + ("playing".equals(state) ? (now - posWall) / 1000.0 * rate : 0);
        if (Math.abs(p - expected) > 1.5) changed = true;   // seek / skip
        title = t; artist = ar; album = al; state = s; dur = d; pos = p; rate = r; posWall = now;
        if (!au.equals(artUrl)) {
            artUrl = au; art = null; changed = true;
            fetchArt(au);
        }
        if (changed) publish();
    }

    private void fetchArt(final String url) {
        if (url.isEmpty()) return;
        new Thread(() -> {
            try {
                HttpURLConnection c = (HttpURLConnection) new URL(url).openConnection();
                c.setConnectTimeout(8000); c.setReadTimeout(8000);
                Bitmap b = BitmapFactory.decodeStream(c.getInputStream());
                c.disconnect();
                if (b != null) main.post(() -> { if (url.equals(artUrl)) { art = b; publish(); } });
            } catch (Exception ignored) {}
        }, "isai-art").start();
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
        if (art != null) mb.putBitmap(MediaMetadata.METADATA_KEY_ALBUM_ART, art);
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
        b.setSmallIcon(android.R.drawable.ic_media_play)
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
        try { ctx.unregisterReceiver(receiver); } catch (Exception ignored) {}
        if (wl != null && wl.isHeld()) wl.release();
        nm.cancel(NID);
        session.release();
    }
}
