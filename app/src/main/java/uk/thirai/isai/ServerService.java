package uk.thirai.isai;

import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.Service;
import android.content.Intent;
import android.content.pm.ServiceInfo;
import android.os.Build;
import android.os.IBinder;

import com.chaquo.python.Python;

import java.net.HttpURLConnection;
import java.net.URL;

/**
 * Keeps the on-device Python backend alive (also while the app is in the background), and
 * restarts it if it exits, crashes or stops answering.
 */
public class ServerService extends Service {
    public static final int PORT = 8765;
    public static volatile String lastError = null;
    /** starting | running | unresponsive | restarting | stopped */
    public static volatile String state = "stopped";
    public static volatile int restarts = 0;

    private static final long CHECK_MS = 8_000;
    private static final long GRACE_MS = 30_000;     // backend import + startup can be slow on a phone
    private static final int MAX_FAILS = 3;

    private static final Object lock = new Object();
    private static Thread serverThread;
    private static Thread watchdog;
    private static volatile boolean wanted = false;
    private static volatile long launchedAt = 0;
    private static volatile boolean busy = false;     // a (re)start is in progress

    @Override
    public int onStartCommand(Intent intent, int flags, int startId) {
        String channel = "isai";
        if (Build.VERSION.SDK_INT >= 26) {
            NotificationManager nm = getSystemService(NotificationManager.class);
            nm.createNotificationChannel(new NotificationChannel(channel, "Isai", NotificationManager.IMPORTANCE_LOW));
        }
        Notification.Builder b = Build.VERSION.SDK_INT >= 26 ? new Notification.Builder(this, channel) : new Notification.Builder(this);
        Notification n = b.setContentTitle("Isai").setContentText("Backend running in the background")
                .setSmallIcon(R.drawable.ic_stat_isai).setOngoing(true).build();
        if (Build.VERSION.SDK_INT >= 29) startForeground(1, n, ServiceInfo.FOREGROUND_SERVICE_TYPE_MEDIA_PLAYBACK);
        else startForeground(1, n);

        ServerLog.init(getApplicationContext());
        synchronized (lock) {
            wanted = true;
            if (serverThread == null || !serverThread.isAlive()) launch();
            if (watchdog == null || !watchdog.isAlive()) {
                watchdog = new Thread(ServerService::watch, "isai-watchdog");
                watchdog.setDaemon(true);
                watchdog.start();
            }
        }
        return START_STICKY;
    }

    @Override public IBinder onBind(Intent intent) { return null; }

    @Override
    public void onDestroy() {
        wanted = false;
        state = "stopped";
        ServerLog.append("[app] service destroyed, stopping backend");
        stopPython();
        super.onDestroy();
    }

    // ---------------------------------------------------------------- control

    /** Starts the Python server on a fresh thread. Caller holds `lock` or is the only starter. */
    private static void launch() {
        lastError = null;
        launchedAt = System.currentTimeMillis();
        state = "starting";
        ServerLog.append("[app] starting backend on 127.0.0.1:" + PORT);
        Thread t = new Thread(() -> {
            try {
                Python.getInstance().getModule("isai_launcher").callAttr("start", PORT);
                ServerLog.append("[app] backend exited");
            } catch (Throwable th) {
                android.util.Log.e("Isai", "backend crashed", th);
                lastError = android.util.Log.getStackTraceString(th);
                ServerLog.append("[app] backend crashed:\n" + lastError);
            }
        }, "isai-server");
        serverThread = t;
        t.start();
    }

    private static void stopPython() {
        try { Python.getInstance().getModule("isai_launcher").callAttr("stop"); } catch (Throwable ignored) {}
    }

    /** Stop the current server (if any) and start a new one. Safe to call from any thread except the UI thread's critical path. */
    public static void restart(String reason) {
        synchronized (lock) {
            if (busy || !wanted) return;
            busy = true;
        }
        try {
            restarts++;
            state = "restarting";
            ServerLog.append("[app] restarting backend: " + reason);
            stopPython();
            Thread old = serverThread;
            if (old != null) {
                try { old.join(8_000); } catch (InterruptedException ignored) {}
                if (old.isAlive()) ServerLog.append("[app] old backend is still shutting down; starting anyway");
            }
            synchronized (lock) { if (wanted) launch(); }
        } finally {
            busy = false;
        }
    }

    /** From the in-app log screen. Runs off the calling thread. */
    public static void requestRestart(String reason) {
        new Thread(() -> restart(reason), "isai-restart").start();
    }

    // ---------------------------------------------------------------- watchdog

    private static boolean ping() {
        HttpURLConnection c = null;
        try {
            c = (HttpURLConnection) new URL("http://127.0.0.1:" + PORT + "/__isai_ping").openConnection();
            c.setConnectTimeout(2_000);
            c.setReadTimeout(4_000);
            return c.getResponseCode() == 200;
        } catch (Exception e) {
            return false;
        } finally {
            if (c != null) c.disconnect();
        }
    }

    private static void watch() {
        int fails = 0, crashes = 0;
        long okSince = 0;
        while (wanted) {
            try { Thread.sleep(CHECK_MS); } catch (InterruptedException e) { return; }
            if (!wanted) return;
            if (busy) { fails = 0; continue; }

            boolean exited = serverThread == null || !serverThread.isAlive();
            if (exited) {
                // Crashed or exited: restart with a growing delay (5 s, 10 s, ... max 60 s) so a hard bug can't spin.
                long wait = Math.min(60_000, 5_000L << Math.min(crashes, 4));
                crashes++;
                ServerLog.append("[app] backend is not running; restarting in " + (wait / 1000) + " s");
                state = "restarting";
                try { Thread.sleep(wait); } catch (InterruptedException e) { return; }
                restart("backend process exited");
                fails = 0;
                okSince = 0;
                continue;
            }

            if (ping()) {
                if (!"running".equals(state)) ServerLog.append("[app] backend is up");
                state = "running";
                fails = 0;
                if (okSince == 0) okSince = System.currentTimeMillis();
                if (System.currentTimeMillis() - okSince > 120_000) crashes = 0;   // stable: reset back-off
                continue;
            }

            okSince = 0;
            if (System.currentTimeMillis() - launchedAt < GRACE_MS) continue;     // still starting up
            fails++;
            state = "unresponsive";
            ServerLog.append("[app] backend not answering (" + fails + "/" + MAX_FAILS + ")");
            if (fails >= MAX_FAILS) {
                restart("backend stopped answering");
                fails = 0;
            }
        }
    }
}
