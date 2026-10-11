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

/** Keeps the on-device Python backend alive (also while the app is in the background). */
public class ServerService extends Service {
    public static final int PORT = 8765;
    private static boolean started = false;
    public static volatile String lastError = null;

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

        synchronized (ServerService.class) {
            if (!started) {
                started = true;
                new Thread(() -> {
                    try {
                        Python.getInstance().getModule("isai_launcher").callAttr("start", PORT);
                    } catch (Throwable t) {
                        android.util.Log.e("Isai", "backend crashed", t);
                        lastError = android.util.Log.getStackTraceString(t);
                        synchronized (ServerService.class) { started = false; }
                    }
                }, "isai-server").start();
            }
        }
        return START_STICKY;
    }

    @Override public IBinder onBind(Intent intent) { return null; }
}
