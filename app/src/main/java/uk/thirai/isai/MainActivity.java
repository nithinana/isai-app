package uk.thirai.isai;

import android.Manifest;
import android.app.Activity;
import android.content.Context;
import android.content.Intent;
import android.graphics.Color;
import android.net.ConnectivityManager;
import android.net.Network;
import android.net.NetworkCapabilities;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.view.Gravity;
import android.webkit.WebResourceError;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.FrameLayout;
import android.widget.ImageView;

import androidx.webkit.WebViewAssetLoader;

import org.json.JSONObject;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.net.HttpURLConnection;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.net.URL;

public class MainActivity extends Activity {
    /** The live site. Same page for browser and app; it picks its own API (see isai_patch_index.py). */
    private static final String HOST = "isai.thirai.uk";
    private static final String ROOT = "https://" + HOST + "/";
    private static final String LOCAL = "http://127.0.0.1:" + ServerService.PORT;

    private WebView web;
    private FrameLayout root;
    private FrameLayout splash;
    private MediaBridge media;
    private volatile boolean forceBundled = false;   // serve the bundled copy of the site (same origin)

    @Override
    protected void onCreate(Bundle state) {
        super.onCreate(state);
        android.util.Log.d("Isai", "MainActivity created, build 2.4 (live site)");

        if (Build.VERSION.SDK_INT >= 33) {
            requestPermissions(new String[]{Manifest.permission.POST_NOTIFICATIONS}, 1);
        }
        Intent svc = new Intent(this, ServerService.class);
        if (Build.VERSION.SDK_INT >= 26) startForegroundService(svc); else startService(svc);

        // Bundled copy of the site: only used when offline (or the site is down). Same host => same
        // origin, so localStorage / IndexedDB downloads / service worker are shared with the live site.
        final WebViewAssetLoader bundled = new WebViewAssetLoader.Builder()
                .setDomain(HOST)
                .addPathHandler("/", new WebViewAssetLoader.AssetsPathHandler(this))
                .build();

        root = new FrameLayout(this);
        root.setBackgroundColor(Color.parseColor("#0A0A0B"));
        web = new WebView(this);
        web.setBackgroundColor(Color.parseColor("#0A0A0B"));
        root.addView(web, new FrameLayout.LayoutParams(-1, -1));

        splash = new FrameLayout(this);
        splash.setBackgroundColor(Color.parseColor("#0A0A0B"));
        splash.setClickable(true);
        ImageView logo = new ImageView(this);
        logo.setImageResource(R.drawable.thirai_logo);
        logo.setAdjustViewBounds(true);
        int w = (int) (200 * getResources().getDisplayMetrics().density);
        splash.addView(logo, new FrameLayout.LayoutParams(w, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.CENTER));
        root.addView(splash, new FrameLayout.LayoutParams(-1, -1));
        setContentView(root);

        WebSettings s = web.getSettings();
        s.setJavaScriptEnabled(true);
        s.setDomStorageEnabled(true);
        s.setMediaPlaybackRequiresUserGesture(false);
        s.setAllowFileAccess(false);
        s.setMixedContentMode(WebSettings.MIXED_CONTENT_ALWAYS_ALLOW); // https site -> http://127.0.0.1 backend
        if (Build.VERSION.SDK_INT >= 26) web.setRendererPriorityPolicy(WebView.RENDERER_PRIORITY_IMPORTANT, false);

        media = new MediaBridge(this, web);
        web.addJavascriptInterface(media, "IsaiNative");

        web.setWebViewClient(new WebViewClient() {
            @Override
            public WebResourceResponse shouldInterceptRequest(WebView v, WebResourceRequest r) {
                Uri u = r.getUrl();
                if (HOST.equals(u.getHost()) && (forceBundled || !online())) {
                    String path = u.getPath();
                    if (path == null || path.isEmpty() || "/".equals(path)) u = u.buildUpon().path("/index.html").build();
                    return bundled.shouldInterceptRequest(u);   // null for files we don't bundle
                }
                return null;
            }

            @Override
            public boolean shouldOverrideUrlLoading(WebView v, WebResourceRequest r) {
                Uri u = r.getUrl();
                if (HOST.equals(u.getHost())) return false;
                try { startActivity(new Intent(Intent.ACTION_VIEW, u)); } catch (Exception ignored) {}
                return true;
            }

            @Override
            public void onReceivedError(WebView v, WebResourceRequest r, WebResourceError e) {
                if (r.isForMainFrame() && HOST.equals(r.getUrl().getHost()) && !forceBundled) {
                    forceBundled = true;            // site unreachable: fall back to the bundled copy once
                    v.loadUrl(ROOT);
                }
            }

            @Override
            public void onPageFinished(WebView v, String url) {
                if (url != null && url.startsWith("https://" + HOST)) hideSplash();
            }
        });

        if (state != null) { web.restoreState(state); return; }

        // Wait (max 25 s) for the on-device backend, tell the page about it, then load the site.
        // If it never comes up the page simply uses the public API.
        new Thread(() -> {
            long end = System.currentTimeMillis() + 25_000;
            boolean up = false;
            while (System.currentTimeMillis() < end && ServerService.lastError == null) {
                try (Socket sock = new Socket()) {
                    sock.connect(new InetSocketAddress("127.0.0.1", ServerService.PORT), 400);
                    up = true;
                    break;
                } catch (Exception e) {
                    try { Thread.sleep(300); } catch (InterruptedException ignored) {}
                }
            }
            String info = "";
            if (up) {
                int api = 0;
                try {
                    HttpURLConnection c = (HttpURLConnection) new URL(LOCAL + "/health").openConnection();
                    c.setConnectTimeout(2000); c.setReadTimeout(4000);
                    try (InputStream in = c.getInputStream()) {
                        ByteArrayOutputStream bo = new ByteArrayOutputStream();
                        byte[] buf = new byte[4096]; int n;
                        while ((n = in.read(buf)) > 0) bo.write(buf, 0, n);
                        api = new JSONObject(bo.toString("UTF-8")).optInt("api_version", 0);
                    }
                    c.disconnect();
                    info = new JSONObject().put("url", LOCAL).put("api", api).toString();
                } catch (Exception e) {
                    android.util.Log.d("Isai", "local /health failed: " + e);
                }
            }
            android.util.Log.d("Isai", "backendInfo=" + (info.isEmpty() ? "(none, using public API)" : info));
            media.setBackendInfo(info);
            runOnUiThread(() -> web.loadUrl(ROOT));
        }, "isai-wait").start();
    }

    private boolean online() {
        try {
            ConnectivityManager cm = (ConnectivityManager) getSystemService(Context.CONNECTIVITY_SERVICE);
            Network n = cm.getActiveNetwork();
            NetworkCapabilities c = n == null ? null : cm.getNetworkCapabilities(n);
            return c != null && c.hasCapability(NetworkCapabilities.NET_CAPABILITY_INTERNET);
        } catch (Exception e) {
            return true;
        }
    }

    private void hideSplash() {
        if (splash == null) return;
        final FrameLayout sp = splash;
        splash = null;
        sp.animate().alpha(0f).setDuration(250).withEndAction(() -> root.removeView(sp));
    }

    @Override protected void onSaveInstanceState(Bundle out) { super.onSaveInstanceState(out); web.saveState(out); }

    @Override
    public void onBackPressed() {
        if (web.canGoBack()) web.goBack(); else super.onBackPressed();
    }

    @Override
    protected void onDestroy() {
        if (media != null) media.release();
        if (isFinishing()) stopService(new Intent(this, ServerService.class));
        super.onDestroy();
    }
}
