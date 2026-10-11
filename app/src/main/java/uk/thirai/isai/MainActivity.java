package uk.thirai.isai;

import android.Manifest;
import android.app.Activity;
import android.content.Intent;
import android.graphics.Color;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;

import androidx.webkit.WebViewAssetLoader;

import java.net.InetSocketAddress;
import java.net.Socket;

public class MainActivity extends Activity {
    // UI origin ends in .thirai.uk so both your API's and the account server's CORS accept it.
    private static final String HOST = "apk.thirai.uk";
    private WebView web;

    @Override
    protected void onCreate(Bundle state) {
        super.onCreate(state);

        if (Build.VERSION.SDK_INT >= 33) {
            requestPermissions(new String[]{Manifest.permission.POST_NOTIFICATIONS}, 1);
        }
        Intent svc = new Intent(this, ServerService.class);
        if (Build.VERSION.SDK_INT >= 26) startForegroundService(svc); else startService(svc);

        final WebViewAssetLoader loader = new WebViewAssetLoader.Builder()
                .setDomain(HOST)
                .addPathHandler("/", new WebViewAssetLoader.AssetsPathHandler(this))
                .build();

        web = new WebView(this);
        web.setBackgroundColor(Color.parseColor("#0A0A0B"));
        setContentView(web);

        WebSettings s = web.getSettings();
        s.setJavaScriptEnabled(true);
        s.setDomStorageEnabled(true);
        s.setMediaPlaybackRequiresUserGesture(false);
        s.setAllowFileAccess(false);
        s.setMixedContentMode(WebSettings.MIXED_CONTENT_ALWAYS_ALLOW); // https UI -> http://127.0.0.1 backend

        web.setWebViewClient(new WebViewClient() {
            @Override
            public WebResourceResponse shouldInterceptRequest(WebView v, WebResourceRequest r) {
                return loader.shouldInterceptRequest(r.getUrl());
            }

            @Override
            public boolean shouldOverrideUrlLoading(WebView v, WebResourceRequest r) {
                Uri u = r.getUrl();
                if (HOST.equals(u.getHost())) return false;
                try { startActivity(new Intent(Intent.ACTION_VIEW, u)); } catch (Exception ignored) {}
                return true;
            }
        });

        if (state != null) { web.restoreState(state); return; }

        web.loadDataWithBaseURL(null, page("Starting music engine\u2026", ""), "text/html", "utf-8", null);

        // Poll for the Python backend; show its error instead of a blank screen if it fails.
        new Thread(() -> {
            long end = System.currentTimeMillis() + 90_000;
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
            final boolean ok = up;
            runOnUiThread(() -> {
                if (ok) web.loadUrl("https://" + HOST + "/index.html");
                else {
                    String err = ServerService.lastError != null ? ServerService.lastError : "Timed out waiting for the backend (90 s).";
                    web.loadDataWithBaseURL(null, page("Backend failed to start", err), "text/html", "utf-8", null);
                }
            });
        }, "isai-wait").start();
    }

    private static String page(String title, String detail) {
        return "<html><body style='background:#0a0a0b;color:#f4f4f7;font-family:sans-serif;padding:24px'>"
                + "<h2>" + android.text.TextUtils.htmlEncode(title) + "</h2>"
                + "<pre style='white-space:pre-wrap;font-size:11px;color:#a3a3b0'>" + android.text.TextUtils.htmlEncode(detail) + "</pre></body></html>";
    }

    @Override protected void onSaveInstanceState(Bundle out) { super.onSaveInstanceState(out); web.saveState(out); }

    @Override
    public void onBackPressed() {
        if (web.canGoBack()) web.goBack(); else super.onBackPressed();
    }
}
