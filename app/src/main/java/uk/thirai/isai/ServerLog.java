package uk.thirai.isai;

import android.content.Context;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.text.SimpleDateFormat;
import java.util.ArrayDeque;
import java.util.Date;
import java.util.Locale;

/** In-memory ring buffer of backend log lines, mirrored to a file so a crash log survives a process restart. */
public final class ServerLog {
    private static final int MAX = 1500;
    private static final long MAX_FILE = 512 * 1024;
    private static final ArrayDeque<String> lines = new ArrayDeque<>();
    private static long seq = 0;                 // seq of the newest line; oldest buffered = seq - lines.size() + 1
    private static File file;
    private static final SimpleDateFormat TS = new SimpleDateFormat("HH:mm:ss", Locale.US);

    private ServerLog() {}

    public static synchronized void init(Context c) {
        if (file != null) return;
        file = new File(c.getFilesDir(), "server.log");
        try {
            if (file.exists() && file.length() > MAX_FILE) file.delete();
            if (file.exists()) {
                try (BufferedReader r = new BufferedReader(new FileReader(file))) {
                    String l;
                    while ((l = r.readLine()) != null) push(l);
                }
                push("---- app started ----");
            }
        } catch (Exception ignored) {}
    }

    private static void push(String l) {
        lines.addLast(l);
        seq++;
        while (lines.size() > MAX) lines.removeFirst();
    }

    /** Called from Python (stdout/stderr/logging) and from Java. Multi-line text is split. */
    public static synchronized void append(String text) {
        if (text == null) return;
        String ts = TS.format(new Date());
        for (String part : text.split("\\r?\\n")) {
            if (part.trim().isEmpty()) continue;
            String l = ts + "  " + part;
            push(l);
            if (file != null) {
                try (FileWriter w = new FileWriter(file, true)) { w.write(l + "\n"); } catch (Exception ignored) {}
            }
        }
    }

    /** {"seq":N,"state":"running","restarts":2,"lines":[...]} with the lines newer than `after`. */
    public static synchronized String since(long after) {
        try {
            JSONArray arr = new JSONArray();
            long first = seq - lines.size() + 1;
            long i = first;
            for (String l : lines) { if (i > after) arr.put(l); i++; }
            return new JSONObject().put("seq", seq).put("state", ServerService.state)
                    .put("restarts", ServerService.restarts).put("lines", arr).toString();
        } catch (Exception e) {
            return "{\"seq\":" + seq + ",\"state\":\"unknown\",\"lines\":[]}";
        }
    }
}
