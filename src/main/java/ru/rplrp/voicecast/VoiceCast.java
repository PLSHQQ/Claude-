package ru.rplrp.voicecast;

import de.maxhenkel.voicechat.api.BukkitVoicechatService;
import de.maxhenkel.voicechat.api.VoicechatApi;
import de.maxhenkel.voicechat.api.VoicechatConnection;
import de.maxhenkel.voicechat.api.VoicechatPlugin;
import de.maxhenkel.voicechat.api.VoicechatServerApi;
import de.maxhenkel.voicechat.api.audiochannel.AudioPlayer;
import de.maxhenkel.voicechat.api.audiochannel.LocationalAudioChannel;
import de.maxhenkel.voicechat.api.events.EventRegistration;
import de.maxhenkel.voicechat.api.events.MicrophonePacketEvent;
import de.maxhenkel.voicechat.api.events.VoicechatServerStartedEvent;
import de.maxhenkel.voicechat.api.opus.OpusDecoder;
import org.bukkit.Bukkit;
import org.bukkit.ChatColor;
import org.bukkit.Location;
import org.bukkit.World;
import org.bukkit.command.Command;
import org.bukkit.command.CommandSender;
import org.bukkit.entity.LivingEntity;
import org.bukkit.entity.Player;
import org.bukkit.event.EventHandler;
import org.bukkit.event.Listener;
import org.bukkit.event.player.PlayerQuitEvent;
import org.bukkit.inventory.ItemStack;
import org.bukkit.inventory.meta.ItemMeta;
import org.bukkit.plugin.java.JavaPlugin;
import org.vosk.LibVosk;
import org.vosk.LogLevel;
import org.vosk.Model;
import org.vosk.Recognizer;

import java.io.File;
import java.io.InputStream;
import java.net.URI;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

public final class VoiceCast extends JavaPlugin implements VoicechatPlugin, Listener {

    private static final Pattern TEXT = Pattern.compile("\"text\"\\s*:\\s*\"([^\"]*)\"");

    private record Phrase(String phrase, String say, String requireItem, long cooldownMs, List<String> commands) {}

    private static final class Session {
        OpusDecoder decoder;
        Recognizer rec;
        volatile long last;
        volatile boolean speaking;
        long started;
    }

    private final Map<UUID, Session> sessions = new ConcurrentHashMap<>();
    private final Set<UUID> off = ConcurrentHashMap.newKeySet();
    private final Map<String, Long> cooldowns = new ConcurrentHashMap<>();
    private final Map<String, short[]> voices = new ConcurrentHashMap<>();
    private final ExecutorService worker = Executors.newSingleThreadExecutor(r -> {
        Thread t = new Thread(r, "VoiceCast-recognizer");
        t.setDaemon(true);
        return t;
    });
    private volatile List<Phrase> phrases = List.of();
    private volatile String grammar = "[]";
    private volatile Model model;
    private volatile VoicechatServerApi api;
    private int maxListeners = 4;
    private long silenceMs = 450;

    @Override
    public void onEnable() {
        saveDefaultConfig();
        loadPhrases();
        new File(getDataFolder(), "voices").mkdirs();
        BukkitVoicechatService service = getServer().getServicesManager().load(BukkitVoicechatService.class);
        if (service == null) {
            getLogger().severe("Simple Voice Chat не найден, плагин выключен.");
            getServer().getPluginManager().disablePlugin(this);
            return;
        }
        service.registerPlugin(this);
        getServer().getPluginManager().registerEvents(this, this);
        Bukkit.getScheduler().runTaskAsynchronously(this, this::loadModel);
        // конец фразы по паузе
        Bukkit.getScheduler().runTaskTimerAsynchronously(this, () -> {
            long now = System.currentTimeMillis();
            for (Map.Entry<UUID, Session> e : sessions.entrySet()) {
                Session s = e.getValue();
                if (s.speaking && (now - s.last > silenceMs || now - s.started > 6000)) {
                    UUID id = e.getKey();
                    worker.submit(() -> finish(id));
                }
            }
        }, 20L, 4L);
        // голос боссов: датапак вешает на босса тег bv_<файл>, плагин проигрывает voices/<файл>.wav
        Bukkit.getScheduler().runTaskTimer(this, this::scanBossVoices, 40L, 5L);
    }

    @Override
    public void onDisable() {
        worker.shutdownNow();
        for (Session s : sessions.values()) closeSession(s);
        sessions.clear();
        Model m = model;
        if (m != null) m.close();
    }

    private void loadPhrases() {
        reloadConfig();
        maxListeners = getConfig().getInt("max-listeners", 4);
        silenceMs = getConfig().getLong("silence-ms", 450);
        List<Phrase> list = new ArrayList<>();
        StringBuilder g = new StringBuilder("[");
        for (Map<?, ?> m : getConfig().getMapList("phrases")) {
            Object p = m.get("phrase");
            if (p == null) continue;
            String phrase = norm(p.toString());
            String say = m.get("say") == null ? null : m.get("say").toString();
            String req = m.get("require-item") == null ? null : m.get("require-item").toString();
            long cd = m.get("cooldown") instanceof Number n ? (long) (n.doubleValue() * 1000) : 3000;
            List<String> cmds = new ArrayList<>();
            if (m.get("commands") instanceof List<?> l) for (Object o : l) cmds.add(o.toString());
            list.add(new Phrase(phrase, say, req, cd, cmds));
            g.append('"').append(phrase.replace("\"", "")).append("\",");
        }
        g.append("\"[unk]\"]");
        phrases = list;
        grammar = g.toString();
        voices.clear();
    }

    private static String norm(String s) {
        return s.toLowerCase().replace('ё', 'е').replaceAll("[^a-zа-я0-9 ]", " ").replaceAll("\\s+", " ").trim();
    }

    private void loadModel() {
        try {
            File dir = new File(getDataFolder(), getConfig().getString("model-dir", "model"));
            if (!new File(dir, "am").exists() && getConfig().getBoolean("auto-download-model", true)) {
                getLogger().info("Скачиваю модель распознавания речи...");
                download(getConfig().getString("model-url"), dir.toPath());
            }
            if (!new File(dir, "am").exists()) {
                getLogger().severe("Модель не найдена в " + dir + ". Распознавание выключено.");
                return;
            }
            LibVosk.setLogLevel(LogLevel.WARNINGS);
            model = new Model(dir.getAbsolutePath());
            getLogger().info("Модель загружена, фраз: " + phrases.size());
        } catch (Throwable t) {
            getLogger().severe("Не удалось загрузить модель: " + t);
        }
    }

    private void download(String url, Path dir) throws Exception {
        Files.createDirectories(dir);
        Path root = dir.toAbsolutePath().normalize();
        try (InputStream in = URI.create(url).toURL().openStream(); ZipInputStream zip = new ZipInputStream(in)) {
            ZipEntry e;
            while ((e = zip.getNextEntry()) != null) {
                String name = e.getName();
                int slash = name.indexOf('/');
                if (slash < 0 || slash == name.length() - 1) continue; // убираем верхнюю папку архива
                Path out = root.resolve(name.substring(slash + 1)).normalize();
                if (!out.startsWith(root)) continue;
                if (e.isDirectory()) Files.createDirectories(out);
                else {
                    Files.createDirectories(out.getParent());
                    Files.copy(zip, out, StandardCopyOption.REPLACE_EXISTING);
                }
            }
        }
    }

    // ---------- Simple Voice Chat ----------

    @Override
    public String getPluginId() {
        return "voicecast";
    }

    @Override
    public void initialize(VoicechatApi a) {
    }

    @Override
    public void registerEvents(EventRegistration reg) {
        reg.registerEvent(VoicechatServerStartedEvent.class, e -> api = e.getVoicechat());
        reg.registerEvent(MicrophonePacketEvent.class, this::onMic);
    }

    private void onMic(MicrophonePacketEvent e) {
        VoicechatConnection con = e.getSenderConnection();
        if (con == null || model == null) return;
        UUID id = con.getPlayer().getUuid();
        if (off.contains(id)) return;
        byte[] opus = e.getPacket().getOpusEncodedData();
        if (opus == null) return;
        byte[] copy = opus.clone();
        VoicechatServerApi a = e.getVoicechat();
        worker.submit(() -> feed(a, id, copy));
    }

    private void feed(VoicechatServerApi a, UUID id, byte[] opus) {
        try {
            Session s = sessions.get(id);
            if (s == null) {
                if (sessions.size() >= maxListeners) return;
                s = new Session();
                s.decoder = a.createDecoder();
                s.rec = new Recognizer(model, 16000f, grammar);
                sessions.put(id, s);
            }
            if (opus.length == 0) {
                if (s.speaking) finish(id);
                return;
            }
            short[] pcm = s.decoder.decode(opus);
            if (pcm == null || pcm.length == 0) return;
            // 48 кГц -> 16 кГц
            int n = pcm.length / 3;
            ByteBuffer buf = ByteBuffer.allocate(n * 2).order(ByteOrder.LITTLE_ENDIAN);
            for (int i = 0; i < n; i++) buf.putShort((short) ((pcm[i * 3] + pcm[i * 3 + 1] + pcm[i * 3 + 2]) / 3));
            if (!s.speaking) {
                s.speaking = true;
                s.started = System.currentTimeMillis();
            }
            s.last = System.currentTimeMillis();
            s.rec.acceptWaveForm(buf.array(), n * 2);
        } catch (Throwable t) {
            getLogger().warning("Ошибка распознавания: " + t);
        }
    }

    private void finish(UUID id) {
        Session s = sessions.get(id);
        if (s == null || !s.speaking) return;
        s.speaking = false;
        String text;
        try {
            Matcher m = TEXT.matcher(s.rec.getFinalResult());
            text = m.find() ? norm(m.group(1)) : "";
            s.rec.reset();
        } catch (Throwable t) {
            return;
        }
        if (text.isEmpty()) return;
        Phrase best = null;
        for (Phrase p : phrases)
            if ((" " + text + " ").contains(" " + p.phrase + " ") && (best == null || p.phrase.length() > best.phrase.length())) best = p;
        if (best == null) return;
        Phrase hit = best;
        Bukkit.getScheduler().runTask(this, () -> fire(id, hit));
    }

    private void fire(UUID id, Phrase p) {
        Player pl = Bukkit.getPlayer(id);
        if (pl == null || !pl.hasPermission("voicecast.use")) return;
        String key = id + "|" + p.phrase;
        long now = System.currentTimeMillis();
        Long until = cooldowns.get(key);
        if (until != null && until > now) return;
        if (p.requireItem != null && !hasItem(pl, p.requireItem)) return;
        cooldowns.put(key, now + p.cooldownMs);
        pl.sendActionBar(ChatColor.GOLD + "Голос: " + p.phrase);
        if (!p.commands.isEmpty()) {
            for (String c : p.commands) Bukkit.dispatchCommand(Bukkit.getConsoleSender(), c.replace("%player%", pl.getName()));
        } else {
            pl.chat(p.say != null ? p.say : p.phrase);
        }
    }

    private static boolean hasItem(Player pl, String name) {
        String want = norm(name);
        for (ItemStack it : pl.getInventory().getContents()) {
            if (it == null || !it.hasItemMeta()) continue;
            ItemMeta meta = it.getItemMeta();
            String n = meta.hasItemName() ? meta.getItemName() : meta.hasDisplayName() ? meta.getDisplayName() : null;
            if (n != null && norm(ChatColor.stripColor(n)).equals(want)) return true;
        }
        return false;
    }

    private static void closeSession(Session s) {
        try {
            if (s.rec != null) s.rec.close();
            if (s.decoder != null) s.decoder.close();
        } catch (Throwable ignored) {
        }
    }

    @EventHandler
    public void onQuit(PlayerQuitEvent e) {
        UUID id = e.getPlayer().getUniqueId();
        worker.submit(() -> {
            Session s = sessions.remove(id);
            if (s != null) closeSession(s);
        });
    }

    // ---------- голос боссов ----------

    private void scanBossVoices() {
        if (api == null) return;
        for (World w : Bukkit.getWorlds()) {
            for (LivingEntity en : w.getLivingEntities()) {
                Set<String> tags = en.getScoreboardTags();
                if (tags.isEmpty()) continue;
                for (String tag : List.copyOf(tags)) {
                    if (!tag.startsWith("bv_")) continue;
                    en.removeScoreboardTag(tag);
                    play(tag.substring(3), en.getLocation().add(0, 1.5, 0));
                }
            }
        }
    }

    private boolean play(String name, Location loc) {
        VoicechatServerApi a = api;
        if (a == null || !name.matches("[a-z0-9_]+")) return false;
        short[] pcm = voices.computeIfAbsent(name, this::loadWav);
        if (pcm.length == 0) return false;
        LocationalAudioChannel ch = a.createLocationalAudioChannel(UUID.randomUUID(), a.fromServerLevel(loc.getWorld()), a.createPosition(loc.getX(), loc.getY(), loc.getZ()));
        if (ch == null) return false;
        AudioPlayer player = a.createAudioPlayer(ch, a.createEncoder(), pcm);
        player.startPlaying();
        return true;
    }

    /** Читает WAV (PCM 16 бит, любое число каналов и частота) и приводит к 48 кГц моно. */
    private short[] loadWav(String name) {
        try {
            byte[] b = Files.readAllBytes(new File(getDataFolder(), "voices/" + name + ".wav").toPath());
            ByteBuffer buf = ByteBuffer.wrap(b).order(ByteOrder.LITTLE_ENDIAN);
            int channels = 1, rate = 48000, bits = 16, dataPos = -1, dataLen = 0, pos = 12;
            while (pos + 8 <= b.length) {
                String id = new String(b, pos, 4, java.nio.charset.StandardCharsets.US_ASCII);
                int len = buf.getInt(pos + 4);
                if (id.equals("fmt ")) {
                    channels = buf.getShort(pos + 10);
                    rate = buf.getInt(pos + 12);
                    bits = buf.getShort(pos + 22);
                } else if (id.equals("data")) {
                    dataPos = pos + 8;
                    dataLen = Math.min(len, b.length - dataPos);
                    break;
                }
                pos += 8 + len + (len & 1);
            }
            if (dataPos < 0 || bits != 16 || channels < 1) {
                getLogger().warning("Файл " + name + ".wav должен быть PCM 16 бит.");
                return new short[0];
            }
            int frames = dataLen / (2 * channels);
            short[] mono = new short[frames];
            for (int i = 0; i < frames; i++) {
                int sum = 0;
                for (int c = 0; c < channels; c++) sum += buf.getShort(dataPos + (i * channels + c) * 2);
                mono[i] = (short) (sum / channels);
            }
            if (rate == 48000) return mono;
            int outLen = (int) ((long) frames * 48000 / rate);
            short[] out = new short[outLen];
            for (int i = 0; i < outLen; i++) {
                double src = (double) i * rate / 48000;
                int i0 = (int) src, i1 = Math.min(i0 + 1, frames - 1);
                double f = src - i0;
                out[i] = (short) (mono[i0] * (1 - f) + mono[i1] * f);
            }
            return out;
        } catch (Exception e) {
            getLogger().warning("Нет звука voices/" + name + ".wav");
            return new short[0];
        }
    }

    // ---------- команда ----------

    @Override
    public boolean onCommand(CommandSender sender, Command cmd, String label, String[] args) {
        if (args.length == 0) return false;
        switch (args[0].toLowerCase()) {
            case "on", "off" -> {
                if (!(sender instanceof Player pl)) return true;
                if (args[0].equalsIgnoreCase("on")) off.remove(pl.getUniqueId());
                else off.add(pl.getUniqueId());
                sender.sendMessage(ChatColor.GREEN + "Голосовые способности: " + (args[0].equalsIgnoreCase("on") ? "включены" : "выключены"));
            }
            case "reload" -> {
                if (!sender.hasPermission("voicecast.admin")) return true;
                loadPhrases();
                worker.submit(() -> {
                    for (Session s : sessions.values()) closeSession(s);
                    sessions.clear();
                });
                sender.sendMessage(ChatColor.GREEN + "Перезагружено, фраз: " + phrases.size());
            }
            case "play" -> {
                if (!sender.hasPermission("voicecast.admin") || !(sender instanceof Player pl) || args.length < 2) return true;
                sender.sendMessage(play(args[1].toLowerCase(), pl.getLocation()) ? ChatColor.GREEN + "Играю " + args[1] : ChatColor.RED + "Не удалось проиграть " + args[1]);
            }
            default -> {
                return false;
            }
        }
        return true;
    }
}
