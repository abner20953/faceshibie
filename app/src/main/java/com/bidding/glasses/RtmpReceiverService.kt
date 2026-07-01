package com.bidding.glasses

import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.content.Context
import android.content.Intent
import android.os.Build
import android.os.IBinder
import android.os.PowerManager
import android.net.wifi.WifiManager
import androidx.core.app.NotificationCompat

class RtmpReceiverService : Service() {

    private var receiver: EmbeddedRtmpReceiver? = null
    private var previewDecoder: RtmpAvcPreviewDecoder? = null
    private var wakeLock: PowerManager.WakeLock? = null
    private var wifiLock: WifiManager.WifiLock? = null
    private var receiverStartedAtMs = 0L
    private var lastVideoTagAtMs = 0L
    private var lastPreviewFrameAtMs = 0L
    private var lastPreviewCacheAtMs = 0L
    private var lastPreviewWatchdogResetAtMs = 0L
    private var lastNotificationUpdateAtMs = 0L
    private var lastNotificationStateKey = ""
    private var firstVideoTagAtMs = 0L

    override fun onCreate() {
        super.onCreate()
        ensureNotificationChannel()
    }

    override fun onBind(intent: Intent?): IBinder? = null

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        when (intent?.action) {
            ACTION_START -> {
                val port = intent.getIntExtra(EXTRA_PORT, DEFAULT_PORT)
                val streamKey = intent.getStringExtra(EXTRA_STREAM_KEY).orEmpty().ifBlank { DEFAULT_STREAM_KEY }
                startForeground(NOTIFICATION_ID, buildNotification("等待眼镜推流", port, streamKey))
                startReceiver(port, streamKey)
            }
            ACTION_RESET_PREVIEW -> {
                val reason = intent.getStringExtra(EXTRA_REASON).orEmpty().ifBlank { "external_reset" }
                val snapshot = latestSnapshot
                if (snapshot.running) {
                    startForeground(
                        NOTIFICATION_ID,
                        buildNotification(snapshot.message, snapshot.port, snapshot.expectedStreamKey)
                    )
                    if (snapshot.clientConnected) {
                        resetPreviewDecoder(reason)
                    } else {
                        broadcastLog("预览解码器外部复位跳过: reason=$reason, clientConnected=false", null)
                    }
                }
            }
            ACTION_STOP -> {
                stopReceiver(intent.getStringExtra(EXTRA_REASON).orEmpty().ifBlank { "stop" })
                stopForeground(STOP_FOREGROUND_REMOVE)
                stopSelf()
            }
        }
        return START_STICKY
    }

    override fun onDestroy() {
        stopReceiver("service destroyed")
        super.onDestroy()
    }

    private fun startReceiver(port: Int, streamKey: String) {
        val current = receiver?.currentSnapshot()
        if (current?.running == true) {
            acquireStreamingLocks("receiver_already_running")
            updateNotification(current)
            return
        }
        latestSnapshot = EmbeddedRtmpReceiver.Snapshot(
            running = true,
            listening = false,
            port = port,
            expectedStreamKey = streamKey,
            message = "正在启动 RTMP 接收服务..."
        )
        acquireStreamingLocks("start_receiver")
        latestPreviewFrame = null
        receiverStartedAtMs = System.currentTimeMillis()
        lastVideoTagAtMs = 0L
        firstVideoTagAtMs = 0L
        lastPreviewFrameAtMs = 0L
        lastPreviewCacheAtMs = 0L
        lastPreviewWatchdogResetAtMs = 0L
        lastNotificationUpdateAtMs = 0L
        lastNotificationStateKey = ""
        broadcastSnapshot(latestSnapshot)
        previewDecoder?.release()
        previewDecoder = RtmpAvcPreviewDecoder(
            callback = object : RtmpAvcPreviewDecoder.Callback {
                override fun onPreviewFrame(jpegBytes: ByteArray, width: Int, height: Int, decodedFrames: Long) {
                    lastPreviewFrameAtMs = System.currentTimeMillis()
                    broadcastPreview(jpegBytes, width, height, decodedFrames)
                }

                override fun onDecoderLog(message: String, throwable: Throwable?) {
                    broadcastLog("预览解码: $message", throwable)
                }
            }
        )
        receiver = EmbeddedRtmpReceiver(
            port = port,
            expectedStreamKey = streamKey,
            callback = object : EmbeddedRtmpReceiver.Callback {
                override fun onSnapshot(snapshot: EmbeddedRtmpReceiver.Snapshot) {
                    latestSnapshot = snapshot
                    broadcastSnapshot(snapshot)
                    updateNotification(snapshot)
                }

                override fun onLog(message: String, throwable: Throwable?) {
                    broadcastLog(message, throwable)
                }

                override fun onVideoTag(payload: ByteArray, timestampMs: Int) {
                    val now = System.currentTimeMillis()
                    lastVideoTagAtMs = now
                    if (firstVideoTagAtMs <= 0L) {
                        firstVideoTagAtMs = now
                    }
                    previewDecoder?.onVideoTag(payload, timestampMs)
                    checkPreviewDecoderWatchdog(now)
                }
            }
        ).also { it.start() }
    }

    private fun checkPreviewDecoderWatchdog(now: Long = System.currentTimeMillis()) {
        if (previewDecoder == null || lastVideoTagAtMs <= 0L) {
            return
        }
        if (now - lastPreviewWatchdogResetAtMs < PREVIEW_WATCHDOG_RESET_COOLDOWN_MS) {
            return
        }
        val noPreviewYet = lastPreviewFrameAtMs <= 0L &&
            firstVideoTagAtMs > 0L &&
            now - firstVideoTagAtMs >= FIRST_PREVIEW_TIMEOUT_MS
        val previewStale = lastPreviewFrameAtMs > 0L &&
            now - lastPreviewFrameAtMs >= PREVIEW_STALL_TIMEOUT_MS
        if (!noPreviewYet && !previewStale) {
            return
        }
        val reason = if (noPreviewYet) {
            "first_preview_timeout"
        } else {
            "preview_stall_${now - lastPreviewFrameAtMs}ms"
        }
        lastPreviewWatchdogResetAtMs = now
        broadcastLog(
            "预览看门狗触发: reason=$reason, videoTags=${latestSnapshot.videoTags}, " +
                "bytes=${latestSnapshot.totalPayloadBytes}",
            null
        )
        previewDecoder?.reset(reason)
    }

    private fun resetPreviewDecoder(reason: String) {
        val decoder = previewDecoder
        if (decoder == null) {
            broadcastLog("预览解码器外部复位跳过: reason=$reason, decoder=null", null)
            return
        }
        lastPreviewWatchdogResetAtMs = System.currentTimeMillis()
        lastPreviewFrameAtMs = 0L
        lastPreviewCacheAtMs = 0L
        firstVideoTagAtMs = 0L
        latestPreviewFrame = null
        broadcastLog(
            "预览解码器外部复位: reason=$reason, videoTags=${latestSnapshot.videoTags}, " +
                "bytes=${latestSnapshot.totalPayloadBytes}",
            null
        )
        decoder.reset(reason)
    }

    private fun stopReceiver(reason: String) {
        receiver?.stop(reason)
        receiver = null
        previewDecoder?.release()
        previewDecoder = null
        releaseStreamingLocks()
        receiverStartedAtMs = 0L
        lastVideoTagAtMs = 0L
        firstVideoTagAtMs = 0L
        lastPreviewFrameAtMs = 0L
        lastPreviewCacheAtMs = 0L
        lastPreviewWatchdogResetAtMs = 0L
        lastNotificationUpdateAtMs = 0L
        lastNotificationStateKey = ""
        latestPreviewFrame = null
        latestSnapshot = latestSnapshot.copy(
            running = false,
            listening = false,
            clientConnected = false,
            message = "RTMP 接收服务已停止"
        )
        broadcastSnapshot(latestSnapshot)
    }

    private fun acquireStreamingLocks(reason: String) {
        acquireWakeLock(reason)
        acquireWifiLock(reason)
    }

    private fun acquireWakeLock(reason: String) {
        val existing = wakeLock
        if (existing?.isHeld == true) {
            return
        }
        try {
            val powerManager = getSystemService(Context.POWER_SERVICE) as PowerManager
            wakeLock = powerManager.newWakeLock(
                PowerManager.PARTIAL_WAKE_LOCK,
                "$packageName:rtmp-receiver"
            ).apply {
                setReferenceCounted(false)
                acquire()
            }
            broadcastLog("RTMP 接收保活: WakeLock acquired, reason=$reason", null)
        } catch (e: Exception) {
            broadcastLog("RTMP 接收保活: WakeLock acquire failed, reason=$reason", e)
        }
    }

    private fun acquireWifiLock(reason: String) {
        val existing = wifiLock
        if (existing?.isHeld == true) {
            return
        }
        try {
            val wifiManager = applicationContext.getSystemService(Context.WIFI_SERVICE) as WifiManager
            val mode = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
                WifiManager.WIFI_MODE_FULL_LOW_LATENCY
            } else {
                @Suppress("DEPRECATION")
                WifiManager.WIFI_MODE_FULL_HIGH_PERF
            }
            wifiLock = wifiManager.createWifiLock(mode, "$packageName:rtmp-receiver").apply {
                setReferenceCounted(false)
                acquire()
            }
            broadcastLog("RTMP 接收保活: WifiLock acquired, reason=$reason", null)
        } catch (e: Exception) {
            broadcastLog("RTMP 接收保活: WifiLock acquire failed, reason=$reason", e)
        }
    }

    private fun releaseStreamingLocks() {
        try {
            wakeLock?.takeIf { it.isHeld }?.release()
        } catch (e: Exception) {
            broadcastLog("RTMP 接收保活: WakeLock release failed", e)
        } finally {
            wakeLock = null
        }
        try {
            wifiLock?.takeIf { it.isHeld }?.release()
        } catch (e: Exception) {
            broadcastLog("RTMP 接收保活: WifiLock release failed", e)
        } finally {
            wifiLock = null
        }
    }

    private fun broadcastSnapshot(snapshot: EmbeddedRtmpReceiver.Snapshot) {
        val intent = Intent(ACTION_STATUS).apply {
            setPackage(packageName)
            putExtra(EXTRA_RUNNING, snapshot.running)
            putExtra(EXTRA_LISTENING, snapshot.listening)
            putExtra(EXTRA_CONNECTED, snapshot.clientConnected)
            putExtra(EXTRA_PORT, snapshot.port)
            putExtra(EXTRA_STREAM_KEY, snapshot.expectedStreamKey)
            putExtra(EXTRA_APP_NAME, snapshot.appName)
            putExtra(EXTRA_STREAM_NAME, snapshot.streamName)
            putExtra(EXTRA_REMOTE, snapshot.remoteAddress)
            putExtra(EXTRA_VIDEO_TAGS, snapshot.videoTags)
            putExtra(EXTRA_AUDIO_TAGS, snapshot.audioTags)
            putExtra(EXTRA_METADATA_TAGS, snapshot.metadataTags)
            putExtra(EXTRA_BYTES, snapshot.totalPayloadBytes)
            putExtra(EXTRA_KEYFRAMES, snapshot.keyframeCount)
            putExtra(EXTRA_AVC_SEQ, snapshot.avcSequenceHeaderCount)
            putExtra(EXTRA_VIDEO_CODEC, snapshot.lastVideoCodec)
            putExtra(EXTRA_AUDIO_CODEC, snapshot.lastAudioCodec)
            putExtra(EXTRA_FIRST_VIDEO_AT, snapshot.firstVideoAtMs)
            putExtra(EXTRA_LAST_DATA_AT, snapshot.lastDataAtMs)
            putExtra(EXTRA_DISCONNECT_COUNT, snapshot.disconnectCount)
            putExtra(EXTRA_RECENT_DISCONNECT_COUNT, snapshot.recentDisconnectCount)
            putExtra(EXTRA_LAST_DISCONNECT_AT, snapshot.lastDisconnectAtMs)
            putExtra(EXTRA_MESSAGE, snapshot.message)
        }
        sendBroadcast(intent)
    }

    private fun broadcastPreview(jpegBytes: ByteArray, width: Int, height: Int, decodedFrames: Long) {
        val now = System.currentTimeMillis()
        if (latestPreviewFrame == null || now - lastPreviewCacheAtMs >= PREVIEW_CACHE_INTERVAL_MS) {
            latestPreviewFrame = CachedPreviewFrame(
                jpegBytes = jpegBytes.copyOf(),
                width = width,
                height = height,
                decodedFrames = decodedFrames,
                receivedAtMs = now
            )
            lastPreviewCacheAtMs = now
        }
        val listener = onPreviewFrameListener
        if (listener != null) {
            try {
                listener.invoke(jpegBytes, width, height, decodedFrames)
                return
            } catch (e: Exception) {
                broadcastLog("预览帧内存回调失败，回退到广播传递", e)
            }
        }
        val intent = Intent(ACTION_PREVIEW).apply {
            setPackage(packageName)
            putExtra(EXTRA_PREVIEW_JPEG, jpegBytes)
            putExtra(EXTRA_PREVIEW_WIDTH, width)
            putExtra(EXTRA_PREVIEW_HEIGHT, height)
            putExtra(EXTRA_DECODED_FRAMES, decodedFrames)
        }
        sendBroadcast(intent)
    }

    private fun broadcastLog(message: String, throwable: Throwable?) {
        val intent = Intent(ACTION_LOG).apply {
            setPackage(packageName)
            putExtra(EXTRA_MESSAGE, message)
            throwable?.let { putExtra(EXTRA_THROWABLE, android.util.Log.getStackTraceString(it)) }
        }
        sendBroadcast(intent)
    }

    private fun updateNotification(snapshot: EmbeddedRtmpReceiver.Snapshot) {
        val now = System.currentTimeMillis()
        val stateKey = buildString {
            append(snapshot.running)
            append('|')
            append(snapshot.listening)
            append('|')
            append(snapshot.clientConnected)
            append('|')
            append(snapshot.port)
            append('|')
            append(snapshot.expectedStreamKey)
            append('|')
            append(snapshot.streamName)
            append('|')
            append(snapshot.lastVideoCodec)
            append('|')
            append(snapshot.message)
        }
        if (stateKey == lastNotificationStateKey &&
            now - lastNotificationUpdateAtMs < NOTIFICATION_UPDATE_INTERVAL_MS
        ) {
            return
        }
        lastNotificationStateKey = stateKey
        lastNotificationUpdateAtMs = now
        val manager = getSystemService(NotificationManager::class.java)
        manager.notify(
            NOTIFICATION_ID,
            buildNotification(snapshot.message, snapshot.port, snapshot.expectedStreamKey)
        )
    }

    private fun buildNotification(message: String, port: Int, streamKey: String) =
        NotificationCompat.Builder(this, CHANNEL_ID)
            .setSmallIcon(R.drawable.ic_nav_video)
            .setContentTitle("RTMP 接收验证运行中")
            .setContentText(message)
            .setStyle(
                NotificationCompat.BigTextStyle().bigText(
                    "$message\n推流地址：rtmp://手机IP:$port/live\n推流码：$streamKey"
                )
            )
            .setOngoing(true)
            .setOnlyAlertOnce(true)
            .setContentIntent(openAppPendingIntent())
            .build()

    private fun openAppPendingIntent(): PendingIntent? {
        val launchIntent = packageManager.getLaunchIntentForPackage(packageName) ?: return null
        return PendingIntent.getActivity(
            this,
            0,
            launchIntent,
            PendingIntent.FLAG_UPDATE_CURRENT or PendingIntent.FLAG_IMMUTABLE
        )
    }

    private fun ensureNotificationChannel() {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.O) {
            return
        }
        val channel = NotificationChannel(
            CHANNEL_ID,
            "RTMP 接收验证",
            NotificationManager.IMPORTANCE_LOW
        )
        getSystemService(NotificationManager::class.java).createNotificationChannel(channel)
    }

    companion object {
        const val ACTION_START = "com.bidding.glasses.rtmp.START"
        const val ACTION_STOP = "com.bidding.glasses.rtmp.STOP"
        const val ACTION_STATUS = "com.bidding.glasses.rtmp.STATUS"
        const val ACTION_LOG = "com.bidding.glasses.rtmp.LOG"
        const val ACTION_PREVIEW = "com.bidding.glasses.rtmp.PREVIEW"
        const val ACTION_RESET_PREVIEW = "com.bidding.glasses.rtmp.RESET_PREVIEW"

        const val EXTRA_PORT = "port"
        const val EXTRA_STREAM_KEY = "stream_key"
        const val EXTRA_REASON = "reason"
        const val EXTRA_RUNNING = "running"
        const val EXTRA_LISTENING = "listening"
        const val EXTRA_CONNECTED = "connected"
        const val EXTRA_APP_NAME = "app_name"
        const val EXTRA_STREAM_NAME = "stream_name"
        const val EXTRA_REMOTE = "remote"
        const val EXTRA_VIDEO_TAGS = "video_tags"
        const val EXTRA_AUDIO_TAGS = "audio_tags"
        const val EXTRA_METADATA_TAGS = "metadata_tags"
        const val EXTRA_BYTES = "bytes"
        const val EXTRA_KEYFRAMES = "keyframes"
        const val EXTRA_AVC_SEQ = "avc_seq"
        const val EXTRA_VIDEO_CODEC = "video_codec"
        const val EXTRA_AUDIO_CODEC = "audio_codec"
        const val EXTRA_FIRST_VIDEO_AT = "first_video_at"
        const val EXTRA_LAST_DATA_AT = "last_data_at"
        const val EXTRA_DISCONNECT_COUNT = "disconnect_count"
        const val EXTRA_RECENT_DISCONNECT_COUNT = "recent_disconnect_count"
        const val EXTRA_LAST_DISCONNECT_AT = "last_disconnect_at"
        const val EXTRA_MESSAGE = "message"
        const val EXTRA_THROWABLE = "throwable"
        const val EXTRA_PREVIEW_JPEG = "preview_jpeg"
        const val EXTRA_PREVIEW_WIDTH = "preview_width"
        const val EXTRA_PREVIEW_HEIGHT = "preview_height"
        const val EXTRA_DECODED_FRAMES = "decoded_frames"

        private const val CHANNEL_ID = "rtmp_receiver"
        private const val NOTIFICATION_ID = 1935
        private const val DEFAULT_PORT = 1935
        private const val DEFAULT_STREAM_KEY = "rokid"
        private const val NOTIFICATION_UPDATE_INTERVAL_MS = 2_000L
        private const val FIRST_PREVIEW_TIMEOUT_MS = 5_000L
        private const val PREVIEW_STALL_TIMEOUT_MS = 4_000L
        private const val PREVIEW_WATCHDOG_RESET_COOLDOWN_MS = 6_000L
        private const val PREVIEW_CACHE_INTERVAL_MS = 500L

        @Volatile var latestSnapshot: EmbeddedRtmpReceiver.Snapshot = EmbeddedRtmpReceiver.Snapshot()
        @Volatile var latestPreviewFrame: CachedPreviewFrame? = null

        @Volatile var onPreviewFrameListener: ((jpegBytes: ByteArray, width: Int, height: Int, decodedFrames: Long) -> Unit)? = null
    }

    data class CachedPreviewFrame(
        val jpegBytes: ByteArray,
        val width: Int,
        val height: Int,
        val decodedFrames: Long,
        val receivedAtMs: Long
    )
}
