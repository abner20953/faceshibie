package com.bidding.glasses

import java.io.ByteArrayOutputStream
import java.io.DataInputStream
import java.io.EOFException
import java.io.InputStream
import java.io.OutputStream
import java.net.InetSocketAddress
import java.net.ServerSocket
import java.net.Socket
import java.net.SocketTimeoutException
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.util.ArrayDeque
import java.util.Locale
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import kotlin.math.min

/**
 * Minimal RTMP publish receiver for field verification.
 *
 * It intentionally does not decode video or call cloud APIs. The first milestone is only:
 * - accept a publish connection from the glasses,
 * - complete the RTMP handshake / publish commands,
 * - count incoming FLV video/audio/metadata messages.
 *
 * Keeping this class isolated makes the experimental live-stream path easy to replace later
 * with a full RTMP/FFmpeg pipeline without touching the existing photo/gallery/video workflows.
 */
class EmbeddedRtmpReceiver(
    private val port: Int,
    private val expectedStreamKey: String,
    private val callback: Callback
) {

    interface Callback {
        fun onSnapshot(snapshot: Snapshot)
        fun onLog(message: String, throwable: Throwable? = null)
        fun onVideoTag(payload: ByteArray, timestampMs: Int) {}
    }

    data class Snapshot(
        val running: Boolean = false,
        val listening: Boolean = false,
        val clientConnected: Boolean = false,
        val port: Int = 1935,
        val expectedStreamKey: String = "rokid",
        val appName: String = "",
        val streamName: String = "",
        val remoteAddress: String = "",
        val videoTags: Long = 0L,
        val audioTags: Long = 0L,
        val metadataTags: Long = 0L,
        val totalPayloadBytes: Long = 0L,
        val keyframeCount: Long = 0L,
        val avcSequenceHeaderCount: Long = 0L,
        val lastVideoCodec: String = "",
        val lastAudioCodec: String = "",
        val firstVideoAtMs: Long = 0L,
        val lastDataAtMs: Long = 0L,
        val disconnectCount: Long = 0L,
        val recentDisconnectCount: Int = 0,
        val lastDisconnectAtMs: Long = 0L,
        val message: String = "未启动"
    )

    private data class ChunkStreamState(
        var timestamp: Int = 0,
        var timestampDelta: Int = 0,
        var messageLength: Int = 0,
        var messageTypeId: Int = 0,
        var messageStreamId: Int = 0,
        var payload: ByteArrayOutputStream? = null,
        var received: Int = 0
    )

    @Volatile private var stopRequested = false
    @Volatile private var serverSocket: ServerSocket? = null
    @Volatile private var clientSocket: Socket? = null
    @Volatile private var snapshot = Snapshot(port = port, expectedStreamKey = expectedStreamKey)
    private var executor: ExecutorService? = null
    private var inboundChunkSize = DEFAULT_RTMP_CHUNK_SIZE
    private var outboundChunkSize = DEFAULT_RTMP_CHUNK_SIZE
    private var lastSnapshotEmitAt = 0L
    private var lastAcknowledgedPayloadBytes = 0L
    private var disconnectCount = 0L
    private var lastDisconnectAtMs = 0L
    private val recentDisconnectAtMs = ArrayDeque<Long>()

    fun start() {
        if (executor != null) {
            callback.onLog("内置 RTMP 接收服务已在运行")
            return
        }
        stopRequested = false
        snapshot = Snapshot(
            running = true,
            listening = false,
            port = port,
            expectedStreamKey = expectedStreamKey,
            message = "正在启动 RTMP 接收服务..."
        )
        callback.onSnapshot(snapshot)
        executor = Executors.newSingleThreadExecutor { runnable ->
            Thread(runnable, "EmbeddedRtmpReceiver").apply { isDaemon = true }
        }
        executor?.execute {
            runServerLoop()
        }
    }

    fun stop(reason: String = "stop") {
        stopRequested = true
        updateSnapshot(message = "正在停止 RTMP 接收服务: $reason")
        try {
            clientSocket?.close()
        } catch (_: Exception) {
        }
        try {
            serverSocket?.close()
        } catch (_: Exception) {
        }
        executor?.shutdownNow()
        executor = null
    }

    fun currentSnapshot(): Snapshot = snapshot

    private fun runServerLoop() {
        try {
            ServerSocket().use { server ->
                server.reuseAddress = true
                server.bind(InetSocketAddress(port))
                server.soTimeout = SERVER_ACCEPT_TIMEOUT_MS
                serverSocket = server
                updateSnapshot(
                    listening = true,
                    message = "RTMP 接收服务已启动，等待眼镜推流..."
                )
                callback.onLog("内置 RTMP 接收服务监听中: port=$port, expectedKey=$expectedStreamKey")

                while (!stopRequested) {
                    try {
                        val socket = server.accept()
                        clientSocket?.close()
                        clientSocket = socket
                        socket.tcpNoDelay = true
                        socket.soTimeout = SOCKET_READ_TIMEOUT_MS
                        handleClient(socket)
                    } catch (_: SocketTimeoutException) {
                        // Periodically check stopRequested.
                    }
                }
            }
        } catch (e: Exception) {
            if (!stopRequested) {
                callback.onLog("内置 RTMP 接收服务异常", e)
                updateSnapshot(
                    running = false,
                    listening = false,
                    clientConnected = false,
                    message = "RTMP 接收服务启动失败: ${e.message ?: e.javaClass.simpleName}"
                )
            }
        } finally {
            serverSocket = null
            clientSocket = null
            val finalMessage = if (stopRequested) "RTMP 接收服务已停止" else snapshot.message
            snapshot = snapshot.copy(
                running = false,
                listening = false,
                clientConnected = false,
                message = finalMessage
            )
            callback.onSnapshot(snapshot)
            executor = null
        }
    }

    private fun handleClient(socket: Socket) {
        val remote = socket.remoteSocketAddress?.toString().orEmpty()
        callback.onLog("RTMP 客户端已连接: remote=$remote")
        lastAcknowledgedPayloadBytes = 0L
        updateSnapshot(
            clientConnected = true,
            remoteAddress = remote,
            appName = "",
            streamName = "",
            videoTags = 0L,
            audioTags = 0L,
            metadataTags = 0L,
            totalPayloadBytes = 0L,
            keyframeCount = 0L,
            avcSequenceHeaderCount = 0L,
            lastVideoCodec = "",
            lastAudioCodec = "",
            firstVideoAtMs = 0L,
            lastDataAtMs = 0L,
            message = "眼镜已连接，正在等待推流命令..."
        )

        try {
            socket.getInputStream().use { rawInput ->
                socket.getOutputStream().use { output ->
                    val input = DataInputStream(rawInput)
                    performHandshake(input, output)
                    callback.onLog("RTMP 握手完成: remote=$remote")
                    updateSnapshot(message = "RTMP 握手完成，等待 publish...")
                    readRtmpMessages(input, output)
                }
            }
        } catch (e: EOFException) {
            callback.onLog("RTMP 客户端断开: remote=$remote")
            if (!stopRequested) {
                recordClientDisconnect()
            }
        } catch (e: SocketTimeoutException) {
            if (!stopRequested) {
                callback.onLog("RTMP 客户端读取超时: remote=$remote", e)
                recordClientDisconnect()
            }
        } catch (e: Exception) {
            if (!stopRequested) {
                callback.onLog("RTMP 客户端处理异常: remote=$remote", e)
                recordClientDisconnect()
            }
        } finally {
            try {
                socket.close()
            } catch (_: Exception) {
            }
            if (clientSocket === socket) {
                clientSocket = null
            }
            updateSnapshot(
                clientConnected = false,
                remoteAddress = "",
                message = if (stopRequested) "RTMP 接收服务正在停止" else "眼镜推流已断开，继续等待新连接..."
            )
        }
    }

    private fun recordClientDisconnect(now: Long = System.currentTimeMillis()) {
        disconnectCount += 1L
        lastDisconnectAtMs = now
        recentDisconnectAtMs.addLast(now)
        trimRecentDisconnects(now)
    }

    private fun trimRecentDisconnects(now: Long = System.currentTimeMillis()) {
        while (true) {
            val first = recentDisconnectAtMs.firstOrNull() ?: break
            if (now - first <= RECENT_DISCONNECT_WINDOW_MS) {
                break
            }
            recentDisconnectAtMs.removeFirst()
        }
    }

    private fun performHandshake(input: DataInputStream, output: OutputStream) {
        val c0 = input.readUnsignedByte()
        if (c0 != RTMP_VERSION) {
            throw IOExceptionCompat("Unsupported RTMP version: $c0")
        }
        val c1 = ByteArray(RTMP_HANDSHAKE_SIZE)
        input.readFully(c1)

        val s1 = ByteArray(RTMP_HANDSHAKE_SIZE)
        val now = (System.currentTimeMillis() / 1000L).toInt()
        s1[0] = ((now ushr 24) and 0xFF).toByte()
        s1[1] = ((now ushr 16) and 0xFF).toByte()
        s1[2] = ((now ushr 8) and 0xFF).toByte()
        s1[3] = (now and 0xFF).toByte()

        output.write(byteArrayOf(RTMP_VERSION.toByte()))
        output.write(s1)
        output.write(c1)
        output.flush()

        val c2 = ByteArray(RTMP_HANDSHAKE_SIZE)
        input.readFully(c2)
    }

    private fun readRtmpMessages(input: DataInputStream, output: OutputStream) {
        val chunkStates = mutableMapOf<Int, ChunkStreamState>()

        while (!stopRequested) {
            val first = try {
                input.readUnsignedByte()
            } catch (e: SocketTimeoutException) {
                continue
            }
            val fmt = (first and 0xC0) ushr 6
            var csid = first and 0x3F
            if (csid == 0) {
                csid = input.readUnsignedByte() + 64
            } else if (csid == 1) {
                val b0 = input.readUnsignedByte()
                val b1 = input.readUnsignedByte()
                csid = b0 + b1 * 256 + 64
            }

            val state = chunkStates.getOrPut(csid) { ChunkStreamState() }
            val startsNewMessage = readChunkHeader(fmt, input, state)
            if (startsNewMessage) {
                state.payload = ByteArrayOutputStream(state.messageLength.coerceAtLeast(0))
                state.received = 0
            } else if (state.payload == null || state.received >= state.messageLength) {
                state.payload = ByteArrayOutputStream(state.messageLength.coerceAtLeast(0))
                state.received = 0
                if (fmt == 3 && state.timestampDelta > 0) {
                    state.timestamp += state.timestampDelta
                }
            }

            val remaining = state.messageLength - state.received
            if (remaining <= 0) {
                processMessage(output, state.messageTypeId, state.messageStreamId, state.timestamp, ByteArray(0))
                state.payload = null
                state.received = 0
                continue
            }

            val chunkPayloadSize = min(inboundChunkSize, remaining)
            val chunkPayload = ByteArray(chunkPayloadSize)
            input.readFully(chunkPayload)
            state.payload?.write(chunkPayload)
            state.received += chunkPayloadSize

            if (state.received >= state.messageLength) {
                val payload = state.payload?.toByteArray() ?: ByteArray(0)
                processMessage(output, state.messageTypeId, state.messageStreamId, state.timestamp, payload)
                state.payload = null
                state.received = 0
            }
        }
    }

    private fun readChunkHeader(fmt: Int, input: DataInputStream, state: ChunkStreamState): Boolean {
        return when (fmt) {
            0 -> {
                var timestamp = readUInt24(input)
                val length = readUInt24(input)
                val typeId = input.readUnsignedByte()
                val streamId = readInt32LittleEndian(input)
                if (timestamp == RTMP_EXTENDED_TIMESTAMP) {
                    timestamp = readInt32BigEndian(input)
                }
                state.timestamp = timestamp
                state.timestampDelta = 0
                state.messageLength = length
                state.messageTypeId = typeId
                state.messageStreamId = streamId
                true
            }
            1 -> {
                var delta = readUInt24(input)
                val length = readUInt24(input)
                val typeId = input.readUnsignedByte()
                if (delta == RTMP_EXTENDED_TIMESTAMP) {
                    delta = readInt32BigEndian(input)
                }
                state.timestamp += delta
                state.timestampDelta = delta
                state.messageLength = length
                state.messageTypeId = typeId
                true
            }
            2 -> {
                var delta = readUInt24(input)
                if (delta == RTMP_EXTENDED_TIMESTAMP) {
                    delta = readInt32BigEndian(input)
                }
                state.timestamp += delta
                state.timestampDelta = delta
                true
            }
            else -> false
        }
    }

    private fun processMessage(
        output: OutputStream,
        typeId: Int,
        messageStreamId: Int,
        timestampMs: Int,
        payload: ByteArray
    ) {
        val nextTotalPayloadBytes = if (payload.isNotEmpty()) {
            val total = snapshot.totalPayloadBytes + payload.size
            updateSnapshot(
                totalPayloadBytes = total,
                lastDataAtMs = System.currentTimeMillis()
            )
            total
        } else {
            snapshot.totalPayloadBytes
        }

        when (typeId) {
            RTMP_MSG_SET_CHUNK_SIZE -> {
                if (payload.size >= 4) {
                    inboundChunkSize = ByteBuffer.wrap(payload, 0, 4).int and 0x7FFFFFFF
                    callback.onLog("RTMP 客户端设置 chunkSize=$inboundChunkSize")
                }
            }
            RTMP_MSG_USER_CONTROL -> handleUserControl(output, payload)
            RTMP_MSG_AUDIO -> handleAudio(payload)
            RTMP_MSG_VIDEO -> handleVideo(payload, timestampMs)
            RTMP_MSG_DATA_AMF0, RTMP_MSG_DATA_AMF3 -> handleMetadata(payload)
            RTMP_MSG_COMMAND_AMF0, RTMP_MSG_COMMAND_AMF3 -> handleCommand(output, typeId, messageStreamId, payload)
        }

        maybeSendAcknowledgement(output, nextTotalPayloadBytes)
    }

    private fun handleUserControl(output: OutputStream, payload: ByteArray) {
        if (payload.size < 2) {
            return
        }
        val eventType = ((payload[0].toInt() and 0xFF) shl 8) or (payload[1].toInt() and 0xFF)
        when (eventType) {
            RTMP_USER_CONTROL_PING_REQUEST -> {
                if (payload.size >= 6) {
                    val timestamp = ByteBuffer.wrap(payload, 2, 4).order(ByteOrder.BIG_ENDIAN).int
                    callback.onLog("RTMP ping 请求: timestamp=$timestamp，已响应 pong")
                    sendUserControlPingResponse(output, timestamp)
                }
            }
            RTMP_USER_CONTROL_STREAM_BEGIN -> {
                callback.onLog("RTMP user control: stream begin")
            }
        }
    }

    private fun maybeSendAcknowledgement(output: OutputStream, totalPayloadBytes: Long) {
        if (totalPayloadBytes - lastAcknowledgedPayloadBytes < SERVER_ACK_EVERY_BYTES) {
            return
        }
        val sequenceNumber = totalPayloadBytes.coerceAtMost(0x7FFFFFFFL).toInt()
        sendAcknowledgement(output, sequenceNumber)
        lastAcknowledgedPayloadBytes = totalPayloadBytes
        callback.onLog("RTMP ACK 已发送: sequence=$sequenceNumber, totalPayloadBytes=$totalPayloadBytes")
    }

    private fun handleCommand(output: OutputStream, typeId: Int, messageStreamId: Int, payload: ByteArray) {
        val commandPayload = if (typeId == RTMP_MSG_COMMAND_AMF3 && payload.isNotEmpty()) {
            payload.copyOfRange(1, payload.size)
        } else {
            payload
        }
        val reader = Amf0Reader(commandPayload)
        val command = reader.readValue() as? String ?: return
        val transactionId = (reader.readValue() as? Number)?.toDouble() ?: 0.0
        val remaining = mutableListOf<Any?>()
        while (reader.hasRemaining()) {
            remaining += reader.readValue()
        }
        val normalizedCommand = command.lowercase(Locale.ROOT)
        callback.onLog("RTMP 命令: command=$command, txn=$transactionId, streamId=$messageStreamId")

        when (normalizedCommand) {
            "connect" -> {
                val appName = (remaining.firstOrNull() as? Map<*, *>)?.get("app")?.toString().orEmpty()
                updateSnapshot(appName = appName, message = "收到 connect，正在响应...")
                sendSetChunkSize(output, SERVER_OUTBOUND_CHUNK_SIZE)
                sendWindowAcknowledgementSize(output, SERVER_ACK_WINDOW_SIZE)
                sendSetPeerBandwidth(output, SERVER_ACK_WINDOW_SIZE, 2)
                sendConnectResult(output, transactionId)
            }
            "releaseStream", "fcpublish" -> {
                if (transactionId > 0.0) {
                    sendCommand(output, 3, 0, "_result", transactionId, null)
                }
                if (normalizedCommand == "fcpublish") {
                    val streamName = remaining.filterIsInstance<String>().firstOrNull().orEmpty()
                    sendOnFCPublish(output, streamName)
                }
            }
            "createstream" -> {
                sendCommand(output, 3, 0, "_result", transactionId, null, 1.0)
            }
            "publish" -> {
                val streamName = remaining.filterIsInstance<String>().firstOrNull().orEmpty()
                val keyMatched = expectedStreamKey.isBlank() || streamName == expectedStreamKey
                updateSnapshot(
                    streamName = streamName,
                    message = if (keyMatched) {
                        "收到 publish，开始接收视频流..."
                    } else {
                        "收到 publish，推流码为 $streamName（预期 $expectedStreamKey），仍继续接收"
                    }
                )
                sendUserControlStreamBegin(output, 1)
                sendPublishStart(output, streamName)
            }
        }
    }

    private fun handleMetadata(payload: ByteArray) {
        updateSnapshot(metadataTags = snapshot.metadataTags + 1)
        if (snapshot.metadataTags <= 3) {
            callback.onLog("RTMP 元数据已收到: count=${snapshot.metadataTags}, bytes=${payload.size}")
        }
    }

    private fun handleAudio(payload: ByteArray) {
        val codec = if (payload.isNotEmpty()) {
            when ((payload[0].toInt() ushr 4) and 0x0F) {
                10 -> "AAC"
                2 -> "MP3"
                7 -> "G711A"
                8 -> "G711U"
                else -> "audioCodec=${(payload[0].toInt() ushr 4) and 0x0F}"
            }
        } else {
            ""
        }
        updateSnapshot(
            audioTags = snapshot.audioTags + 1,
            lastAudioCodec = codec
        )
    }

    private fun handleVideo(payload: ByteArray, timestampMs: Int) {
        val now = System.currentTimeMillis()
        var keyframes = snapshot.keyframeCount
        var avcSeq = snapshot.avcSequenceHeaderCount
        var codec = snapshot.lastVideoCodec
        if (payload.isNotEmpty()) {
            val frameType = (payload[0].toInt() ushr 4) and 0x0F
            val codecId = payload[0].toInt() and 0x0F
            if (frameType == 1) {
                keyframes += 1
            }
            codec = when (codecId) {
                7 -> "H.264/AVC"
                12 -> "H.265/HEVC"
                else -> "videoCodec=$codecId"
            }
            if (codecId == 7 && payload.size >= 5 && payload[1].toInt() == 0) {
                avcSeq += 1
            }
            if (codecId == 7) {
                callback.onVideoTag(payload, timestampMs)
            }
        }
        val firstVideoAt = if (snapshot.firstVideoAtMs <= 0L) now else snapshot.firstVideoAtMs
        updateSnapshot(
            videoTags = snapshot.videoTags + 1,
            keyframeCount = keyframes,
            avcSequenceHeaderCount = avcSeq,
            lastVideoCodec = codec,
            firstVideoAtMs = firstVideoAt,
            message = if (codec != snapshot.lastVideoCodec || !snapshot.message.startsWith("正在接收推流")) {
                "正在接收推流：codec=$codec"
            } else {
                snapshot.message
            }
        )
        if (snapshot.videoTags <= 3 || snapshot.videoTags % 60L == 0L) {
            callback.onLog(
                "RTMP 视频数据: videoTags=${snapshot.videoTags}, codec=$codec, " +
                    "keyframes=$keyframes, avcSeq=$avcSeq"
            )
        }
    }

    private fun updateSnapshot(
        running: Boolean = snapshot.running,
        listening: Boolean = snapshot.listening,
        clientConnected: Boolean = snapshot.clientConnected,
        appName: String = snapshot.appName,
        streamName: String = snapshot.streamName,
        remoteAddress: String = snapshot.remoteAddress,
        videoTags: Long = snapshot.videoTags,
        audioTags: Long = snapshot.audioTags,
        metadataTags: Long = snapshot.metadataTags,
        totalPayloadBytes: Long = snapshot.totalPayloadBytes,
        keyframeCount: Long = snapshot.keyframeCount,
        avcSequenceHeaderCount: Long = snapshot.avcSequenceHeaderCount,
        lastVideoCodec: String = snapshot.lastVideoCodec,
        lastAudioCodec: String = snapshot.lastAudioCodec,
        firstVideoAtMs: Long = snapshot.firstVideoAtMs,
        lastDataAtMs: Long = snapshot.lastDataAtMs,
        message: String = snapshot.message
    ) {
        val oldMessage = snapshot.message
        val now = System.currentTimeMillis()
        trimRecentDisconnects(now)
        snapshot = snapshot.copy(
            running = running,
            listening = listening,
            clientConnected = clientConnected,
            appName = appName,
            streamName = streamName,
            remoteAddress = remoteAddress,
            videoTags = videoTags,
            audioTags = audioTags,
            metadataTags = metadataTags,
            totalPayloadBytes = totalPayloadBytes,
            keyframeCount = keyframeCount,
            avcSequenceHeaderCount = avcSequenceHeaderCount,
            lastVideoCodec = lastVideoCodec,
            lastAudioCodec = lastAudioCodec,
            firstVideoAtMs = firstVideoAtMs,
            lastDataAtMs = lastDataAtMs,
            disconnectCount = disconnectCount,
            recentDisconnectCount = recentDisconnectAtMs.size,
            lastDisconnectAtMs = lastDisconnectAtMs,
            message = message
        )
        if (now - lastSnapshotEmitAt > SNAPSHOT_EMIT_INTERVAL_MS ||
            !running ||
            message != oldMessage ||
            videoTags <= 3
        ) {
            lastSnapshotEmitAt = now
            callback.onSnapshot(snapshot)
        }
    }

    private fun sendConnectResult(output: OutputStream, transactionId: Double) {
        sendCommand(
            output = output,
            chunkStreamId = 3,
            messageStreamId = 0,
            command = "_result",
            transactionId = transactionId,
            commandObject = mapOf(
                "fmsVer" to "FMS/3,5,7,7009",
                "capabilities" to 31.0,
                "mode" to 1.0
            ),
            mapOf(
                "level" to "status",
                "code" to "NetConnection.Connect.Success",
                "description" to "Connection succeeded.",
                "objectEncoding" to 0.0
            )
        )
    }

    private fun sendOnFCPublish(output: OutputStream, streamName: String) {
        sendCommand(
            output,
            chunkStreamId = 5,
            messageStreamId = 1,
            command = "onFCPublish",
            transactionId = 0.0,
            commandObject = null,
            mapOf(
                "code" to "NetStream.Publish.Start",
                "description" to "FCPublish to stream $streamName"
            )
        )
    }

    private fun sendPublishStart(output: OutputStream, streamName: String) {
        sendCommand(
            output,
            chunkStreamId = 5,
            messageStreamId = 1,
            command = "onStatus",
            transactionId = 0.0,
            commandObject = null,
            mapOf(
                "level" to "status",
                "code" to "NetStream.Publish.Start",
                "description" to "Start publishing $streamName",
                "details" to streamName
            )
        )
    }

    private fun sendSetChunkSize(output: OutputStream, chunkSize: Int) {
        outboundChunkSize = chunkSize
        val payload = ByteBuffer.allocate(4).putInt(chunkSize).array()
        sendRtmpMessage(output, 2, 0, RTMP_MSG_SET_CHUNK_SIZE, payload)
    }

    private fun sendWindowAcknowledgementSize(output: OutputStream, size: Int) {
        val payload = ByteBuffer.allocate(4).putInt(size).array()
        sendRtmpMessage(output, 2, 0, RTMP_MSG_WINDOW_ACK_SIZE, payload)
    }

    private fun sendSetPeerBandwidth(output: OutputStream, size: Int, limitType: Int) {
        val payload = ByteArrayOutputStream().apply {
            write(ByteBuffer.allocate(4).putInt(size).array())
            write(limitType)
        }.toByteArray()
        sendRtmpMessage(output, 2, 0, RTMP_MSG_SET_PEER_BANDWIDTH, payload)
    }

    private fun sendUserControlStreamBegin(output: OutputStream, streamId: Int) {
        val payload = ByteArrayOutputStream().apply {
            write(0)
            write(0)
            write(ByteBuffer.allocate(4).putInt(streamId).array())
        }.toByteArray()
        sendRtmpMessage(output, 2, 0, RTMP_MSG_USER_CONTROL, payload)
    }

    private fun sendUserControlPingResponse(output: OutputStream, timestamp: Int) {
        val payload = ByteArrayOutputStream().apply {
            write(0)
            write(RTMP_USER_CONTROL_PING_RESPONSE)
            write(ByteBuffer.allocate(4).putInt(timestamp).array())
        }.toByteArray()
        sendRtmpMessage(output, 2, 0, RTMP_MSG_USER_CONTROL, payload)
    }

    private fun sendAcknowledgement(output: OutputStream, sequenceNumber: Int) {
        val payload = ByteBuffer.allocate(4).putInt(sequenceNumber).array()
        sendRtmpMessage(output, 2, 0, RTMP_MSG_ACKNOWLEDGEMENT, payload)
    }

    private fun sendCommand(
        output: OutputStream,
        chunkStreamId: Int,
        messageStreamId: Int,
        command: String,
        transactionId: Double,
        commandObject: Any?,
        vararg arguments: Any?
    ) {
        val payload = ByteArrayOutputStream().apply {
            writeAmf0String(command)
            writeAmf0Number(transactionId)
            writeAmf0Value(commandObject)
            arguments.forEach { writeAmf0Value(it) }
        }.toByteArray()
        sendRtmpMessage(output, chunkStreamId, messageStreamId, RTMP_MSG_COMMAND_AMF0, payload)
    }

    private fun sendRtmpMessage(
        output: OutputStream,
        chunkStreamId: Int,
        messageStreamId: Int,
        typeId: Int,
        payload: ByteArray
    ) {
        var offset = 0
        var first = true
        while (offset < payload.size || first) {
            if (first) {
                writeBasicHeader(output, 0, chunkStreamId)
                writeUInt24(output, 0)
                writeUInt24(output, payload.size)
                output.write(typeId)
                writeInt32LittleEndian(output, messageStreamId)
                first = false
            } else {
                writeBasicHeader(output, 3, chunkStreamId)
            }
            val size = min(outboundChunkSize, payload.size - offset).coerceAtLeast(0)
            if (size > 0) {
                output.write(payload, offset, size)
                offset += size
            }
            if (payload.isEmpty()) {
                break
            }
        }
        output.flush()
    }

    private fun writeBasicHeader(output: OutputStream, fmt: Int, chunkStreamId: Int) {
        if (chunkStreamId in 2..63) {
            output.write((fmt shl 6) or chunkStreamId)
        } else if (chunkStreamId in 64..319) {
            output.write(fmt shl 6)
            output.write(chunkStreamId - 64)
        } else {
            output.write((fmt shl 6) or 1)
            val value = chunkStreamId - 64
            output.write(value and 0xFF)
            output.write((value ushr 8) and 0xFF)
        }
    }

    private class Amf0Reader(private val bytes: ByteArray) {
        private var offset = 0

        fun hasRemaining(): Boolean = offset < bytes.size

        fun readValue(): Any? {
            if (offset >= bytes.size) return null
            return when (val type = readUnsignedByte()) {
                0x00 -> readDouble()
                0x01 -> readUnsignedByte() != 0
                0x02 -> readUtf8(readUInt16())
                0x03 -> readObject()
                0x05, 0x06 -> null
                0x08 -> {
                    skip(4)
                    readObject()
                }
                0x0A -> {
                    val count = readInt32()
                    (0 until count).map { readValue() }
                }
                else -> {
                    throw IOExceptionCompat("Unsupported AMF0 type: $type")
                }
            }
        }

        private fun readObject(): Map<String, Any?> {
            val result = linkedMapOf<String, Any?>()
            while (offset + 3 <= bytes.size) {
                val keyLength = readUInt16()
                if (keyLength == 0 && offset < bytes.size && bytes[offset].toInt() == 0x09) {
                    offset += 1
                    break
                }
                val key = readUtf8(keyLength)
                result[key] = readValue()
            }
            return result
        }

        private fun readDouble(): Double {
            requireAvailable(8)
            val value = ByteBuffer.wrap(bytes, offset, 8).order(ByteOrder.BIG_ENDIAN).double
            offset += 8
            return value
        }

        private fun readInt32(): Int {
            requireAvailable(4)
            val value = ByteBuffer.wrap(bytes, offset, 4).order(ByteOrder.BIG_ENDIAN).int
            offset += 4
            return value
        }

        private fun readUInt16(): Int {
            requireAvailable(2)
            val value = ((bytes[offset].toInt() and 0xFF) shl 8) or (bytes[offset + 1].toInt() and 0xFF)
            offset += 2
            return value
        }

        private fun readUnsignedByte(): Int {
            requireAvailable(1)
            return bytes[offset++].toInt() and 0xFF
        }

        private fun readUtf8(length: Int): String {
            requireAvailable(length)
            val value = bytes.copyOfRange(offset, offset + length).toString(Charsets.UTF_8)
            offset += length
            return value
        }

        private fun skip(count: Int) {
            requireAvailable(count)
            offset += count
        }

        private fun requireAvailable(count: Int) {
            if (offset + count > bytes.size) {
                throw EOFException("AMF0 payload ended unexpectedly")
            }
        }
    }

    private fun ByteArrayOutputStream.writeAmf0Value(value: Any?) {
        when (value) {
            null -> write(0x05)
            is String -> writeAmf0String(value)
            is Number -> writeAmf0Number(value.toDouble())
            is Boolean -> {
                write(0x01)
                write(if (value) 1 else 0)
            }
            is Map<*, *> -> writeAmf0Object(value)
            else -> writeAmf0String(value.toString())
        }
    }

    private fun ByteArrayOutputStream.writeAmf0String(value: String) {
        val encoded = value.toByteArray(Charsets.UTF_8)
        write(0x02)
        write((encoded.size ushr 8) and 0xFF)
        write(encoded.size and 0xFF)
        write(encoded)
    }

    private fun ByteArrayOutputStream.writeAmf0Number(value: Double) {
        write(0x00)
        write(ByteBuffer.allocate(8).order(ByteOrder.BIG_ENDIAN).putDouble(value).array())
    }

    private fun ByteArrayOutputStream.writeAmf0Object(values: Map<*, *>) {
        write(0x03)
        values.forEach { (key, value) ->
            val keyBytes = key.toString().toByteArray(Charsets.UTF_8)
            write((keyBytes.size ushr 8) and 0xFF)
            write(keyBytes.size and 0xFF)
            write(keyBytes)
            writeAmf0Value(value)
        }
        write(0x00)
        write(0x00)
        write(0x09)
    }

    private fun readUInt24(input: DataInputStream): Int {
        return (input.readUnsignedByte() shl 16) or
            (input.readUnsignedByte() shl 8) or
            input.readUnsignedByte()
    }

    private fun readInt32BigEndian(input: DataInputStream): Int {
        return (input.readUnsignedByte() shl 24) or
            (input.readUnsignedByte() shl 16) or
            (input.readUnsignedByte() shl 8) or
            input.readUnsignedByte()
    }

    private fun readInt32LittleEndian(input: DataInputStream): Int {
        val b0 = input.readUnsignedByte()
        val b1 = input.readUnsignedByte()
        val b2 = input.readUnsignedByte()
        val b3 = input.readUnsignedByte()
        return b0 or (b1 shl 8) or (b2 shl 16) or (b3 shl 24)
    }

    private fun writeUInt24(output: OutputStream, value: Int) {
        output.write((value ushr 16) and 0xFF)
        output.write((value ushr 8) and 0xFF)
        output.write(value and 0xFF)
    }

    private fun writeInt32LittleEndian(output: OutputStream, value: Int) {
        output.write(value and 0xFF)
        output.write((value ushr 8) and 0xFF)
        output.write((value ushr 16) and 0xFF)
        output.write((value ushr 24) and 0xFF)
    }

    private class IOExceptionCompat(message: String) : java.io.IOException(message)

    companion object {
        private const val RTMP_VERSION = 3
        private const val RTMP_HANDSHAKE_SIZE = 1536
        private const val DEFAULT_RTMP_CHUNK_SIZE = 128
        private const val SERVER_OUTBOUND_CHUNK_SIZE = 4096
        private const val SERVER_ACK_WINDOW_SIZE = 5_000_000
        private const val SERVER_ACK_EVERY_BYTES = 1_000_000L
        private const val RECENT_DISCONNECT_WINDOW_MS = 60_000L
        private const val SERVER_ACCEPT_TIMEOUT_MS = 1000
        private const val SOCKET_READ_TIMEOUT_MS = 5000
        private const val SNAPSHOT_EMIT_INTERVAL_MS = 1000L
        private const val RTMP_EXTENDED_TIMESTAMP = 0xFFFFFF

        private const val RTMP_MSG_SET_CHUNK_SIZE = 1
        private const val RTMP_MSG_ACKNOWLEDGEMENT = 3
        private const val RTMP_MSG_USER_CONTROL = 4
        private const val RTMP_MSG_WINDOW_ACK_SIZE = 5
        private const val RTMP_MSG_SET_PEER_BANDWIDTH = 6
        private const val RTMP_MSG_AUDIO = 8
        private const val RTMP_MSG_VIDEO = 9
        private const val RTMP_MSG_DATA_AMF3 = 15
        private const val RTMP_MSG_COMMAND_AMF3 = 17
        private const val RTMP_MSG_DATA_AMF0 = 18
        private const val RTMP_MSG_COMMAND_AMF0 = 20

        private const val RTMP_USER_CONTROL_STREAM_BEGIN = 0
        private const val RTMP_USER_CONTROL_PING_REQUEST = 6
        private const val RTMP_USER_CONTROL_PING_RESPONSE = 7
    }
}
