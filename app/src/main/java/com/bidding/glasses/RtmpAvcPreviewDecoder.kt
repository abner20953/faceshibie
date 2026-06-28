package com.bidding.glasses

import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.ImageFormat
import android.graphics.Rect
import android.graphics.YuvImage
import android.media.Image
import android.media.MediaCodec
import android.media.MediaCodecInfo
import android.media.MediaFormat
import java.io.ByteArrayOutputStream
import java.nio.ByteBuffer

/**
 * Low-rate H.264 preview decoder for the embedded RTMP receiver.
 *
 * This is deliberately a preview probe, not the final recognition pipeline:
 * it decodes all video access units to keep the codec state healthy, but only emits
 * a throttled JPEG frame for UI preview / local face boxes.
 */
class RtmpAvcPreviewDecoder(
    private val callback: Callback
) {

    interface Callback {
        fun onPreviewFrame(jpegBytes: ByteArray, width: Int, height: Int, decodedFrames: Long)
        fun onDecoderLog(message: String, throwable: Throwable? = null)
    }

    private var codec: MediaCodec? = null
    private var configured = false
    private var naluLengthSize = 4
    private var decodedFrames = 0L
    private var fedFrames = 0L
    private var lastPreviewEmitAt = 0L
    private var outputWidth = 0
    private var outputHeight = 0
    private var cachedAvcConfigData: ByteArray? = null

    @Synchronized
    fun onVideoTag(payload: ByteArray, timestampMs: Int) {
        if (payload.size < 5) {
            return
        }
        val codecId = payload[0].toInt() and 0x0F
        if (codecId != 7) {
            return
        }
        val avcPacketType = payload[1].toInt() and 0xFF
        val avcPayload = payload.copyOfRange(5, payload.size)
        when (avcPacketType) {
            0 -> configureFromAvcDecoderConfigurationRecord(avcPayload)
            1 -> feedAccessUnit(avcPayload, timestampMs)
        }
    }

    @Synchronized
    fun release() {
        releaseInternal(clearCachedConfig = true)
    }

    @Synchronized
    fun reset(reason: String) {
        val cachedConfig = cachedAvcConfigData?.copyOf()
        callback.onDecoderLog("RTMP 预览解码器重置: reason=$reason, hasCachedConfig=${cachedConfig != null}")
        releaseInternal(clearCachedConfig = false)
        if (cachedConfig != null) {
            configureFromAvcDecoderConfigurationRecord(cachedConfig)
        }
    }

    private fun releaseInternal(clearCachedConfig: Boolean) {
        try {
            codec?.stop()
        } catch (_: Exception) {
        }
        try {
            codec?.release()
        } catch (_: Exception) {
        }
        codec = null
        configured = false
        decodedFrames = 0L
        fedFrames = 0L
        lastPreviewEmitAt = 0L
        if (clearCachedConfig) {
            cachedAvcConfigData = null
        }
    }

    private fun configureFromAvcDecoderConfigurationRecord(data: ByteArray) {
        try {
            val config = parseAvcDecoderConfigurationRecord(data)
            naluLengthSize = config.naluLengthSize
            val dimensions = parseSpsDimensions(config.sps)
            outputWidth = dimensions?.first ?: 720
            outputHeight = dimensions?.second ?: 1280
            cachedAvcConfigData = data.copyOf()
            releaseInternal(clearCachedConfig = false)
            naluLengthSize = config.naluLengthSize
            outputWidth = dimensions?.first ?: 720
            outputHeight = dimensions?.second ?: 1280

            val format = MediaFormat.createVideoFormat("video/avc", outputWidth, outputHeight).apply {
                setByteBuffer("csd-0", ByteBuffer.wrap(startCodePrefixed(config.sps)))
                setByteBuffer("csd-1", ByteBuffer.wrap(startCodePrefixed(config.pps)))
                setInteger(
                    MediaFormat.KEY_COLOR_FORMAT,
                    MediaCodecInfo.CodecCapabilities.COLOR_FormatYUV420Flexible
                )
            }
            codec = MediaCodec.createDecoderByType("video/avc").apply {
                configure(format, null, null, 0)
                start()
            }
            configured = true
            callback.onDecoderLog(
                "RTMP 预览解码器已配置: size=${outputWidth}x$outputHeight, naluLengthSize=$naluLengthSize"
            )
        } catch (e: Exception) {
            configured = false
            callback.onDecoderLog("RTMP 预览解码器配置失败", e)
        }
    }

    private fun feedAccessUnit(data: ByteArray, timestampMs: Int) {
        val activeCodec = codec ?: return
        if (!configured) {
            return
        }
        val accessUnit = try {
            lengthPrefixedNalusToAnnexB(data, naluLengthSize)
        } catch (e: Exception) {
            callback.onDecoderLog("RTMP H.264 NALU 转换失败", e)
            return
        }
        if (accessUnit.isEmpty()) {
            return
        }
        try {
            val inputIndex = activeCodec.dequeueInputBuffer(CODEC_DEQUEUE_TIMEOUT_US)
            if (inputIndex >= 0) {
                val inputBuffer = activeCodec.getInputBuffer(inputIndex)
                inputBuffer?.clear()
                inputBuffer?.put(accessUnit)
                activeCodec.queueInputBuffer(
                    inputIndex,
                    0,
                    accessUnit.size,
                    timestampMs.toLong().coerceAtLeast(0L) * 1000L,
                    0
                )
                fedFrames += 1
            }
            drainOutput(activeCodec)
        } catch (e: Exception) {
            callback.onDecoderLog("RTMP 预览解码异常，重置解码器", e)
            reset("decode_exception")
        }
    }

    private fun drainOutput(activeCodec: MediaCodec) {
        val bufferInfo = MediaCodec.BufferInfo()
        while (true) {
            when (val outputIndex = activeCodec.dequeueOutputBuffer(bufferInfo, CODEC_DEQUEUE_TIMEOUT_US)) {
                MediaCodec.INFO_TRY_AGAIN_LATER -> return
                MediaCodec.INFO_OUTPUT_FORMAT_CHANGED -> {
                    val format = activeCodec.outputFormat
                    outputWidth = if (format.containsKey(MediaFormat.KEY_WIDTH)) {
                        format.getInteger(MediaFormat.KEY_WIDTH)
                    } else {
                        outputWidth
                    }
                    outputHeight = if (format.containsKey(MediaFormat.KEY_HEIGHT)) {
                        format.getInteger(MediaFormat.KEY_HEIGHT)
                    } else {
                        outputHeight
                    }
                    callback.onDecoderLog("RTMP 预览解码输出格式: $format")
                }
                else -> if (outputIndex >= 0) {
                    decodedFrames += 1
                    val shouldEmit = bufferInfo.size > 0 &&
                        System.currentTimeMillis() - lastPreviewEmitAt >= PREVIEW_EMIT_INTERVAL_MS
                    if (shouldEmit) {
                        val image = activeCodec.getOutputImage(outputIndex)
                        if (image != null) {
                            image.use {
                                emitPreviewFrame(it)
                            }
                            lastPreviewEmitAt = System.currentTimeMillis()
                        }
                    }
                    activeCodec.releaseOutputBuffer(outputIndex, false)
                }
            }
        }
    }

    private fun emitPreviewFrame(image: Image) {
        try {
            val frame = imageToNativeJpegFrame(image)
            callback.onPreviewFrame(frame.bytes, frame.width, frame.height, decodedFrames)
        } catch (e: Exception) {
            callback.onDecoderLog("RTMP 预览帧生成失败", e)
        }
    }

    private fun imageToNativeJpegFrame(image: Image): PreviewFrame {
        val crop = normalizedEvenCrop(image.cropRect, image.width, image.height)
        val width = crop.width()
        val height = crop.height()
        require(width >= 2 && height >= 2) { "Invalid preview crop: $crop" }
        val nv21 = yuv420ThreePlanesToNV21(image, crop, width, height)
        val bytes = ByteArrayOutputStream((width * height / 6).coerceAtLeast(32 * 1024)).use { out ->
            val yuvImage = YuvImage(nv21, ImageFormat.NV21, width, height, null)
            val success = yuvImage.compressToJpeg(Rect(0, 0, width, height), PREVIEW_JPEG_QUALITY, out)
            require(success) { "YuvImage.compressToJpeg failed: ${width}x$height" }
            out.toByteArray()
        }
        return maybeScaleJpegFrame(bytes, width, height, PREVIEW_JPEG_MAX_SIDE)
    }

    private fun normalizedEvenCrop(rawCrop: Rect, imageWidth: Int, imageHeight: Int): Rect {
        val left = rawCrop.left.coerceIn(0, (imageWidth - 2).coerceAtLeast(0)) and -2
        val top = rawCrop.top.coerceIn(0, (imageHeight - 2).coerceAtLeast(0)) and -2
        var right = rawCrop.right.coerceIn(left + 2, imageWidth)
        var bottom = rawCrop.bottom.coerceIn(top + 2, imageHeight)
        if ((right - left) % 2 != 0) {
            right -= 1
        }
        if ((bottom - top) % 2 != 0) {
            bottom -= 1
        }
        return Rect(left, top, right.coerceAtLeast(left + 2), bottom.coerceAtLeast(top + 2))
    }

    private fun yuv420ThreePlanesToNV21(image: Image, crop: Rect, width: Int, height: Int): ByteArray {
        require(image.planes.size >= 3) { "Unsupported decoded image planes=${image.planes.size}" }
        val planes = image.planes
        val yPlaneSize = width * height
        val nv21 = ByteArray(yPlaneSize + width * height / 2)
        copyLumaPlaneToNv21(planes[0], crop, width, height, nv21)
        copyChromaPlanesToNv21(
            uPlane = planes[1],
            vPlane = planes[2],
            crop = crop,
            width = width,
            height = height,
            output = nv21,
            outputOffset = yPlaneSize
        )
        return nv21
    }

    private fun copyLumaPlaneToNv21(
        plane: Image.Plane,
        crop: Rect,
        width: Int,
        height: Int,
        output: ByteArray
    ) {
        val buffer = plane.buffer.duplicate()
        val basePosition = buffer.position()
        val limit = buffer.limit()
        val rowStride = plane.rowStride
        val pixelStride = plane.pixelStride
        for (row in 0 until height) {
            val sourceRow = crop.top + row
            val sourceIndex = basePosition + sourceRow * rowStride + crop.left * pixelStride
            val outputIndex = row * width
            if (pixelStride == 1 && sourceIndex >= basePosition && sourceIndex + width <= limit) {
                buffer.position(sourceIndex)
                buffer.get(output, outputIndex, width)
            } else {
                for (col in 0 until width) {
                    output[outputIndex + col] = readPlaneByte(
                        plane = plane,
                        x = crop.left + col,
                        y = sourceRow,
                        fallback = 16
                    )
                }
            }
        }
    }

    private fun copyChromaPlanesToNv21(
        uPlane: Image.Plane,
        vPlane: Image.Plane,
        crop: Rect,
        width: Int,
        height: Int,
        output: ByteArray,
        outputOffset: Int
    ) {
        val chromaWidth = width / 2
        val chromaHeight = height / 2
        val chromaLeft = crop.left / 2
        val chromaTop = crop.top / 2
        for (row in 0 until chromaHeight) {
            val outputRow = outputOffset + row * width
            val sourceY = chromaTop + row
            for (col in 0 until chromaWidth) {
                val sourceX = chromaLeft + col
                val outputIndex = outputRow + col * 2
                output[outputIndex] = readPlaneByte(vPlane, sourceX, sourceY, fallback = 128)
                output[outputIndex + 1] = readPlaneByte(uPlane, sourceX, sourceY, fallback = 128)
            }
        }
    }

    private fun readPlaneByte(plane: Image.Plane, x: Int, y: Int, fallback: Int): Byte {
        val buffer = plane.buffer
        val index = buffer.position() + y * plane.rowStride + x * plane.pixelStride
        return if (index >= buffer.position() && index < buffer.limit()) {
            buffer.get(index)
        } else {
            fallback.toByte()
        }
    }

    private fun maybeScaleJpegFrame(bytes: ByteArray, width: Int, height: Int, maxSide: Int): PreviewFrame {
        val largestSide = maxOf(width, height)
        if (largestSide <= maxSide) {
            return PreviewFrame(bytes, width, height)
        }
        val scale = maxSide.toFloat() / largestSide.toFloat()
        val targetWidth = (width * scale).toInt().coerceAtLeast(2)
        val targetHeight = (height * scale).toInt().coerceAtLeast(2)
        val source = BitmapFactory.decodeByteArray(bytes, 0, bytes.size)
            ?: return PreviewFrame(bytes, width, height)
        val scaled = try {
            Bitmap.createScaledBitmap(source, targetWidth, targetHeight, true)
        } finally {
            try {
                source.recycle()
            } catch (_: Exception) {
            }
        }
        return try {
            val scaledBytes = ByteArrayOutputStream((targetWidth * targetHeight / 6).coerceAtLeast(32 * 1024)).use { out ->
                scaled.compress(Bitmap.CompressFormat.JPEG, PREVIEW_JPEG_QUALITY, out)
                out.toByteArray()
            }
            PreviewFrame(scaledBytes, targetWidth, targetHeight)
        } finally {
            try {
                scaled.recycle()
            } catch (_: Exception) {
            }
        }
    }

    private fun parseAvcDecoderConfigurationRecord(data: ByteArray): AvcConfig {
        require(data.size >= 7) { "AVC config too short: ${data.size}" }
        val lengthSize = (data[4].toInt() and 0x03) + 1
        var offset = 5
        val spsCount = data[offset++].toInt() and 0x1F
        require(spsCount > 0) { "AVC config missing SPS" }
        val spsLength = readUInt16(data, offset)
        offset += 2
        require(offset + spsLength <= data.size) { "AVC config SPS overflow" }
        val sps = data.copyOfRange(offset, offset + spsLength)
        offset += spsLength
        require(offset < data.size) { "AVC config missing PPS count" }
        val ppsCount = data[offset++].toInt() and 0xFF
        require(ppsCount > 0) { "AVC config missing PPS" }
        val ppsLength = readUInt16(data, offset)
        offset += 2
        require(offset + ppsLength <= data.size) { "AVC config PPS overflow" }
        val pps = data.copyOfRange(offset, offset + ppsLength)
        return AvcConfig(lengthSize, sps, pps)
    }

    private fun lengthPrefixedNalusToAnnexB(data: ByteArray, lengthSize: Int): ByteArray {
        val output = ByteArrayOutputStream()
        var offset = 0
        while (offset + lengthSize <= data.size) {
            var length = 0
            repeat(lengthSize) {
                length = (length shl 8) or (data[offset + it].toInt() and 0xFF)
            }
            offset += lengthSize
            if (length <= 0 || offset + length > data.size) {
                break
            }
            output.write(START_CODE)
            output.write(data, offset, length)
            offset += length
        }
        return output.toByteArray()
    }

    private fun startCodePrefixed(nalu: ByteArray): ByteArray {
        return ByteArrayOutputStream().apply {
            write(START_CODE)
            write(nalu)
        }.toByteArray()
    }

    private fun parseSpsDimensions(sps: ByteArray): Pair<Int, Int>? {
        return try {
            val rbsp = removeEmulationPreventionBytes(sps)
            val bits = BitReader(rbsp)
            bits.readBits(8) // nal header
            val profileIdc = bits.readBits(8)
            bits.readBits(8) // constraints
            bits.readBits(8) // level
            bits.readUE() // sps id
            var chromaFormatIdc = 1
            if (profileIdc in setOf(100, 110, 122, 244, 44, 83, 86, 118, 128, 138, 144)) {
                chromaFormatIdc = bits.readUE()
                if (chromaFormatIdc == 3) {
                    bits.readBit()
                }
                bits.readUE()
                bits.readUE()
                bits.readBit()
                val seqScalingMatrixPresent = bits.readBit() == 1
                if (seqScalingMatrixPresent) {
                    val count = if (chromaFormatIdc != 3) 8 else 12
                    for (i in 0 until count) {
                        if (bits.readBit() == 1) {
                            skipScalingList(bits, if (i < 6) 16 else 64)
                        }
                    }
                }
            }
            bits.readUE() // log2_max_frame_num_minus4
            val picOrderCntType = bits.readUE()
            if (picOrderCntType == 0) {
                bits.readUE()
            } else if (picOrderCntType == 1) {
                bits.readBit()
                bits.readSE()
                bits.readSE()
                val cycle = bits.readUE()
                repeat(cycle) { bits.readSE() }
            }
            bits.readUE() // max_num_ref_frames
            bits.readBit() // gaps flag
            val picWidthInMbsMinus1 = bits.readUE()
            val picHeightInMapUnitsMinus1 = bits.readUE()
            val frameMbsOnlyFlag = bits.readBit()
            if (frameMbsOnlyFlag == 0) {
                bits.readBit()
            }
            bits.readBit() // direct 8x8
            var cropLeft = 0
            var cropRight = 0
            var cropTop = 0
            var cropBottom = 0
            if (bits.readBit() == 1) {
                cropLeft = bits.readUE()
                cropRight = bits.readUE()
                cropTop = bits.readUE()
                cropBottom = bits.readUE()
            }
            val width = (picWidthInMbsMinus1 + 1) * 16
            val height = (2 - frameMbsOnlyFlag) * (picHeightInMapUnitsMinus1 + 1) * 16
            val cropUnitX: Int
            val cropUnitY: Int
            if (chromaFormatIdc == 0) {
                cropUnitX = 1
                cropUnitY = 2 - frameMbsOnlyFlag
            } else {
                val subWidthC = if (chromaFormatIdc == 3) 1 else 2
                val subHeightC = if (chromaFormatIdc == 1) 2 else 1
                cropUnitX = subWidthC
                cropUnitY = subHeightC * (2 - frameMbsOnlyFlag)
            }
            val croppedWidth = width - (cropLeft + cropRight) * cropUnitX
            val croppedHeight = height - (cropTop + cropBottom) * cropUnitY
            croppedWidth.coerceAtLeast(1) to croppedHeight.coerceAtLeast(1)
        } catch (_: Exception) {
            null
        }
    }

    private fun skipScalingList(bits: BitReader, size: Int) {
        var lastScale = 8
        var nextScale = 8
        for (j in 0 until size) {
            if (nextScale != 0) {
                val deltaScale = bits.readSE()
                nextScale = (lastScale + deltaScale + 256) % 256
            }
            lastScale = if (nextScale == 0) lastScale else nextScale
        }
    }

    private fun removeEmulationPreventionBytes(data: ByteArray): ByteArray {
        val output = ByteArrayOutputStream(data.size)
        var i = 0
        var zeroCount = 0
        while (i < data.size) {
            val value = data[i].toInt() and 0xFF
            if (zeroCount >= 2 && value == 0x03) {
                i += 1
                zeroCount = 0
                continue
            }
            output.write(value)
            zeroCount = if (value == 0) zeroCount + 1 else 0
            i += 1
        }
        return output.toByteArray()
    }



    private fun readUInt16(data: ByteArray, offset: Int): Int {
        return ((data[offset].toInt() and 0xFF) shl 8) or (data[offset + 1].toInt() and 0xFF)
    }

    private data class AvcConfig(
        val naluLengthSize: Int,
        val sps: ByteArray,
        val pps: ByteArray
    )

    private data class PreviewFrame(
        val bytes: ByteArray,
        val width: Int,
        val height: Int
    )

    private class BitReader(private val data: ByteArray) {
        private var bitOffset = 0

        fun readBit(): Int = readBits(1)

        fun readBits(count: Int): Int {
            var value = 0
            repeat(count) {
                val byteIndex = bitOffset / 8
                val shift = 7 - (bitOffset % 8)
                val bit = if (byteIndex < data.size) {
                    (data[byteIndex].toInt() shr shift) and 1
                } else {
                    0
                }
                value = (value shl 1) or bit
                bitOffset += 1
            }
            return value
        }

        fun readUE(): Int {
            var zeros = 0
            while (readBit() == 0 && zeros < 32) {
                zeros += 1
            }
            val suffix = if (zeros > 0) readBits(zeros) else 0
            return (1 shl zeros) - 1 + suffix
        }

        fun readSE(): Int {
            val value = readUE()
            val sign = if (value % 2 == 0) -1 else 1
            return sign * ((value + 1) / 2)
        }
    }

    companion object {
        private val START_CODE = byteArrayOf(0, 0, 0, 1)
        private const val CODEC_DEQUEUE_TIMEOUT_US = 1_000L
        private const val PREVIEW_EMIT_INTERVAL_MS = 100L
        private const val PREVIEW_JPEG_MAX_SIDE = 1280
        private const val PREVIEW_JPEG_QUALITY = 90
    }
}
