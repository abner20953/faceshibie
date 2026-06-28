package com.bidding.glasses

import android.Manifest

import android.app.Activity

import android.content.BroadcastReceiver

import android.content.ClipData

import android.content.ClipboardManager

import android.content.ContentUris

import android.content.Context

import android.content.Intent

import android.content.IntentFilter

import android.content.pm.PackageManager

import android.graphics.Bitmap

import android.graphics.BitmapFactory
import android.graphics.BitmapRegionDecoder

import android.graphics.Canvas

import android.graphics.Color

import android.graphics.Matrix

import android.graphics.Paint

import android.graphics.Rect

import android.hardware.display.DisplayManager

import android.media.AudioAttributes

import android.media.AudioManager

import android.media.ExifInterface

import android.media.Image

import android.media.MediaCodec

import android.media.MediaExtractor

import android.media.MediaFormat

import android.media.MediaMetadataRetriever

import android.media.ToneGenerator

import android.net.Uri

import android.os.Bundle

import android.os.Handler

import android.os.Looper

import android.os.Build

import android.provider.MediaStore

import android.provider.OpenableColumns

import android.speech.tts.TextToSpeech

import android.text.Editable

import android.text.TextWatcher

import android.util.Base64

import android.util.Log

import android.util.Size

import android.view.Display

import android.view.KeyEvent

import android.view.MotionEvent

import android.view.View

import android.view.animation.AlphaAnimation

import android.widget.Button

import android.widget.FrameLayout

import android.widget.ImageView

import android.widget.LinearLayout

import android.widget.ScrollView

import android.widget.TextView

import android.widget.Toast

import androidx.appcompat.app.AlertDialog

import androidx.appcompat.app.AppCompatActivity

import androidx.core.app.ActivityCompat

import androidx.core.content.ContextCompat

import com.bidding.glasses.databinding.ActivityMainBinding

import com.google.android.gms.tasks.Tasks

import com.google.gson.Gson

import com.google.gson.JsonObject

import com.google.gson.reflect.TypeToken

import com.google.mlkit.vision.common.InputImage

import com.google.mlkit.vision.face.Face

import com.google.mlkit.vision.face.FaceDetection

import com.google.mlkit.vision.face.FaceDetector

import com.google.mlkit.vision.face.FaceDetectorOptions

import okhttp3.*

import okhttp3.MediaType.Companion.toMediaTypeOrNull

import okhttp3.RequestBody.Companion.toRequestBody

import java.io.ByteArrayOutputStream

import java.io.ByteArrayInputStream

import java.io.File

import java.io.IOException
import java.net.Inet4Address
import java.net.NetworkInterface
import java.net.SocketException
import java.net.URLEncoder

import java.text.SimpleDateFormat

import java.util.*

import java.util.concurrent.ExecutorService

import java.util.concurrent.Executors

import java.util.concurrent.RejectedExecutionException

import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicLong

import kotlin.math.abs

import kotlin.math.roundToInt

import kotlin.math.sqrt

// 引入 Rokid 官方 CXR-L (Cross Reality Link) 标准跨端协同开发包

import com.rokid.cxr.link.CXRLink

import com.rokid.cxr.link.callbacks.ICXRLinkCbk

import com.rokid.cxr.link.callbacks.IImageStreamCbk

import com.rokid.cxr.link.utils.CxrDefs

import com.rokid.cxr.link.utils.GlassInfo

import com.rokid.sprite.aiapp.externalapp.auth.AuthResult

import com.rokid.sprite.aiapp.externalapp.auth.AuthorizationHelper

import com.rokid.sprite.aiapp.externalapp.auth.GlassPermission

class MainActivity : AppCompatActivity(), TextToSpeech.OnInitListener {

    private lateinit var binding: ActivityMainBinding

    private lateinit var workExecutor: ExecutorService

    private lateinit var realtimeCloudExecutor: ExecutorService

    private lateinit var thumbnailExecutor: ExecutorService

    private val faceDetector: FaceDetector by lazy {

        FaceDetection.getClient(

            FaceDetectorOptions.Builder()

                .setPerformanceMode(FaceDetectorOptions.PERFORMANCE_MODE_ACCURATE)

                .setLandmarkMode(FaceDetectorOptions.LANDMARK_MODE_NONE)

                .setContourMode(FaceDetectorOptions.CONTOUR_MODE_NONE)

                .setClassificationMode(FaceDetectorOptions.CLASSIFICATION_MODE_NONE)

                .setMinFaceSize(0.08f)

                .build()

        )

    }

    private val sensitiveFaceDetector: FaceDetector by lazy {

        FaceDetection.getClient(

            FaceDetectorOptions.Builder()

                .setPerformanceMode(FaceDetectorOptions.PERFORMANCE_MODE_ACCURATE)

                .setLandmarkMode(FaceDetectorOptions.LANDMARK_MODE_NONE)

                .setContourMode(FaceDetectorOptions.CONTOUR_MODE_NONE)

                .setClassificationMode(FaceDetectorOptions.CLASSIFICATION_MODE_NONE)

                .setMinFaceSize(0.04f)

                .build()

        )

    }

    private val videoFaceDetector: FaceDetector by lazy {

        FaceDetection.getClient(

            FaceDetectorOptions.Builder()

                .setPerformanceMode(FaceDetectorOptions.PERFORMANCE_MODE_ACCURATE)

                .setLandmarkMode(FaceDetectorOptions.LANDMARK_MODE_NONE)

                .setContourMode(FaceDetectorOptions.CONTOUR_MODE_NONE)

                .setClassificationMode(FaceDetectorOptions.CLASSIFICATION_MODE_NONE)

                .setMinFaceSize(0.04f)

                .enableTracking()

                .build()

        )

    }

    private var realtimeFaceDetector: FaceDetector? = null

    private val lookbackFaceDetectorLock = Any()

    private var lookbackFaceDetector: FaceDetector? = null

    private var currentRtmpPreviewBitmap: Bitmap? = null

    private var lastRealtimeFaceDetectAt = 0L

    @Volatile private var isRtmpPreviewRenderRunning = false

    @Volatile private var latestRealtimeOverlaySnapshot: RealtimeOverlaySnapshot? = null

    

    // Rokid CXR-L 核心链路管理器与最新视频帧缓存

    private var cxrLink: CXRLink? = null

    private var cxrAuthToken: String? = null

    @Volatile private var isCxrServiceConnected = false

    @Volatile private var isGlassWirelessConnected = false

    @Volatile private var pendingGlassCapture = false

    @Volatile private var activeCaptureTaskId: String? = null

    @Volatile private var timedOutCaptureTaskId: String? = null

    @Volatile private var timedOutCaptureAcceptUntil = 0L

    @Volatile private var activeCaptureRequestStartedAt = 0L

    @Volatile private var activeCaptureRequestWidth = 0

    @Volatile private var activeCaptureRequestHeight = 0

    @Volatile private var activeCaptureRequestQuality = 0

    @Volatile private var activeCaptureTimeoutMs = GLASS_CAPTURE_TIMEOUT_MS

    @Volatile private var latestFrameBytes: ByteArray? = null

    @Volatile private var capturedFrameBytes: ByteArray? = null // 用于缓存抓拍那一刻的图片数据，防止网络延迟后流画面更新导致裁剪错位

    @Volatile private var lastLocalFaceCrop: Bitmap? = null

    @Volatile private var isMatchingRequestRunning = false

    @Volatile private var lastExternalCaptureTriggerAt = 0L

    

    // 缓存当前正在对比的 Bitmap 实例以防内存溢出与异步翻页冲突

    private var currentLiveFace: Bitmap? = null

    private var currentSystemFace: Bitmap? = null

    // Rokid 官方双目 AR 防抖平视投影显示窗口 (用于在眼镜端投射半透明卡片)

    private var arPresentation: CxrArPresentation? = null

    

    // 缓存多人匹配核验的结果列表以及当前显示的专家索引 (多人轮播核心状态)

    private val matchedExpertsList = ArrayList<ExpertInfo>()

    private val realtimeExpertsByTrack = linkedMapOf<Long, List<ExpertInfo>>()

    private val realtimeRecordLock = Any()

    private val realtimeSavedExpertAt = mutableMapOf<String, Long>()

    private var currentDisplayIndex = 0

    private val recognitionRecords = Collections.synchronizedList(mutableListOf<RecognitionRecord>())

    private val sharedRecognitionRecords = Collections.synchronizedList(mutableListOf<SharedRecognitionRecord>())

    private val deletedSharedRecordIds = Collections.synchronizedSet(mutableSetOf<String>())

    private val deletedSharedRecordTimestamps = Collections.synchronizedMap(mutableMapOf<String, Long>())

    private val sharedOriginalCacheInFlight = Collections.synchronizedSet(mutableSetOf<String>())

    private var galleryPreviewPhotos: List<GalleryPhoto> = emptyList()

    private val selectedGalleryPhotoKeys = Collections.synchronizedSet(mutableSetOf<String>())

    private val processedGalleryPhotoKeys = Collections.synchronizedSet(mutableSetOf<String>())

    @Volatile private var isGalleryPreviewLoading = false

    private var isHandlingBottomNavSelection = false

    private var isUpdatingBottomNavSelection = false

    private var galleryPullStartY = 0f

    private var isGalleryPulling = false

    @Volatile private var isGalleryRefreshing = false

    private val galleryBatchLock = Any()

    @Volatile private var isGalleryBatchRunning = false

    @Volatile private var galleryBatchFaceCount = 0

    @Volatile private var galleryBatchExpertCount = 0

    private var activeGalleryBatchId = 0L

    private var activeGalleryBatchTotal = 0

    private val activeGalleryBatchRecordIds = mutableSetOf<String>()

    private val completedGalleryBatchRecordIds = mutableSetOf<String>()

    private var videoPreviewItems: List<GalleryVideo> = emptyList()

    private val selectedVideoKeys = Collections.synchronizedSet(mutableSetOf<String>())

    @Volatile private var isVideoPreviewLoading = false

    @Volatile private var isVideoRecognitionRunning = false

    @Volatile private var activeVideoBatchId = 0L

    private var videoPullStartY = 0f

    private var isVideoPulling = false

    @Volatile private var isVideoRefreshing = false

    @Volatile private var isRealtimeStreamRunning = false

    @Volatile private var isRealtimeRecognitionPageActive = false

    @Volatile private var realtimeStreamStopRequested = false

    @Volatile private var activeRealtimeStreamRunId = 0L

    @Volatile private var latestRtmpReceiverSnapshot = EmbeddedRtmpReceiver.Snapshot()

    private var isRtmpReceiverBroadcastRegistered = false

    @Volatile private var isRtmpPreviewFaceDetectionRunning = false

    @Volatile private var rtmpPreviewFaceDetectionStartedAt = 0L

    @Volatile private var rtmpPreviewFaceDetectionToken = 0L

    private val realtimeRecognitionSession = AtomicLong(0L)

    private val rtmpPreviewFrameDispatchLock = Any()

    private var pendingRtmpPreviewFrame: RtmpPreviewFramePacket? = null

    @Volatile private var isRtmpPreviewFrameDispatchPosted = false

    @Volatile private var latestRtmpPreviewFrameIndex = 0L

    @Volatile private var latestRtmpPreviewFrameBytes = 0

    @Volatile private var latestRtmpPreviewFrameWidth = 0

    @Volatile private var latestRtmpPreviewFrameHeight = 0

    @Volatile private var lastRtmpPreviewFrameReceivedAt = 0L

    @Volatile private var lastRtmpPreviewFrameRenderedAt = 0L

    @Volatile private var lastRtmpPreviewRenderedFrameIndex = 0L

    @Volatile private var rtmpPreviewRenderStartedAt = 0L

    @Volatile private var lastRtmpPreviewHealthLogAt = 0L

    @Volatile private var lastRtmpPreviewHealthLogKey = ""

    @Volatile private var latestRealtimeFaceCount = -1

    @Volatile private var latestRealtimeValidFaceCount = -1

    @Volatile private var latestRealtimeUploadableFaceCount = -1

    @Volatile private var lastRealtimeDetectAt = 0L

    @Volatile private var lastRealtimeDetectFrame = 0L

    @Volatile private var lastRealtimeDetectDetectedCount = -1

    @Volatile private var lastRealtimeDetectValidCount = -1

    @Volatile private var lastRealtimeDetectUploadableCount = -1

    @Volatile private var lastRealtimeDetectWaitingCount = -1

    @Volatile private var lastRealtimeDetectLowQualityCount = -1

    @Volatile private var lastRealtimeDetectCostMs = -1L

    @Volatile private var lastRealtimeEvaluateCostMs = -1L

    @Volatile private var lastRealtimeDetectBitmapWidth = 0

    @Volatile private var lastRealtimeDetectBitmapHeight = 0

    @Volatile private var lastRealtimeDetectBytes = 0

    @Volatile private var lastRealtimeCloudCompletedAt = 0L

    @Volatile private var lastRealtimeCloudTrackId = 0L

    @Volatile private var lastRealtimeCloudFrame = 0L

    @Volatile private var lastRealtimeCloudResult = "none"

    @Volatile private var lastRealtimeCloudCostMs = -1L

    @Volatile private var lastRealtimeCloudMessage = ""

    private val realtimeTrackLock = Any()

    private val realtimePersonTracks = mutableListOf<RealtimePersonTrack>()

    private val realtimeLookbackLock = Any()

    private val realtimeLookbackFrames = ArrayDeque<RealtimeLookbackFrame>()

    private val realtimeCloudEventLines = ArrayDeque<String>()

    private var realtimeTrackSequence = 0L

    @Volatile private var activeRealtimeCloudRequestCount = 0

    @Volatile private var lastRealtimeCloudRequestAt = 0L

    private val realtimeCloudBudgetLock = Any()

    private val realtimeCloudHttpRequestStarts = ArrayDeque<Long>()

    private val realtimeTrackLastRescueAt = mutableMapOf<Long, Long>()

    @Volatile private var activeRealtimeCloudHttpRequestCount = 0

    @Volatile private var lastRealtimeRescueHttpAt = 0L

    @Volatile private var lastRealtimeCloudBudgetLogAt = 0L

    @Volatile private var lastRealtimeCloudBudgetLogKey = ""

    private val realtimeRescueLock = Any()

    private val realtimeRescueCandidates = ArrayDeque<RealtimeRescueCandidate>()

    @Volatile private var activeRealtimeRescueRequestCount = 0

    @Volatile private var lastRealtimeNoLocalFaceRescueCandidateAt = 0L

    @Volatile private var lastRealtimeCrowdModeAt = 0L

    @Volatile private var lastRealtimeCrowdModeLogged = false

    @Volatile private var latestRealtimeResultNames = ""

    @Volatile private var latestRealtimeResultAt = 0L

    @Volatile private var latestRealtimeAttemptText = ""

    @Volatile private var latestRealtimeAttemptAt = 0L

    @Volatile private var lastRealtimeFaceLogAt = 0L

    @Volatile private var lastRealtimeLoggedFaceCount = -1

    @Volatile private var lastRealtimeLoggedValidFaceCount = -1

    @Volatile private var lastRealtimeLoggedUploadableFaceCount = -1

    @Volatile private var lastRealtimeLookbackFrameAt = 0L

    @Volatile private var lastRealtimeCloudScheduleWaitLogAt = 0L

    @Volatile private var lastRealtimeCloudScheduleWaitLogKey = ""

    private val rtmpReceiverBroadcastReceiver = object : BroadcastReceiver() {
        override fun onReceive(context: Context?, intent: Intent?) {
            when (intent?.action) {
                RtmpReceiverService.ACTION_STATUS -> {
                    latestRtmpReceiverSnapshot = rtmpSnapshotFromIntent(intent)
                    renderRtmpReceiverSnapshot(latestRtmpReceiverSnapshot)
                }
                RtmpReceiverService.ACTION_LOG -> {
                    val message = intent.getStringExtra(RtmpReceiverService.EXTRA_MESSAGE).orEmpty()
                    val throwableText = intent.getStringExtra(RtmpReceiverService.EXTRA_THROWABLE).orEmpty()
                    if (throwableText.isBlank()) {
                        recordDiagnostic("RTMP接收验证: $message")
                    } else {
                        recordDiagnostic("RTMP接收验证: $message\n${throwableText.lineSequence().take(8).joinToString("\n")}")
                    }
                }
                RtmpReceiverService.ACTION_PREVIEW -> {
                    handleRtmpPreviewFrame(intent)
                }
            }
        }
    }

    // 网络请求与配置

    private val okHttpClient = OkHttpClient()

    private var serverBaseUrl = "http://82.157.244.174"

    private var glassCaptureWidth = DEFAULT_GLASS_CAPTURE_WIDTH

    private var glassCaptureHeight = DEFAULT_GLASS_CAPTURE_HEIGHT

    private var glassCaptureQuality = DEFAULT_GLASS_CAPTURE_QUALITY

    private var soundPromptEnabled = true

    private var recordShareEnabled = true

    private var shareNickname = ""

    private var shareDeviceId = ""

    @Volatile private var sharedRecordSyncRunning = false

    @Volatile private var sharedRecordSyncInFlight = false

    @Volatile private var sharedRecordSyncCursor = 0L

    

    // 语音播报 TTS

    private var tts: TextToSpeech? = null

    private var isTtsInitialized = false

    

    // UI 自动淡出 Handler

    private val mainHandler = Handler(Looper.getMainLooper())

    private val diagnosticTimeFormat = SimpleDateFormat("HH:mm:ss.SSS", Locale.CHINA)

    private val historyTimeFormat = SimpleDateFormat("MM-dd HH:mm", Locale.CHINA)

    private val diagnosticLines = ArrayDeque<String>()

    private val hideArRunnable = Runnable { hideArOverlay() }

    private val glassCaptureTimeoutRunnable = Runnable {

        if (pendingGlassCapture) {

            val timeoutTaskId = activeCaptureTaskId

            timedOutCaptureTaskId = timeoutTaskId

            timedOutCaptureAcceptUntil = System.currentTimeMillis() + LATE_CAPTURE_ACCEPT_MS

            pendingGlassCapture = false

            activeCaptureTaskId = null

            isMatchingRequestRunning = false

            updateRecognitionRecord(timeoutTaskId) {

                it.status = STATUS_FAILED

                it.statusText = "眼镜拍照超时"

                it.errorMessage = "眼镜拍照超时；若照片稍后回传，App 会继续尝试识别"

            }

            recordDiagnostic(

                "抓拍超时: service=$isCxrServiceConnected, glass=$isGlassWirelessConnected, " +

                    "latestFrameBytes=${latestFrameBytes?.size ?: 0}, lateAcceptMs=$LATE_CAPTURE_ACCEPT_MS"

            )

            playResultBeep(success = false)

            updateStatus("眼镜拍照超时，若照片稍后回传将继续识别", isWorking = false)

        }

    }

    private val sharedRecordSyncRunnable = object : Runnable {

        override fun run() {

            if (!sharedRecordSyncRunning || !recordShareEnabled || !isActivityResumed) {

                return

            }

            fetchSharedRecognitionRecords(initialFetch = false)

            mainHandler.postDelayed(this, SHARED_RECORD_POLL_MS)

        }

    }

    override fun onCreate(savedInstanceState: Bundle?) {

        super.onCreate(savedInstanceState)

        binding = ActivityMainBinding.inflate(layoutInflater)

        setContentView(binding.root)

        isRealtimeRecognitionPageActive = binding.mainPage.visibility == View.VISIBLE

        bumpRealtimeRecognitionSession("Activity 创建")

        // 初始化本地语音播报和线程池

        tts = TextToSpeech(this, this)

        workExecutor = Executors.newFixedThreadPool(MAX_PARALLEL_WORKERS)

        realtimeCloudExecutor = Executors.newFixedThreadPool(REALTIME_CROWD_CLOUD_MAX_CONCURRENT_REQUESTS)

        thumbnailExecutor = Executors.newCachedThreadPool()

        loadRecognitionRecords()

        loadProcessedGalleryPhotoKeys()

        markInterruptedRecordsForRetry()

        cleanupExpiredRecognitionRecords()

        loadCaptureParams()

        loadSoundSettings()

        loadShareSettings()

        loadSharedRecognitionRecords()

        setupCaptureParamControls()

        setupSoundSettingsControls()

        setupShareSettingsControls()

        renderHistoryList()

        recordDiagnostic("App启动: ${deviceBrief()} app=${appVersionBrief()}")

        // 1. 申请核心权限

        if (!allPermissionsGranted()) {

            recordDiagnostic("运行时权限未全部授予，开始请求: ${runtimePermissionStatus()}")

            ActivityCompat.requestPermissions(

                this, requiredRuntimePermissions(), REQUEST_CODE_PERMISSIONS

            )

        } else {

            recordDiagnostic("运行时权限已满足: ${runtimePermissionStatus()}")

            requestCxrAuthorizationAndConnect()

        }

        // 2. 绑定配置保存按钮

        binding.btnSaveConfig.setOnClickListener {

            val ipInput = binding.etServerIp.text.toString().trim()

            if (ipInput.isNotEmpty()) {

                serverBaseUrl = ipInput

                Toast.makeText(this, "服务器配置已保存: $serverBaseUrl", Toast.LENGTH_SHORT).show()

                recordDiagnostic("服务器地址已保存: $serverBaseUrl")

            }

            requestCxrAuthorizationAndConnect()

            showMainPage()

        }

        // 手机屏幕上的手动抓拍比对按钮

        binding.btnCapture.setOnClickListener {

            recordDiagnostic("用户点击现场抓拍比对")

            takePhotoAndMatch()

        }

        binding.btnMainStartRtmpReceiver.setOnClickListener {

            startEmbeddedRtmpReceiver()

        }

        binding.btnMainStopRtmpReceiver.setOnClickListener {

            stopEmbeddedRtmpReceiver("用户在主页面停止实时视频")

        }

        binding.btnMainCopyRtmpPushAddress.setOnClickListener {

            copyRtmpPushAddressToClipboard()

        }

        binding.btnOpenSettings.setOnClickListener {

            showSettingsPage()

        }

        binding.btnOpenHistory.setOnClickListener {

            showHistoryPage()

        }

        binding.btnBackMain.setOnClickListener {

            showMainPage()

        }

        binding.btnBackFromHistory.setOnClickListener {

            showMainPage()

        }

        binding.bottomNav.setOnItemSelectedListener { item ->

            if (isUpdatingBottomNavSelection) {

                return@setOnItemSelectedListener true

            }

            isHandlingBottomNavSelection = true

            try {

                when (item.itemId) {

                    R.id.navCapture -> showMainPage()

                    R.id.navGallery -> showGalleryPage()

                    R.id.navVideo -> showVideoPage()

                    R.id.navHistory -> showHistoryPage()

                    R.id.navSettings -> showSettingsPage()

                    else -> return@setOnItemSelectedListener false

                }

            } finally {

                isHandlingBottomNavSelection = false

            }

            true

        }

        binding.btnStartGalleryRecognition.setOnClickListener {

            startGalleryLatestRecognition()

        }

        setupGalleryPullRefresh()

        setupVideoPullRefresh()

        binding.btnStartVideoRecognition.setOnClickListener {

            startVideoRecognition()

        }

        binding.btnStartRealtimeStreamTest.setOnClickListener {

            startRealtimeStreamTest()

        }

        binding.btnStopRealtimeStreamTest.setOnClickListener {

            stopRealtimeStreamTest("用户点击停止")

        }

        binding.btnStartRtmpReceiver.setOnClickListener {

            restartEmbeddedRtmpReceiver()

        }

        binding.btnStopRtmpReceiver.setOnClickListener {

            stopEmbeddedRtmpReceiver("用户点击停止")

        }

        binding.btnCopyRtmpPushAddress.setOnClickListener {

            copyRtmpPushAddressToClipboard()

        }

        binding.btnPickVideo.setOnClickListener {

            launchVideoPicker()

        }

        binding.btnPickGalleryImage.setOnClickListener {

            launchImagePicker()

        }

        binding.btnCopyDiagnostics.setOnClickListener {

            copyDiagnosticsToClipboard()

        }

        binding.btnClearFailedHistory.setOnClickListener {

            clearFailedHistoryRecords()

        }

        updateRtmpReceiverAddressHint()

        registerRtmpReceiverBroadcasts()

        ensureRealtimeReceiverRunningForMainPage()

    }

    private var isActivityResumed = false

    override fun onResume() {

        super.onResume()

        isActivityResumed = true

        latestRtmpReceiverSnapshot = RtmpReceiverService.latestSnapshot

        updateRtmpReceiverAddressHint()

        renderRtmpReceiverSnapshot(latestRtmpReceiverSnapshot)

        startSharedRecordSync()

        recordDiagnostic("Activity 状态变更为: RESUMED")

    }

    override fun onPause() {

        super.onPause()

        isActivityResumed = false

        stopSharedRecordSync()

        stopRealtimeStreamTest("Activity 暂停")

        recordDiagnostic("Activity 状态变更为: PAUSED")

    }

    @Deprecated("Use OnBackPressedDispatcher when the project adopts AndroidX activity callbacks.")

    override fun onBackPressed() {

        if (binding.settingsPage.visibility == View.VISIBLE ||

            binding.historyPage.visibility == View.VISIBLE ||

            binding.galleryPage.visibility == View.VISIBLE ||

            binding.videoPage.visibility == View.VISIBLE

        ) {

            showMainPage()

        } else {

            super.onBackPressed()

        }

    }

    private fun showSettingsPage() {

        try {

            isRealtimeRecognitionPageActive = false

            clearRealtimeRecognitionCandidates("切换到设置与诊断页面")

            updateRtmpReceiverAddressHint()

            binding.mainPage.visibility = View.GONE

            binding.galleryPage.visibility = View.GONE

            binding.videoPage.visibility = View.GONE

            binding.historyPage.visibility = View.GONE

            binding.settingsPage.visibility = View.VISIBLE

            updateBottomNavSelection(PAGE_SETTINGS)

            recordDiagnostic("切换到设置与诊断页面")

        } catch (e: Exception) {

            handlePageSwitchFailure("设置与诊断", e)

        }

    }

    private fun showGalleryPage() {

        try {

            isRealtimeRecognitionPageActive = false

            clearRealtimeRecognitionCandidates("切换到图库识别页面")

            stopRealtimeStreamTest("切换到图库识别页面")

            binding.mainPage.visibility = View.GONE

            binding.settingsPage.visibility = View.GONE

            binding.videoPage.visibility = View.GONE

            binding.historyPage.visibility = View.GONE

            binding.galleryPage.visibility = View.VISIBLE

            updateBottomNavSelection(PAGE_GALLERY)

            ensureGalleryPreviewLoaded()

            recordDiagnostic("切换到图库识别页面")

        } catch (e: Exception) {

            handlePageSwitchFailure("图库识别", e)

        }

    }

    private fun showVideoPage() {

        try {

            isRealtimeRecognitionPageActive = false

            clearRealtimeRecognitionCandidates("切换到视频识别页面")

            stopRealtimeStreamTest("切换到视频识别页面")

            binding.mainPage.visibility = View.GONE

            binding.galleryPage.visibility = View.GONE

            binding.settingsPage.visibility = View.GONE

            binding.historyPage.visibility = View.GONE

            binding.videoPage.visibility = View.VISIBLE

            updateBottomNavSelection(PAGE_VIDEO)

            ensureVideoPreviewLoaded()

            recordDiagnostic("切换到视频识别页面")

        } catch (e: Exception) {

            handlePageSwitchFailure("视频识别", e)

        }

    }

    private fun showHistoryPage() {

        try {

            isRealtimeRecognitionPageActive = false

            stopRealtimeStreamTest("切换到识别记录页面")

            cleanupExpiredRecognitionRecords()

            renderHistoryList()

            binding.mainPage.visibility = View.GONE

            binding.galleryPage.visibility = View.GONE

            binding.videoPage.visibility = View.GONE

            binding.settingsPage.visibility = View.GONE

            binding.historyPage.visibility = View.VISIBLE

            updateBottomNavSelection(PAGE_HISTORY)

            recordDiagnostic("切换到识别记录页面")

            maybeStartRealtimeCloudRecognition()

        } catch (e: Exception) {

            handlePageSwitchFailure("识别记录", e)

        }

    }

    private fun showMainPage() {

        try {

            isRealtimeRecognitionPageActive = true

            stopRealtimeStreamTest("返回识别主页面")

            binding.galleryPage.visibility = View.GONE

            binding.videoPage.visibility = View.GONE

            binding.settingsPage.visibility = View.GONE

            binding.historyPage.visibility = View.GONE

            binding.mainPage.visibility = View.VISIBLE

            updateBottomNavSelection(PAGE_CAPTURE)

            ensureRealtimeReceiverRunningForMainPage()

            recordDiagnostic("返回识别主页面")

        } catch (e: Exception) {

            recordDiagnostic("返回识别主页面异常", e)

        }

    }

    private fun updateBottomNavSelection(page: String) {

        val itemId = when (page) {

            PAGE_GALLERY -> R.id.navGallery

            PAGE_VIDEO -> R.id.navVideo

            PAGE_HISTORY -> R.id.navHistory

            PAGE_SETTINGS -> R.id.navSettings

            else -> R.id.navCapture

        }

        if (isHandlingBottomNavSelection || isUpdatingBottomNavSelection) {

            return

        }

        if (binding.bottomNav.selectedItemId != itemId) {

            isUpdatingBottomNavSelection = true

            try {

                binding.bottomNav.selectedItemId = itemId

            } finally {

                isUpdatingBottomNavSelection = false

            }

        }

    }

    private fun handlePageSwitchFailure(pageName: String, throwable: Throwable) {

        recordDiagnostic("切换${pageName}页面异常", throwable)

        try {

            binding.galleryPage.visibility = View.GONE

            binding.videoPage.visibility = View.GONE

            binding.settingsPage.visibility = View.GONE

            binding.historyPage.visibility = View.GONE

            stopRealtimeStreamTest("页面异常恢复")

            binding.mainPage.visibility = View.VISIBLE

            updateBottomNavSelection(PAGE_CAPTURE)

        } catch (e: Exception) {

            recordDiagnostic("页面异常恢复失败", e)

        }

        Toast.makeText(this, "${pageName}页面打开失败，已记录诊断日志", Toast.LENGTH_SHORT).show()

    }

    private fun setupCaptureParamControls() {

        setCaptureParamFields(glassCaptureWidth, glassCaptureHeight, glassCaptureQuality)

        binding.btnPresetCaptureBalanced.setOnClickListener {

            applyCapturePreset(1920, 1080, 92, "稳定")

        }

        binding.btnPresetCaptureSharp.setOnClickListener {

            applyCapturePreset(2560, 1440, 92, "接近官方")

        }

        binding.btnPresetCaptureHigh.setOnClickListener {

            applyCapturePreset(3024, 4032, 90, "官方尺寸探测")

        }

        binding.btnSaveCaptureParams.setOnClickListener {

            saveCaptureParamsFromFields(showToast = true)

        }

    }

    private fun loadSoundSettings() {

        soundPromptEnabled = getSharedPreferences(SOUND_PREFS_NAME, Context.MODE_PRIVATE)

            .getBoolean(SOUND_PREF_ENABLED, true)

    }

    private fun setupSoundSettingsControls() {

        binding.switchSoundPrompt.isChecked = soundPromptEnabled

        binding.switchSoundPrompt.setOnCheckedChangeListener { _, isChecked ->

            soundPromptEnabled = isChecked

            getSharedPreferences(SOUND_PREFS_NAME, Context.MODE_PRIVATE)

                .edit()

                .putBoolean(SOUND_PREF_ENABLED, isChecked)

                .apply()

            if (!isChecked) {

                tts?.stop()

            }

            val text = if (isChecked) "声音提示已开启" else "声音提示已关闭"

            Toast.makeText(this, text, Toast.LENGTH_SHORT).show()

            recordDiagnostic("声音提示开关已变更: enabled=$isChecked")

        }

    }

    private fun loadShareSettings() {

        val prefs = getSharedPreferences(SHARE_PREFS_NAME, Context.MODE_PRIVATE)

        recordShareEnabled = prefs.getBoolean(SHARE_PREF_ENABLED, true)

        shareNickname = prefs.getString(SHARE_PREF_NICKNAME, "")?.trim().orEmpty()

        shareDeviceId = prefs.getString(SHARE_PREF_DEVICE_ID, "")?.trim().orEmpty()

        if (shareDeviceId.isBlank()) {

            shareDeviceId = UUID.randomUUID().toString()

            prefs.edit().putString(SHARE_PREF_DEVICE_ID, shareDeviceId).apply()

        }

        val deletedIds = prefs.getStringSet(SHARE_PREF_DELETED_IDS, emptySet()) ?: emptySet()

        val now = System.currentTimeMillis()

        val activeDeletedIds = mutableSetOf<String>()

        val activeDeletedTimestamps = mutableMapOf<String, Long>()

        var shouldRewriteDeletedIds = false

        deletedIds.forEach { entry ->

            val separatorIndex = entry.lastIndexOf(':')

            val shareId = if (separatorIndex > 0) entry.substring(0, separatorIndex) else entry

            if (separatorIndex <= 0) {

                shouldRewriteDeletedIds = true

            }

            val deletedAt = if (separatorIndex > 0) {

                entry.substring(separatorIndex + 1).toLongOrNull() ?: now

            } else {

                now

            }

            if (shareId.isNotBlank() && now - deletedAt <= SHARED_DELETED_ID_RETENTION_MS) {

                activeDeletedIds.add(shareId)

                activeDeletedTimestamps[shareId] = deletedAt

            } else if (shareId.isNotBlank()) {

                shouldRewriteDeletedIds = true

            }

        }

        synchronized(deletedSharedRecordIds) {

            deletedSharedRecordIds.clear()

            deletedSharedRecordIds.addAll(activeDeletedIds)

        }

        synchronized(deletedSharedRecordTimestamps) {

            deletedSharedRecordTimestamps.clear()

            deletedSharedRecordTimestamps.putAll(activeDeletedTimestamps)

        }

        if (shouldRewriteDeletedIds) {

            saveDeletedSharedRecordIds()

        }

    }

    private fun setupShareSettingsControls() {

        binding.switchRecordSharing.isChecked = recordShareEnabled

        binding.etShareNickname.setText(shareNickname)

        binding.switchRecordSharing.setOnCheckedChangeListener { _, isChecked ->

            recordShareEnabled = isChecked

            getSharedPreferences(SHARE_PREFS_NAME, Context.MODE_PRIVATE)

                .edit()

                .putBoolean(SHARE_PREF_ENABLED, isChecked)

                .apply()

            if (isChecked) {

                startSharedRecordSync()

            } else {

                stopSharedRecordSync()

            }

            val text = if (isChecked) "记录共享已开启" else "记录共享已关闭"

            Toast.makeText(this, text, Toast.LENGTH_SHORT).show()

            recordDiagnostic("记录共享开关已变更: enabled=$isChecked")

        }

        binding.etShareNickname.addTextChangedListener(object : TextWatcher {

            override fun beforeTextChanged(s: CharSequence?, start: Int, count: Int, after: Int) = Unit

            override fun onTextChanged(s: CharSequence?, start: Int, before: Int, count: Int) = Unit

            override fun afterTextChanged(s: Editable?) {

                shareNickname = s?.toString()?.trim().orEmpty()

                getSharedPreferences(SHARE_PREFS_NAME, Context.MODE_PRIVATE)

                    .edit()

                    .putString(SHARE_PREF_NICKNAME, shareNickname)

                    .apply()

            }

        })

    }

    private fun shareDisplayNickname(): String {

        return shareNickname.trim().ifBlank { DEFAULT_SHARE_NICKNAME }

    }

    private fun saveDeletedSharedRecordIds() {

        pruneDeletedSharedRecordIds()

        val snapshot = synchronized(deletedSharedRecordTimestamps) {

            deletedSharedRecordTimestamps

                .map { (shareId, deletedAt) -> "$shareId:$deletedAt" }

                .toSet()

        }

        getSharedPreferences(SHARE_PREFS_NAME, Context.MODE_PRIVATE)

            .edit()

            .putStringSet(SHARE_PREF_DELETED_IDS, snapshot)

            .apply()

    }

    private fun pruneDeletedSharedRecordIds(now: Long = System.currentTimeMillis()): Boolean {

        val expiredIds = mutableListOf<String>()

        synchronized(deletedSharedRecordTimestamps) {

            val iterator = deletedSharedRecordTimestamps.entries.iterator()

            while (iterator.hasNext()) {

                val entry = iterator.next()

                if (now - entry.value > SHARED_DELETED_ID_RETENTION_MS) {

                    expiredIds.add(entry.key)

                    iterator.remove()

                }

            }

        }

        if (expiredIds.isNotEmpty()) {

            synchronized(deletedSharedRecordIds) {

                deletedSharedRecordIds.removeAll(expiredIds.toSet())

            }

        }

        return expiredIds.isNotEmpty()

    }

    private fun loadCaptureParams() {

        val prefs = getSharedPreferences(CAPTURE_PREFS_NAME, Context.MODE_PRIVATE)

        val savedWidth = prefs.getInt(CAPTURE_PREF_WIDTH, DEFAULT_GLASS_CAPTURE_WIDTH)

        val savedHeight = prefs.getInt(CAPTURE_PREF_HEIGHT, DEFAULT_GLASS_CAPTURE_HEIGHT)

        val savedQuality = prefs.getInt(CAPTURE_PREF_QUALITY, DEFAULT_GLASS_CAPTURE_QUALITY)

        if (isValidCaptureParams(savedWidth, savedHeight, savedQuality)) {

            glassCaptureWidth = savedWidth

            glassCaptureHeight = savedHeight

            glassCaptureQuality = savedQuality

            return

        }

        glassCaptureWidth = DEFAULT_GLASS_CAPTURE_WIDTH

        glassCaptureHeight = DEFAULT_GLASS_CAPTURE_HEIGHT

        glassCaptureQuality = DEFAULT_GLASS_CAPTURE_QUALITY

        prefs.edit()

            .putInt(CAPTURE_PREF_WIDTH, glassCaptureWidth)

            .putInt(CAPTURE_PREF_HEIGHT, glassCaptureHeight)

            .putInt(CAPTURE_PREF_QUALITY, glassCaptureQuality)

            .apply()

        recordDiagnostic(

            "已重置不稳定眼镜拍照参数: saved=${savedWidth}x$savedHeight q=$savedQuality, current=${captureParamsBrief()}"

        )

    }

    private fun setCaptureParamFields(width: Int, height: Int, quality: Int) {

        binding.etCaptureWidth.setText(width.toString())

        binding.etCaptureHeight.setText(height.toString())

        binding.etCaptureQuality.setText(quality.toString())

    }

    private fun applyCapturePreset(width: Int, height: Int, quality: Int, label: String) {

        setCaptureParamFields(width, height, quality)

        if (saveCaptureParamsFromFields(showToast = false)) {

            Toast.makeText(this, "已应用$label: ${captureParamsBrief()}", Toast.LENGTH_SHORT).show()

        }

    }

    private fun saveCaptureParamsFromFields(showToast: Boolean): Boolean {

        val width = binding.etCaptureWidth.text.toString().trim().toIntOrNull()

        val height = binding.etCaptureHeight.text.toString().trim().toIntOrNull()

        val quality = binding.etCaptureQuality.text.toString().trim().toIntOrNull()

        if (width == null || height == null || quality == null) {

            Toast.makeText(this, "请完整填写宽、高、质量", Toast.LENGTH_SHORT).show()

            return false

        }

        if (!isValidCaptureParams(width, height, quality)) {

            Toast.makeText(

                this,

                "参数范围: 宽高 $CAPTURE_MIN_SIZE-$CAPTURE_MAX_SIZE，质量 $CAPTURE_MIN_QUALITY-$CAPTURE_MAX_QUALITY；4032x3024 q90 实测易超时",

                Toast.LENGTH_SHORT

            ).show()

            return false

        }

        glassCaptureWidth = width

        glassCaptureHeight = height

        glassCaptureQuality = quality

        getSharedPreferences(CAPTURE_PREFS_NAME, Context.MODE_PRIVATE)

            .edit()

            .putInt(CAPTURE_PREF_WIDTH, width)

            .putInt(CAPTURE_PREF_HEIGHT, height)

            .putInt(CAPTURE_PREF_QUALITY, quality)

            .apply()

        recordDiagnostic("眼镜拍照参数已应用: ${captureParamsBrief()}")

        if (quality > DEFAULT_GLASS_CAPTURE_QUALITY) {

            recordDiagnostic("高质量拍照参数测试: q=$quality，实测 q95 可能导致 CXR-L 无图片回调")

        }

        if (showToast) {

            val message = if (quality > DEFAULT_GLASS_CAPTURE_QUALITY) {

                "拍照参数已应用: ${captureParamsBrief()}，高质量档仅建议测试"

            } else {

                "拍照参数已应用: ${captureParamsBrief()}"

            }

            Toast.makeText(this, message, Toast.LENGTH_SHORT).show()

        }

        return true

    }

    private fun isValidCaptureParams(width: Int, height: Int, quality: Int): Boolean {

        return width in CAPTURE_MIN_SIZE..CAPTURE_MAX_SIZE &&

            height in CAPTURE_MIN_SIZE..CAPTURE_MAX_SIZE &&

            quality in CAPTURE_MIN_QUALITY..CAPTURE_MAX_QUALITY &&

            !isKnownUnstableCaptureParams(width, height, quality)

    }

    private fun isKnownUnstableCaptureParams(width: Int, height: Int, quality: Int): Boolean {

        return width == 4032 && height == 3024 && quality >= 90

    }

    private fun captureParamsBrief(): String {

        return "${glassCaptureWidth}x$glassCaptureHeight q=$glassCaptureQuality"

    }

    private fun startGalleryLatestRecognition() {

        if (!galleryImagePermissionsGranted()) {

            recordDiagnostic("图库权限未满足，开始请求: ${galleryPermissionStatus()}")

            ActivityCompat.requestPermissions(

                this,

                galleryImagePermissions(),

                REQUEST_CODE_GALLERY_IMAGES

            )

            return

        }

        if (galleryPreviewPhotos.isEmpty()) {

            loadGalleryPreview(force = true)

            Toast.makeText(this, "正在加载图库预览，请确认勾选后再开始识别", Toast.LENGTH_SHORT).show()

            return

        }

        val selectedKeys = synchronized(selectedGalleryPhotoKeys) { selectedGalleryPhotoKeys.toSet() }

        val selectedPhotos = galleryPreviewPhotos.filter { galleryPhotoKey(it) in selectedKeys }

        if (selectedPhotos.isEmpty()) {

            updateGalleryStatus("请至少勾选 1 张照片后再开始识别")

            Toast.makeText(this, "请先勾选要识别的照片", Toast.LENGTH_SHORT).show()

            return

        }

        updateGalleryStatus("已开始 ${selectedPhotos.size} 张照片并行识别，可在记录页查看结果")

        val batchId = startGalleryBatchProgress(selectedPhotos.size)

        isGalleryBatchRunning = true

        recordDiagnostic("用户启动图库照片识别: selected=${selectedPhotos.size}, loaded=${galleryPreviewPhotos.size}, permission=${galleryPermissionStatus()}")

        selectedPhotos.forEachIndexed { index, photo ->

            executeWorker("处理图库照片 ${index + 1}/${selectedPhotos.size}") {

                processGalleryPhoto(index + 1, selectedPhotos.size, photo, batchId)

            }

        }

    }

    private fun startGalleryBatchProgress(total: Int): Long {

        val batchId = System.currentTimeMillis()

        synchronized(galleryBatchLock) {

            activeGalleryBatchId = batchId

            activeGalleryBatchTotal = total

            activeGalleryBatchRecordIds.clear()

            completedGalleryBatchRecordIds.clear()

            galleryBatchFaceCount = 0

            galleryBatchExpertCount = 0

        }

        updateGalleryBatchProgressUi(batchId, completed = 0, total = total, finished = false)

        recordDiagnostic("图库批量识别进度开始: batchId=$batchId, total=$total")

        return batchId

    }

    private fun registerGalleryBatchRecord(batchId: Long, recordId: String) {

        var completed = 0

        var total = 0

        var accepted = false

        synchronized(galleryBatchLock) {

            if (activeGalleryBatchId == batchId) {

                activeGalleryBatchRecordIds.add(recordId)

                completed = completedGalleryBatchRecordIds.size

                total = activeGalleryBatchTotal

                accepted = true

            }

        }

        if (accepted) {

            updateGalleryBatchProgressUi(batchId, completed, total, finished = false)

            recordDiagnostic("图库批量记录加入进度: batchId=$batchId, recordId=$recordId")

        }

    }

    private fun updateGalleryBatchProgressForRecord(recordId: String, status: String) {

        if (!isTerminalRecognitionStatus(status)) {

            return

        }

        var batchId = 0L

        var completed = 0

        var total = 0

        var shouldUpdate = false

        var finished = false

        synchronized(galleryBatchLock) {

            if (recordId in activeGalleryBatchRecordIds && recordId !in completedGalleryBatchRecordIds) {

                completedGalleryBatchRecordIds.add(recordId)

                batchId = activeGalleryBatchId

                completed = completedGalleryBatchRecordIds.size

                total = activeGalleryBatchTotal

                finished = total > 0 && completed >= total

                shouldUpdate = true

            }

        }

        if (shouldUpdate) {

            updateGalleryBatchProgressUi(batchId, completed, total, finished)

            recordDiagnostic(

                "图库批量识别进度更新: batchId=$batchId, recordId=$recordId, " +

                    "status=$status, completed=$completed/$total"

            )

        }

    }

        private fun updateGalleryBatchProgressUi(batchId: Long, completed: Int, total: Int, finished: Boolean) {
        runOnUiThread {
            synchronized(galleryBatchLock) {
                if (activeGalleryBatchId != batchId) {
                    return@runOnUiThread
                }
            }
            binding.galleryProgressPanel.visibility = View.VISIBLE
            binding.galleryBatchProgress.max = total.coerceAtLeast(1)
            binding.galleryBatchProgress.progress = completed.coerceAtMost(total.coerceAtLeast(1))
            
            val resultText = if (finished) {
                val outcome = when {
                    galleryBatchFaceCount == 0 -> "未识别到人脸"
                    galleryBatchExpertCount == 0 -> "未匹配到专家"
                    else -> "发现专家 ${galleryBatchExpertCount} 人"
                }
                "识别完成: $outcome ($completed/$total)"
            } else {
                "正在识别 $completed/$total"
            }
            binding.tvGalleryProgress.text = resultText

            if (finished) {
                isGalleryBatchRunning = false
                renderGalleryPreview(galleryPreviewPhotos)
                updateGallerySelectionStatus()

                val outcome = when {
                    galleryBatchFaceCount == 0 -> "未识别到人脸"
                    galleryBatchExpertCount == 0 -> "未匹配到专家"
                    else -> "发现专家 ${galleryBatchExpertCount} 人"
                }
                updateGalleryStatus("批量识别完成: $outcome")
                Toast.makeText(this@MainActivity, "图库识别完成: $outcome", Toast.LENGTH_SHORT).show()

                if (galleryBatchExpertCount > 0) {
                    playResultBeep(success = true)
                    speakOut("图库识别完成，发现${galleryBatchExpertCount}名专家")
                } else {
                    playResultBeep(success = false)
                    speakOut("图库识别完成，$outcome")
                }

                mainHandler.postDelayed({
                    synchronized(galleryBatchLock) {
                        if (activeGalleryBatchId != batchId ||
                            completedGalleryBatchRecordIds.size < activeGalleryBatchTotal
                        ) {
                            return@postDelayed
                        }
                    }
                    binding.galleryProgressPanel.visibility = View.GONE
                    recordDiagnostic("图库批量识别进度隐藏: batchId=$batchId")
                }, GALLERY_PROGRESS_HIDE_DELAY_MS)
            }
        }
    }

    private fun isTerminalRecognitionStatus(status: String): Boolean {

        return status == STATUS_SUCCESS ||

            status == STATUS_NO_FACE ||

            status == STATUS_NO_MATCH ||

            status == STATUS_FAILED ||

            status == STATUS_INTERRUPTED

    }

    private fun setupGalleryPullRefresh() {

        binding.galleryScroll.setOnTouchListener { _, event ->

            if (isGalleryPreviewLoading || isGalleryRefreshing) {

                return@setOnTouchListener false

            }

            when (event.actionMasked) {

                MotionEvent.ACTION_DOWN -> {

                    galleryPullStartY = event.y

                    isGalleryPulling = binding.galleryScroll.scrollY == 0

                    false

                }

                MotionEvent.ACTION_MOVE -> {

                    if (binding.galleryScroll.scrollY == 0 && event.y - galleryPullStartY > dp(GALLERY_PULL_HINT_DISTANCE_DP)) {

                        isGalleryPulling = true

                        showGalleryRefreshHint("松开刷新")

                    }

                    false

                }

                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {

                    val pullDistance = event.y - galleryPullStartY

                    if (isGalleryPulling && binding.galleryScroll.scrollY == 0 && pullDistance > dp(GALLERY_PULL_REFRESH_DISTANCE_DP)) {

                        setGalleryRefreshing(true)

                        recordDiagnostic("用户下拉刷新图库: pullDistance=${pullDistance.roundToInt()}")

                        loadGalleryPreview(force = true)

                    } else {

                        hideGalleryRefreshHint()

                    }

                    isGalleryPulling = false

                    false

                }

                else -> false

            }

        }

    }

    private fun showGalleryRefreshHint(text: String) {

        binding.tvGalleryRefreshHint.text = text

        binding.tvGalleryRefreshHint.visibility = View.VISIBLE

    }

    private fun hideGalleryRefreshHint() {

        if (!isGalleryRefreshing) {

            binding.tvGalleryRefreshHint.visibility = View.GONE

        }

    }

    private fun setGalleryRefreshing(refreshing: Boolean) {

        isGalleryRefreshing = refreshing

        runOnUiThread {

            if (refreshing) {

                binding.tvGalleryRefreshHint.text = "正在刷新..."

                binding.tvGalleryRefreshHint.visibility = View.VISIBLE

            } else {

                binding.tvGalleryRefreshHint.visibility = View.GONE

            }

        }

    }

    private fun ensureGalleryPreviewLoaded(force: Boolean = false) {

        if (!galleryImagePermissionsGranted()) {

            updateGalleryStatus("需要图库照片权限，点击“开始识别”后授权并加载预览")

            return

        }

        if (!force && galleryPreviewPhotos.isNotEmpty()) {

            updateGallerySelectionStatus()

            return

        }

        loadGalleryPreview(force)

    }

    private fun loadGalleryPreview(force: Boolean = false) {

        if (!galleryImagePermissionsGranted()) {

            setGalleryRefreshing(false)

            ActivityCompat.requestPermissions(

                this,

                galleryImagePermissions(),

                REQUEST_CODE_GALLERY_IMAGES

            )

            return

        }

        if (isGalleryPreviewLoading) {

            updateGalleryStatus("正在加载图库预览...")

            return

        }

        if (!force && galleryPreviewPhotos.isNotEmpty()) {

            setGalleryRefreshing(false)

            updateGallerySelectionStatus()

            return

        }

        val defaultSelectCount = galleryDefaultSelectCount()

        isGalleryPreviewLoading = true

        updateGalleryStatus("正在加载最近照片预览...")

        binding.galleryQueueList.removeAllViews()

        recordDiagnostic("开始加载图库预览: previewLimit=$GALLERY_PREVIEW_SIZE, defaultSelected=$defaultSelectCount")

        executeWorker("读取最近图库照片") {

            val photos = try {

                queryLatestGalleryPhotos(GALLERY_PREVIEW_SIZE)

            } catch (e: Exception) {

                recordDiagnostic("图库照片读取异常: previewLimit=$GALLERY_PREVIEW_SIZE", e)

                runOnUiThread {

                    isGalleryPreviewLoading = false

                    setGalleryRefreshing(false)

                    updateGalleryStatus("图库照片读取失败")

                    Toast.makeText(this, "图库照片读取失败", Toast.LENGTH_SHORT).show()

                }

                return@executeWorker

            }

            if (photos.isEmpty()) {

                recordDiagnostic("图库照片读取为空: previewLimit=$GALLERY_PREVIEW_SIZE")

                runOnUiThread {

                    isGalleryPreviewLoading = false

                    setGalleryRefreshing(false)

                    galleryPreviewPhotos = emptyList()

                    synchronized(selectedGalleryPhotoKeys) { selectedGalleryPhotoKeys.clear() }

                    binding.galleryQueueList.removeAllViews()

                    updateGalleryStatus("未读取到可识别的图库照片")

                    Toast.makeText(this, "未读取到图库照片", Toast.LENGTH_SHORT).show()

                }

                return@executeWorker

            }

            val processedKeys = synchronized(processedGalleryPhotoKeys) {

                processedGalleryPhotoKeys.toSet()

            }

            val latestWindow = photos.take(defaultSelectCount)

            val firstProcessedInWindow = latestWindow.indexOfFirst { galleryPhotoKey(it) in processedKeys }

            val defaultSelectedPhotos = if (firstProcessedInWindow >= 0) {

                latestWindow.take(firstProcessedInWindow)

            } else {

                latestWindow

            }

            val defaultSelectedKeys = defaultSelectedPhotos.map { galleryPhotoKey(it) }

            runOnUiThread {

                isGalleryPreviewLoading = false

                setGalleryRefreshing(false)

                galleryPreviewPhotos = photos

                synchronized(selectedGalleryPhotoKeys) {

                    selectedGalleryPhotoKeys.clear()

                    selectedGalleryPhotoKeys.addAll(defaultSelectedKeys)

                }

                renderGalleryPreview(photos)

                updateGallerySelectionStatus()

            }

            recordDiagnostic(

                "图库预览加载完成: count=${photos.size}, processedKnown=${processedKeys.size}, " +

                    "latestWindow=${latestWindow.size}, firstProcessedInWindow=$firstProcessedInWindow, " +

                    "defaultSelected=${defaultSelectedKeys.size}"

            )

        }

    }

    private fun processGalleryPhoto(index: Int, total: Int, photo: GalleryPhoto, batchId: Long) {

        val record = createRecognitionRecord(

            status = STATUS_LOCAL_PROCESSING,

            statusText = "正在读取图库照片"

        )

        registerGalleryBatchRecord(batchId, record.id)

        try {

            val bytes = contentResolver.openInputStream(photo.uri)?.use { input ->

                input.readBytes()

            }

            if (bytes == null || bytes.isEmpty()) {

                updateRecognitionRecord(record.id) {

                    it.status = STATUS_FAILED

                    it.statusText = "图库照片读取失败"

                    it.errorMessage = "无法读取图片字节"

                }

                recordDiagnostic("图库照片读取失败: index=$index/$total, uri=${photo.uri}, name=${photo.displayName}")

                return

            }

            updateRecognitionRecord(record.id) {

                it.status = STATUS_LOCAL_PROCESSING

                it.statusText = "正在本地检测图库照片"

                it.errorMessage = null

            }

            recordDiagnostic(

                "图库照片读取成功: index=$index/$total, name=${photo.displayName}, " +

                    "bytes=${bytes.size}, size=${photo.width}x${photo.height}, dateTaken=${photo.dateTaken}"

            )

            markGalleryPhotoProcessed(photo)

            processCapturedFrameForMatch(record.id, bytes, "图库照片", processInline = true)

        } catch (e: Exception) {

            updateRecognitionRecord(record.id) {

                it.status = STATUS_FAILED

                it.statusText = "图库照片读取异常"

                it.errorMessage = e.message

            }

            recordDiagnostic("图库照片处理异常: index=$index/$total, uri=${photo.uri}", e)

        }

    }

    private fun queryLatestGalleryPhotos(limit: Int): List<GalleryPhoto> {

        val projection = arrayOf(

            MediaStore.Images.Media._ID,

            MediaStore.Images.Media.DISPLAY_NAME,

            MediaStore.Images.Media.DATE_TAKEN,

            MediaStore.Images.Media.DATE_ADDED,

            MediaStore.Images.Media.SIZE,

            MediaStore.Images.Media.WIDTH,

            MediaStore.Images.Media.HEIGHT

        )

        val sortOrder = "${MediaStore.Images.Media.DATE_TAKEN} DESC, ${MediaStore.Images.Media.DATE_ADDED} DESC"

        val photos = mutableListOf<GalleryPhoto>()

        contentResolver.query(

            MediaStore.Images.Media.EXTERNAL_CONTENT_URI,

            projection,

            null,

            null,

            sortOrder

        )?.use { cursor ->

            val idColumn = cursor.getColumnIndexOrThrow(MediaStore.Images.Media._ID)

            val nameColumn = cursor.getColumnIndexOrThrow(MediaStore.Images.Media.DISPLAY_NAME)

            val dateTakenColumn = cursor.getColumnIndexOrThrow(MediaStore.Images.Media.DATE_TAKEN)

            val dateAddedColumn = cursor.getColumnIndexOrThrow(MediaStore.Images.Media.DATE_ADDED)

            val sizeColumn = cursor.getColumnIndexOrThrow(MediaStore.Images.Media.SIZE)

            val widthColumn = cursor.getColumnIndexOrThrow(MediaStore.Images.Media.WIDTH)

            val heightColumn = cursor.getColumnIndexOrThrow(MediaStore.Images.Media.HEIGHT)

            while (cursor.moveToNext() && photos.size < limit) {

                val id = cursor.getLong(idColumn)

                val uri = ContentUris.withAppendedId(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, id)

                val dateTaken = cursor.getLong(dateTakenColumn).takeIf { it > 0L }

                    ?: cursor.getLong(dateAddedColumn) * 1000L

                photos.add(

                    GalleryPhoto(

                        uri = uri,

                        displayName = cursor.getString(nameColumn) ?: "photo_$id",

                        dateTaken = dateTaken,

                        sizeBytes = cursor.getLong(sizeColumn),

                        width = cursor.getInt(widthColumn),

                        height = cursor.getInt(heightColumn)

                    )

                )

            }

        }

        return photos

    }

    private fun renderGalleryPreview(photos: List<GalleryPhoto>) {

        binding.galleryQueueList.removeAllViews()

        val columns = GALLERY_GRID_COLUMNS

        val gap = dp(3)

        val itemSize = ((resources.displayMetrics.widthPixels - dp(32) - gap * (columns - 1)) / columns)

            .coerceAtLeast(dp(92))

        photos.chunked(columns).forEach { rowPhotos ->

            val row = LinearLayout(this).apply {

                orientation = LinearLayout.HORIZONTAL

            }

            rowPhotos.forEachIndexed { columnIndex, photo ->

                val key = galleryPhotoKey(photo)

                val checked = synchronized(selectedGalleryPhotoKeys) { selectedGalleryPhotoKeys.contains(key) }

                val processed = isGalleryPhotoProcessed(photo)

                val tile = FrameLayout(this).apply {

                    background = ContextCompat.getDrawable(this@MainActivity, R.drawable.bg_preview_panel)

                    contentDescription = photo.displayName

                }

                val tileParams = LinearLayout.LayoutParams(0, itemSize, 1f).apply {

                    if (columnIndex < columns - 1) {

                        marginEnd = gap

                    }

                }

                row.addView(tile, tileParams)

                val thumb = ImageView(this).apply {

                    layoutParams = FrameLayout.LayoutParams(

                        FrameLayout.LayoutParams.MATCH_PARENT,

                        FrameLayout.LayoutParams.MATCH_PARENT

                    )

                    background = ContextCompat.getDrawable(this@MainActivity, R.drawable.bg_preview_panel)

                    scaleType = ImageView.ScaleType.CENTER_CROP

                    tag = key

                }

                tile.addView(thumb)

                loadGalleryThumbnailAsync(photo, thumb, key, itemSize)

                val selectedOverlay = View(this).apply {

                    setBackgroundColor(Color.argb(72, 15, 159, 122))

                    visibility = if (checked) View.VISIBLE else View.GONE

                }

                tile.addView(

                    selectedOverlay,

                    FrameLayout.LayoutParams(

                        FrameLayout.LayoutParams.MATCH_PARENT,

                        FrameLayout.LayoutParams.MATCH_PARENT

                    )

                )

                val checkMark = TextView(this).apply {

                    text = "✓"

                    gravity = android.view.Gravity.CENTER

                    setTextColor(Color.WHITE)

                    textSize = 16f

                    setTypeface(null, android.graphics.Typeface.BOLD)

                    background = ContextCompat.getDrawable(this@MainActivity, R.drawable.bg_gallery_selected_badge)

                    visibility = if (checked) View.VISIBLE else View.GONE

                }

                val checkParams = FrameLayout.LayoutParams(dp(26), dp(26), android.view.Gravity.TOP or android.view.Gravity.END).apply {

                    setMargins(0, dp(6), dp(6), 0)

                }

                tile.addView(checkMark, checkParams)

                if (processed) {

                    val processedDot = View(this).apply {

                        background = ContextCompat.getDrawable(this@MainActivity, R.drawable.bg_gallery_processed_dot)

                    }

                    val dotParams = FrameLayout.LayoutParams(dp(9), dp(9), android.view.Gravity.BOTTOM or android.view.Gravity.START).apply {

                        setMargins(dp(7), 0, 0, dp(7))

                    }

                    tile.addView(processedDot, dotParams)

                }

                tile.setOnClickListener {

                    val nowChecked = synchronized(selectedGalleryPhotoKeys) {

                        if (selectedGalleryPhotoKeys.contains(key)) {

                            selectedGalleryPhotoKeys.remove(key)

                            false

                        } else {

                            selectedGalleryPhotoKeys.add(key)

                            true

                        }

                    }

                    selectedOverlay.visibility = if (nowChecked) View.VISIBLE else View.GONE

                    checkMark.visibility = if (nowChecked) View.VISIBLE else View.GONE

                    updateGallerySelectionStatus()

                }

            }

            if (rowPhotos.size < columns) {

                repeat(columns - rowPhotos.size) { placeholderIndex ->

                    val placeholderParams = LinearLayout.LayoutParams(0, itemSize, 1f).apply {

                        if (rowPhotos.size + placeholderIndex < columns - 1) {

                            marginEnd = gap

                        }

                    }

                    row.addView(View(this), placeholderParams)

                }

            }

            val params = LinearLayout.LayoutParams(

                LinearLayout.LayoutParams.MATCH_PARENT,

                LinearLayout.LayoutParams.WRAP_CONTENT

            ).apply {

                bottomMargin = gap

            }

            binding.galleryQueueList.addView(row, params)

        }

    }

    private fun galleryDefaultSelectCount(): Int {

        return DEFAULT_GALLERY_BATCH_SIZE

    }

    private fun loadGalleryThumbnailAsync(

        photo: GalleryPhoto,

        target: ImageView,

        expectedKey: String,

        maxSide: Int = dp(160)

    ) {

        executeThumbnailWorker("加载图库缩略图") {

            val bitmap = try {

                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {

                    contentResolver.loadThumbnail(photo.uri, Size(maxSide, maxSide), null)

                } else {

                    decodeScaledBitmapFromUri(photo.uri, maxSide)

                }

            } catch (e: Exception) {

                recordDiagnostic("图库缩略图加载失败: name=${photo.displayName}, uri=${photo.uri}", e)

                null

            }

            if (bitmap != null) {

                runOnUiThread {

                    if (target.tag == expectedKey) {

                        target.setImageBitmap(bitmap)

                    }

                }

            }

        }

    }

    private fun decodeScaledBitmapFromUri(uri: Uri, maxSide: Int): Bitmap? {

        val bounds = BitmapFactory.Options().apply { inJustDecodeBounds = true }

        contentResolver.openInputStream(uri)?.use {

            BitmapFactory.decodeStream(it, null, bounds)

        }

        if (bounds.outWidth <= 0 || bounds.outHeight <= 0) {

            return null

        }

        val options = BitmapFactory.Options().apply {

            inSampleSize = calculateInSampleSize(bounds.outWidth, bounds.outHeight, maxSide)

        }

        return contentResolver.openInputStream(uri)?.use {

            BitmapFactory.decodeStream(it, null, options)

        }

    }

    private fun galleryPhotoKey(photo: GalleryPhoto): String {

        return "${photo.uri}|${photo.dateTaken}|${photo.sizeBytes}"

    }

    private fun loadProcessedGalleryPhotoKeys() {

        val keys = getSharedPreferences(GALLERY_PREFS_NAME, Context.MODE_PRIVATE)

            .getStringSet(GALLERY_PREF_PROCESSED_KEYS, emptySet())

            ?: emptySet()

        synchronized(processedGalleryPhotoKeys) {

            processedGalleryPhotoKeys.clear()

            processedGalleryPhotoKeys.addAll(keys)

        }

        recordDiagnostic("已加载图库已检测标记: count=${keys.size}")

    }

    private fun saveProcessedGalleryPhotoKeys() {

        val snapshot = synchronized(processedGalleryPhotoKeys) {

            processedGalleryPhotoKeys.toList().takeLast(PROCESSED_GALLERY_KEY_LIMIT).toSet()

        }

        getSharedPreferences(GALLERY_PREFS_NAME, Context.MODE_PRIVATE)

            .edit()

            .putStringSet(GALLERY_PREF_PROCESSED_KEYS, snapshot)

            .apply()

    }

    private fun markGalleryPhotoProcessed(photo: GalleryPhoto) {

        val key = galleryPhotoKey(photo)

        val changed = synchronized(processedGalleryPhotoKeys) {

            processedGalleryPhotoKeys.add(key)

        }

        if (changed) {

            saveProcessedGalleryPhotoKeys()

            recordDiagnostic("图库照片标记为已检测: name=${photo.displayName}, key=$key")

            runOnUiThread {

                if (binding.galleryPage.visibility == View.VISIBLE && !isGalleryBatchRunning) {

                    renderGalleryPreview(galleryPreviewPhotos)

                    updateGallerySelectionStatus()

                }

            }

        }

    }

    private fun isGalleryPhotoProcessed(photo: GalleryPhoto): Boolean {

        val key = galleryPhotoKey(photo)

        return synchronized(processedGalleryPhotoKeys) {

            processedGalleryPhotoKeys.contains(key)

        }

    }

    private fun updateGallerySelectionStatus() {

        val selectedCount = synchronized(selectedGalleryPhotoKeys) { selectedGalleryPhotoKeys.size }

        val processedVisibleCount = galleryPreviewPhotos.count { isGalleryPhotoProcessed(it) }

        binding.btnStartGalleryRecognition.contentDescription =

            "识别所选，已勾选 $selectedCount 张，已检测 $processedVisibleCount 张"

        updateGalleryStatus("已加载 ${galleryPreviewPhotos.size} 张最近照片，已勾选 $selectedCount 张，已检测 $processedVisibleCount 张")

    }

    private fun updateGalleryStatus(text: String) {

        Log.d(TAG, "Gallery status: $text")

    }

    private fun startVideoRecognition() {

        if (isVideoRecognitionRunning) {

            Toast.makeText(this, "视频识别正在进行，请稍候", Toast.LENGTH_SHORT).show()

            return

        }

        if (videoPreviewItems.isEmpty()) {

            if (!galleryVideoPermissionsGranted()) {

                requestGalleryVideoPermission("startVideoRecognition")

                Toast.makeText(this, "也可以点击“选择视频”直接指定一个视频", Toast.LENGTH_SHORT).show()

                return

            }

            if (!fullVideoLibraryPermissionGranted()) {

                requestGalleryVideoPermission("startVideoRecognition-empty-preview-limited-access")

                Toast.makeText(this, "需要允许读取视频，或点击“选择视频”直接指定一个视频", Toast.LENGTH_SHORT).show()

                return

            }

            loadVideoPreview(force = true)

            Toast.makeText(this, "正在加载视频预览，请选择后再识别", Toast.LENGTH_SHORT).show()

            return

        }

        val selectedKeys = synchronized(selectedVideoKeys) { selectedVideoKeys.toSet() }

        val selectedVideo = videoPreviewItems.firstOrNull { videoKey(it) in selectedKeys }

        if (selectedVideo == null) {

            updateVideoStatus("请先选择 1 个视频")

            Toast.makeText(this, "请先选择要识别的视频", Toast.LENGTH_SHORT).show()

            return

        }

        val batchId = System.currentTimeMillis()

        activeVideoBatchId = batchId

        isVideoRecognitionRunning = true

        updateVideoProgress(batchId, "正在分析视频...", 0, 1, finished = false)

        recordDiagnostic(

            "用户启动视频识别: name=${selectedVideo.displayName}, duration=${selectedVideo.durationMs}, " +

                "size=${selectedVideo.width}x${selectedVideo.height}, bytes=${selectedVideo.sizeBytes}, " +

                "permission=${videoPermissionStatus()}"

        )

        executeWorker("处理视频识别") {

            processVideoForExperts(selectedVideo, batchId)

        }

    }

    private fun ensureVideoPreviewLoaded(force: Boolean = false) {

        if (!galleryVideoPermissionsGranted()) {

            updateVideoStatus("需要图库视频权限，点击识别后授权并加载预览")

            return

        }

        if (videoPreviewItems.isEmpty() && !fullVideoLibraryPermissionGranted()) {

            requestGalleryVideoPermission("ensureVideoPreviewLoaded-limited-access")

            updateVideoStatus("当前只有部分媒体权限，正在请求完整视频权限")

            return

        }

        if (!force && videoPreviewItems.isNotEmpty()) {

            updateVideoSelectionStatus()

            return

        }

        loadVideoPreview(force)

    }

    private fun loadVideoPreview(force: Boolean = false) {

        if (!galleryVideoPermissionsGranted()) {

            setVideoRefreshing(false)

            requestGalleryVideoPermission("loadVideoPreview")

            return

        }

        if (isVideoPreviewLoading) {

            updateVideoStatus("正在加载视频预览...")

            return

        }

        if (!force && videoPreviewItems.isNotEmpty()) {

            setVideoRefreshing(false)

            updateVideoSelectionStatus()

            return

        }

        isVideoPreviewLoading = true

        binding.videoQueueList.removeAllViews()

        updateVideoStatus("正在加载最近视频预览...")

        recordDiagnostic(

            "开始加载视频预览: previewLimit=$VIDEO_PREVIEW_SIZE, " +

                "fullVideoPermission=${fullVideoLibraryPermissionGranted()}, limitedVisual=${limitedMediaSelectionGranted()}"

        )

        executeWorker("读取最近图库视频") {

            val videos = try {

                queryLatestGalleryVideos(VIDEO_PREVIEW_SIZE)

            } catch (e: Exception) {

                recordDiagnostic("视频读取异常: previewLimit=$VIDEO_PREVIEW_SIZE", e)

                runOnUiThread {

                    isVideoPreviewLoading = false

                    setVideoRefreshing(false)

                    updateVideoStatus("视频读取失败")

                    Toast.makeText(this, "视频读取失败", Toast.LENGTH_SHORT).show()

                }

                return@executeWorker

            }

            runOnUiThread {

                isVideoPreviewLoading = false

                setVideoRefreshing(false)

                videoPreviewItems = videos

                synchronized(selectedVideoKeys) {

                    selectedVideoKeys.clear()

                    videos.firstOrNull()?.let { selectedVideoKeys.add(videoKey(it)) }

                }

                renderVideoPreview(videos)

                updateVideoSelectionStatus()

                if (videos.isEmpty()) {

                    val message = if (!fullVideoLibraryPermissionGranted() && limitedMediaSelectionGranted()) {

                        "未读取到已授权视频，请允许读取所有视频或在授权中选择视频"

                    } else {

                        "未读取到图库视频"

                    }

                    Toast.makeText(this, message, Toast.LENGTH_SHORT).show()

                }

            }

            recordDiagnostic(

                "视频预览加载完成: count=${videos.size}, defaultSelected=${if (videos.isEmpty()) 0 else 1}, " +

                    "fullVideoPermission=${fullVideoLibraryPermissionGranted()}, limitedVisual=${limitedMediaSelectionGranted()}"

            )

        }

    }

    private fun setupVideoPullRefresh() {

        binding.videoScroll.setOnTouchListener { _, event ->

            if (isVideoPreviewLoading || isVideoRefreshing || isVideoRecognitionRunning) {

                return@setOnTouchListener false

            }

            when (event.actionMasked) {

                MotionEvent.ACTION_DOWN -> {

                    videoPullStartY = event.y

                    isVideoPulling = binding.videoScroll.scrollY == 0

                    false

                }

                MotionEvent.ACTION_MOVE -> {

                    if (binding.videoScroll.scrollY == 0 && event.y - videoPullStartY > dp(VIDEO_PULL_HINT_DISTANCE_DP)) {

                        isVideoPulling = true

                        showVideoRefreshHint("松开刷新")

                    }

                    false

                }

                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {

                    val pullDistance = event.y - videoPullStartY

                    if (isVideoPulling && binding.videoScroll.scrollY == 0 && pullDistance > dp(VIDEO_PULL_REFRESH_DISTANCE_DP)) {

                        setVideoRefreshing(true)

                        recordDiagnostic("用户下拉刷新视频: pullDistance=${pullDistance.roundToInt()}")

                        loadVideoPreview(force = true)

                    } else {

                        hideVideoRefreshHint()

                    }

                    isVideoPulling = false

                    false

                }

                else -> false

            }

        }

    }

    private fun showVideoRefreshHint(text: String) {

        binding.tvVideoRefreshHint.text = text

        binding.tvVideoRefreshHint.visibility = View.VISIBLE

    }

    private fun hideVideoRefreshHint() {

        if (!isVideoRefreshing) {

            binding.tvVideoRefreshHint.visibility = View.GONE

        }

    }

    private fun setVideoRefreshing(refreshing: Boolean) {

        isVideoRefreshing = refreshing

        runOnUiThread {

            if (refreshing) {

                binding.tvVideoRefreshHint.text = "正在刷新..."

                binding.tvVideoRefreshHint.visibility = View.VISIBLE

            } else {

                binding.tvVideoRefreshHint.visibility = View.GONE

            }

        }

    }

    private fun requestGalleryVideoPermission(reason: String) {

        recordDiagnostic("请求图库视频权限: reason=$reason, status=${videoPermissionStatus()}")

        ActivityCompat.requestPermissions(

            this,

            galleryVideoPermissions(),

            REQUEST_CODE_GALLERY_VIDEOS

        )

    }

    private fun launchImagePicker() {
        val intent = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
            Intent(MediaStore.ACTION_PICK_IMAGES).apply {
                type = "image/*"
            }
        } else {
            Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
                addCategory(Intent.CATEGORY_OPENABLE)
                type = "image/*"
                addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
                addFlags(Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
            }
        }
        try {
            recordDiagnostic("打开系统图片选择器: sdk=${Build.VERSION.SDK_INT}")
            startActivityForResult(intent, REQUEST_CODE_PICK_IMAGE)
        } catch (e: Exception) {
            recordDiagnostic("打开系统图片选择器失败", e)
            Toast.makeText(this, "无法打开系统图片选择器", Toast.LENGTH_SHORT).show()
        }
    }

    private fun handlePickedImage(data: Intent?) {
        val uri = data?.data
        if (uri == null) {
            recordDiagnostic("系统图片选择器返回为空")
            Toast.makeText(this, "未选择图片", Toast.LENGTH_SHORT).show()
            return
        }
        try {
            val flags = data.flags and Intent.FLAG_GRANT_READ_URI_PERMISSION
            if (Build.VERSION.SDK_INT < Build.VERSION_CODES.TIRAMISU) {
                try {
                    contentResolver.takePersistableUriPermission(uri, flags)
                } catch (e: Exception) {
                    recordDiagnostic("图片 URI 持久授权失败，可继续临时识别: uri=$uri", e)
                }
            }
            val photo = buildPickedGalleryPhoto(uri)
            val key = galleryPhotoKey(photo)
            
            synchronized(galleryPreviewPhotos) {
                val mutable = galleryPreviewPhotos.toMutableList()
                mutable.removeAll { it.uri == photo.uri }
                mutable.add(0, photo)
                galleryPreviewPhotos = mutable
            }
            
            synchronized(selectedGalleryPhotoKeys) {
                selectedGalleryPhotoKeys.clear()
                selectedGalleryPhotoKeys.add(key)
            }
            
            renderGalleryPreview(galleryPreviewPhotos)
            updateGallerySelectionStatus()
            
            recordDiagnostic(
                "系统选择图片完成: name=${photo.displayName}, " +
                    "size=${photo.width}x${photo.height}, bytes=${photo.sizeBytes}, uri=$uri"
            )
        } catch (e: Exception) {
            recordDiagnostic("处理系统选择图片异常: uri=$uri", e)
            Toast.makeText(this, "读取所选图片失败，已记录日志", Toast.LENGTH_SHORT).show()
        }
    }

    private fun buildPickedGalleryPhoto(uri: Uri): GalleryPhoto {
        val size = readImageMetadata(uri)
        val openable = readOpenableMetadata(uri)
        return GalleryPhoto(
            uri = uri,
            displayName = openable.first ?: "selected_image",
            dateTaken = System.currentTimeMillis(),
            sizeBytes = openable.second ?: 0L,
            width = size.first,
            height = size.second
        )
    }

    private fun readImageMetadata(uri: Uri): Pair<Int, Int> {
        return try {
            contentResolver.openInputStream(uri)?.use { stream ->
                val options = BitmapFactory.Options().apply {
                    inJustDecodeBounds = true
                }
                BitmapFactory.decodeStream(stream, null, options)
                options.outWidth to options.outHeight
            } ?: (0 to 0)
        } catch (e: Exception) {
            recordDiagnostic("读取图片元数据失败: uri=$uri", e)
            0 to 0
        }
    }

    private fun launchVideoPicker() {

        val intent = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {

            Intent(MediaStore.ACTION_PICK_IMAGES).apply {

                type = "video/*"

            }

        } else {

            Intent(Intent.ACTION_OPEN_DOCUMENT).apply {

                addCategory(Intent.CATEGORY_OPENABLE)

                type = "video/*"

                addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)

                addFlags(Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)

            }

        }

        try {

            recordDiagnostic("打开系统视频选择器: sdk=${Build.VERSION.SDK_INT}, permission=${videoPermissionStatus()}")

            startActivityForResult(intent, REQUEST_CODE_PICK_VIDEO)

        } catch (e: Exception) {

            recordDiagnostic("打开系统视频选择器失败", e)

            Toast.makeText(this, "无法打开系统视频选择器", Toast.LENGTH_SHORT).show()

        }

    }

    private fun handlePickedVideo(data: Intent?) {

        val uri = data?.data

        if (uri == null) {

            recordDiagnostic("系统视频选择器返回为空")

            Toast.makeText(this, "未选择视频", Toast.LENGTH_SHORT).show()

            return

        }

        try {

            val flags = data.flags and Intent.FLAG_GRANT_READ_URI_PERMISSION

            if (Build.VERSION.SDK_INT < Build.VERSION_CODES.TIRAMISU) {

                try {

                    contentResolver.takePersistableUriPermission(uri, flags)

                } catch (e: Exception) {

                    recordDiagnostic("视频 URI 持久授权失败，可继续临时识别: uri=$uri", e)

                }

            }

            val video = buildPickedGalleryVideo(uri)

            videoPreviewItems = listOf(video)

            synchronized(selectedVideoKeys) {

                selectedVideoKeys.clear()

                selectedVideoKeys.add(videoKey(video))

            }

            renderVideoPreview(videoPreviewItems)

            updateVideoSelectionStatus()

            binding.videoProgressPanel.visibility = View.GONE

            recordDiagnostic(

                "系统选择视频完成: name=${video.displayName}, duration=${video.durationMs}, " +

                    "size=${video.width}x${video.height}, bytes=${video.sizeBytes}, uri=$uri"

            )

        } catch (e: Exception) {

            recordDiagnostic("处理系统选择视频异常: uri=$uri", e)

            Toast.makeText(this, "读取所选视频失败，已记录日志", Toast.LENGTH_SHORT).show()

        }

    }

    private fun buildPickedGalleryVideo(uri: Uri): GalleryVideo {

        val metadata = readVideoMetadata(uri)

        val openable = readOpenableMetadata(uri)

        return GalleryVideo(

            uri = uri,

            displayName = openable.first ?: "selected_video",

            dateTaken = System.currentTimeMillis(),

            sizeBytes = openable.second ?: 0L,

            width = metadata.width,

            height = metadata.height,

            durationMs = metadata.durationMs

        )

    }

    private fun readVideoMetadata(uri: Uri): VideoMetadata {

        val retriever = MediaMetadataRetriever()

        return try {

            retriever.setDataSource(this, uri)

            VideoMetadata(

                width = retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_VIDEO_WIDTH)?.toIntOrNull() ?: 0,

                height = retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_VIDEO_HEIGHT)?.toIntOrNull() ?: 0,

                durationMs = retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_DURATION)?.toLongOrNull() ?: 0L

            )

        } finally {

            try {

                retriever.release()

            } catch (e: Exception) {

                // ignore

            }

        }

    }

    private fun readOpenableMetadata(uri: Uri): Pair<String?, Long?> {

        return try {

            contentResolver.query(uri, arrayOf(OpenableColumns.DISPLAY_NAME, OpenableColumns.SIZE), null, null, null)

                ?.use { cursor ->

                    if (cursor.moveToFirst()) {

                        val nameIndex = cursor.getColumnIndex(OpenableColumns.DISPLAY_NAME)

                        val sizeIndex = cursor.getColumnIndex(OpenableColumns.SIZE)

                        val name = if (nameIndex >= 0) cursor.getString(nameIndex) else null

                        val size = if (sizeIndex >= 0) cursor.getLong(sizeIndex) else null

                        name to size

                    } else {

                        null to null

                    }

                } ?: (null to null)

        } catch (e: Exception) {

            recordDiagnostic("读取视频 Openable 元数据失败: uri=$uri", e)

            null to null

        }

    }

    private fun queryLatestGalleryVideos(limit: Int): List<GalleryVideo> {

        val projection = arrayOf(

            MediaStore.Video.Media._ID,

            MediaStore.Video.Media.DISPLAY_NAME,

            MediaStore.Video.Media.DATE_TAKEN,

            MediaStore.Video.Media.DATE_ADDED,

            MediaStore.Video.Media.SIZE,

            MediaStore.Video.Media.WIDTH,

            MediaStore.Video.Media.HEIGHT,

            MediaStore.Video.Media.DURATION

        )

        val sortOrder = "${MediaStore.Video.Media.DATE_TAKEN} DESC, ${MediaStore.Video.Media.DATE_ADDED} DESC"

        val videos = mutableListOf<GalleryVideo>()

        contentResolver.query(

            MediaStore.Video.Media.EXTERNAL_CONTENT_URI,

            projection,

            null,

            null,

            sortOrder

        )?.use { cursor ->

            val idColumn = cursor.getColumnIndexOrThrow(MediaStore.Video.Media._ID)

            val nameColumn = cursor.getColumnIndexOrThrow(MediaStore.Video.Media.DISPLAY_NAME)

            val dateTakenColumn = cursor.getColumnIndexOrThrow(MediaStore.Video.Media.DATE_TAKEN)

            val dateAddedColumn = cursor.getColumnIndexOrThrow(MediaStore.Video.Media.DATE_ADDED)

            val sizeColumn = cursor.getColumnIndexOrThrow(MediaStore.Video.Media.SIZE)

            val widthColumn = cursor.getColumnIndexOrThrow(MediaStore.Video.Media.WIDTH)

            val heightColumn = cursor.getColumnIndexOrThrow(MediaStore.Video.Media.HEIGHT)

            val durationColumn = cursor.getColumnIndexOrThrow(MediaStore.Video.Media.DURATION)

            while (cursor.moveToNext() && videos.size < limit) {

                val id = cursor.getLong(idColumn)

                val uri = ContentUris.withAppendedId(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, id)

                val dateTaken = cursor.getLong(dateTakenColumn).takeIf { it > 0L }

                    ?: cursor.getLong(dateAddedColumn) * 1000L

                videos.add(

                    GalleryVideo(

                        uri = uri,

                        displayName = cursor.getString(nameColumn) ?: "video_$id",

                        dateTaken = dateTaken,

                        sizeBytes = cursor.getLong(sizeColumn),

                        width = cursor.getInt(widthColumn),

                        height = cursor.getInt(heightColumn),

                        durationMs = cursor.getLong(durationColumn)

                    )

                )

            }

        }

        return videos

    }

    private fun renderVideoPreview(videos: List<GalleryVideo>) {

        binding.videoQueueList.removeAllViews()

        val columns = VIDEO_GRID_COLUMNS

        val gap = dp(3)

        val itemSize = ((resources.displayMetrics.widthPixels - dp(32) - gap * (columns - 1)) / columns)

            .coerceAtLeast(dp(120))

        videos.chunked(columns).forEach { rowVideos ->

            val row = LinearLayout(this).apply {

                orientation = LinearLayout.HORIZONTAL

            }

            rowVideos.forEachIndexed { columnIndex, video ->

                val key = videoKey(video)

                val checked = synchronized(selectedVideoKeys) { selectedVideoKeys.contains(key) }

                val tile = FrameLayout(this).apply {

                    background = ContextCompat.getDrawable(this@MainActivity, R.drawable.bg_preview_panel)

                    contentDescription = video.displayName

                }

                val tileParams = LinearLayout.LayoutParams(0, itemSize, 1f).apply {

                    if (columnIndex < columns - 1) {

                        marginEnd = gap

                    }

                }

                row.addView(tile, tileParams)

                val thumb = ImageView(this).apply {

                    layoutParams = FrameLayout.LayoutParams(

                        FrameLayout.LayoutParams.MATCH_PARENT,

                        FrameLayout.LayoutParams.MATCH_PARENT

                    )

                    background = ContextCompat.getDrawable(this@MainActivity, R.drawable.bg_preview_panel)

                    scaleType = ImageView.ScaleType.CENTER_CROP

                    tag = key

                }

                tile.addView(thumb)

                loadVideoThumbnailAsync(video, thumb, key, itemSize)

                val selectedOverlay = View(this).apply {

                    setBackgroundColor(Color.argb(76, 15, 159, 122))

                    visibility = if (checked) View.VISIBLE else View.GONE

                }

                tile.addView(

                    selectedOverlay,

                    FrameLayout.LayoutParams(

                        FrameLayout.LayoutParams.MATCH_PARENT,

                        FrameLayout.LayoutParams.MATCH_PARENT

                    )

                )

                val playMark = TextView(this).apply {

                    text = "▶"

                    gravity = android.view.Gravity.CENTER

                    setTextColor(Color.WHITE)

                    textSize = 16f

                    background = ContextCompat.getDrawable(this@MainActivity, R.drawable.bg_gallery_selected_badge)

                }

                val playParams = FrameLayout.LayoutParams(dp(28), dp(28), android.view.Gravity.CENTER)

                tile.addView(playMark, playParams)

                val durationLabel = TextView(this).apply {

                    text = formatDurationMs(video.durationMs)

                    setTextColor(Color.WHITE)

                    textSize = 10f

                    setPadding(dp(5), dp(2), dp(5), dp(2))

                    setBackgroundColor(Color.argb(140, 0, 0, 0))

                }

                val durationParams = FrameLayout.LayoutParams(

                    FrameLayout.LayoutParams.WRAP_CONTENT,

                    FrameLayout.LayoutParams.WRAP_CONTENT,

                    android.view.Gravity.BOTTOM or android.view.Gravity.END

                ).apply {

                    setMargins(0, 0, dp(6), dp(6))

                }

                tile.addView(durationLabel, durationParams)

                val checkMark = TextView(this).apply {

                    text = "✓"

                    gravity = android.view.Gravity.CENTER

                    setTextColor(Color.WHITE)

                    textSize = 16f

                    setTypeface(null, android.graphics.Typeface.BOLD)

                    background = ContextCompat.getDrawable(this@MainActivity, R.drawable.bg_gallery_selected_badge)

                    visibility = if (checked) View.VISIBLE else View.GONE

                }

                val checkParams = FrameLayout.LayoutParams(dp(26), dp(26), android.view.Gravity.TOP or android.view.Gravity.END).apply {

                    setMargins(0, dp(6), dp(6), 0)

                }

                tile.addView(checkMark, checkParams)

                tile.setOnClickListener {

                    synchronized(selectedVideoKeys) {

                        selectedVideoKeys.clear()

                        selectedVideoKeys.add(key)

                    }

                    renderVideoPreview(videoPreviewItems)

                    updateVideoSelectionStatus()

                }

            }

            if (rowVideos.size < columns) {

                repeat(columns - rowVideos.size) { placeholderIndex ->

                    val placeholderParams = LinearLayout.LayoutParams(0, itemSize, 1f).apply {

                        if (rowVideos.size + placeholderIndex < columns - 1) {

                            marginEnd = gap

                        }

                    }

                    row.addView(View(this), placeholderParams)

                }

            }

            val params = LinearLayout.LayoutParams(

                LinearLayout.LayoutParams.MATCH_PARENT,

                LinearLayout.LayoutParams.WRAP_CONTENT

            ).apply {

                bottomMargin = gap

            }

            binding.videoQueueList.addView(row, params)

        }

    }

    private fun videoKey(video: GalleryVideo): String {

        return "${video.uri}|${video.dateTaken}|${video.sizeBytes}|${video.durationMs}"

    }

    private fun loadVideoThumbnailAsync(

        video: GalleryVideo,

        target: ImageView,

        expectedKey: String,

        maxSide: Int = dp(180)

    ) {

        executeWorker("加载视频缩略图") {

            val bitmap = try {

                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {

                    contentResolver.loadThumbnail(video.uri, Size(maxSide, maxSide), null)

                } else {

                    decodeVideoThumbnail(video.uri, maxSide)

                }

            } catch (e: Exception) {

                recordDiagnostic("视频缩略图加载失败: name=${video.displayName}, uri=${video.uri}", e)

                null

            }

            if (bitmap != null) {

                runOnUiThread {

                    if (target.tag == expectedKey) {

                        target.setImageBitmap(bitmap)

                    }

                }

            }

        }

    }

    private fun decodeVideoThumbnail(uri: Uri, maxSide: Int): Bitmap? {

        val retriever = MediaMetadataRetriever()

        return try {

            retriever.setDataSource(this, uri)

            val frame = retriever.getFrameAtTime(0, MediaMetadataRetriever.OPTION_CLOSEST_SYNC)

            frame?.let { resizeBitmapToMaxSide(it, maxSide) }

        } catch (e: Exception) {

            recordDiagnostic("视频缩略图解码失败: uri=$uri", e)

            null

        } finally {

            try {

                retriever.release()

            } catch (e: Exception) {

                // ignore

            }

        }

    }

    private fun updateVideoSelectionStatus() {

        val selectedCount = synchronized(selectedVideoKeys) { selectedVideoKeys.size }

        binding.btnStartVideoRecognition.contentDescription =

            "识别视频，已选择 $selectedCount 个视频"

        updateVideoStatus("已加载 ${videoPreviewItems.size} 个最近视频，已选择 $selectedCount 个")

    }

    private fun updateVideoStatus(text: String) {

        Log.d(TAG, "Video status: $text")

    }

    private fun startEmbeddedRtmpReceiver() {
        val existing = latestRtmpReceiverSnapshot
        if (existing.running) {
            Toast.makeText(this, "RTMP 接收服务已启动", Toast.LENGTH_SHORT).show()
            updateRtmpReceiverAddressHint()
            return
        }
        resetRealtimePreviewHealthState()
        bumpRealtimeRecognitionSession("启动内置 RTMP 接收服务")
        val streamKey = binding.etRtmpStreamKey.text.toString().trim().ifBlank { DEFAULT_RTMP_STREAM_KEY }
        binding.etRtmpStreamKey.setText(streamKey)
        stopRealtimeStreamTest("启动内置 RTMP 接收服务")
        latestRtmpReceiverSnapshot = EmbeddedRtmpReceiver.Snapshot(
            running = true,
            listening = false,
            port = RTMP_RECEIVER_PORT,
            expectedStreamKey = streamKey,
            message = "正在启动 RTMP 接收服务..."
        )
        renderRtmpReceiverSnapshot(latestRtmpReceiverSnapshot)
        updateRtmpReceiverAddressHint(streamKey)
        recordDiagnostic(
            "内置 RTMP 接收服务启动请求: port=$RTMP_RECEIVER_PORT, streamKey=$streamKey, " +
                "addresses=${localIpv4Addresses().joinToString("|")}"
        )
        val serviceIntent = Intent(this, RtmpReceiverService::class.java).apply {
            action = RtmpReceiverService.ACTION_START
            putExtra(RtmpReceiverService.EXTRA_PORT, RTMP_RECEIVER_PORT)
            putExtra(RtmpReceiverService.EXTRA_STREAM_KEY, streamKey)
        }
        ContextCompat.startForegroundService(this, serviceIntent)
    }

    private fun ensureRealtimeReceiverRunningForMainPage() {
        if (latestRtmpReceiverSnapshot.running) {
            return
        }
        startEmbeddedRtmpReceiver()
    }

    private fun stopEmbeddedRtmpReceiver(reason: String) {
        if (!latestRtmpReceiverSnapshot.running) {
            resetRealtimePreviewHealthState()
            latestRtmpReceiverSnapshot = latestRtmpReceiverSnapshot.copy(
                running = false,
                listening = false,
                clientConnected = false,
                message = "RTMP 接收服务未启动"
            )
            renderRtmpReceiverSnapshot(latestRtmpReceiverSnapshot)
            return
        }
        recordDiagnostic("内置 RTMP 接收服务停止请求: reason=$reason")
        bumpRealtimeRecognitionSession("停止内置 RTMP 接收服务: $reason")
        resetRealtimePreviewHealthState()
        val serviceIntent = Intent(this, RtmpReceiverService::class.java).apply {
            action = RtmpReceiverService.ACTION_STOP
            putExtra(RtmpReceiverService.EXTRA_REASON, reason)
        }
        startService(serviceIntent)
        latestRtmpReceiverSnapshot = latestRtmpReceiverSnapshot.copy(
            running = false,
            listening = false,
            clientConnected = false,
            message = "RTMP 接收服务正在停止..."
        )
        renderRtmpReceiverSnapshot(latestRtmpReceiverSnapshot)
    }

    private fun resetRealtimePreviewHealthState() {
        latestRtmpPreviewFrameIndex = 0L
        latestRtmpPreviewFrameBytes = 0
        latestRtmpPreviewFrameWidth = 0
        latestRtmpPreviewFrameHeight = 0
        lastRtmpPreviewFrameReceivedAt = 0L
        lastRtmpPreviewFrameRenderedAt = 0L
        lastRtmpPreviewRenderedFrameIndex = 0L
        rtmpPreviewRenderStartedAt = 0L
        lastRtmpPreviewHealthLogAt = 0L
        lastRtmpPreviewHealthLogKey = ""
        isRtmpPreviewRenderRunning = false
        synchronized(rtmpPreviewFrameDispatchLock) {
            pendingRtmpPreviewFrame = null
            isRtmpPreviewFrameDispatchPosted = false
        }
    }

    private fun restartEmbeddedRtmpReceiver() {
        recordDiagnostic("用户请求重启内置 RTMP 接收服务")
        val wasRunning = latestRtmpReceiverSnapshot.running
        if (wasRunning) {
            stopEmbeddedRtmpReceiver("用户重启实时接收服务")
            mainHandler.postDelayed({
                if (!isFinishing && !isDestroyed) {
                    startEmbeddedRtmpReceiver()
                }
            }, RTMP_RECEIVER_RESTART_DELAY_MS)
        } else {
            startEmbeddedRtmpReceiver()
        }
    }

    private fun copyRtmpPushAddressToClipboard() {
        val text = buildRtmpPushAddressText(binding.etRtmpStreamKey.text.toString().trim().ifBlank { DEFAULT_RTMP_STREAM_KEY })
        val clipboard = getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
        clipboard.setPrimaryClip(ClipData.newPlainText("Rokid RTMP push config", text))
        Toast.makeText(this, "RTMP 推流填写信息已复制", Toast.LENGTH_SHORT).show()
        recordDiagnostic("用户复制 RTMP 推流填写信息: chars=${text.length}")
    }

    private fun updateRtmpReceiverAddressHint(
        streamKey: String = binding.etRtmpStreamKey.text.toString().trim().ifBlank { DEFAULT_RTMP_STREAM_KEY }
    ) {
        if (!::binding.isInitialized) {
            return
        }
        val displayText = buildRtmpPushAddressDisplayText(streamKey)
        binding.tvRtmpReceiverAddress.text = displayText
        binding.tvMainRtmpPushAddress.text = buildRtmpPushAddressText(streamKey)
    }

    private fun buildRtmpPushAddressDisplayText(streamKey: String): String {
        val addresses = localIpv4Addresses()
        val firstAddress = addresses.firstOrNull() ?: "手机IP"
        val pushUrl = "rtmp://$firstAddress:$RTMP_RECEIVER_PORT/$RTMP_PUSH_APP_NAME"
        val fullUrl = "$pushUrl/$streamKey"
        return buildString {
            appendLine("乐奇 App 填写：")
            appendLine("推流地址：$pushUrl")
            appendLine("推流码：$streamKey")
            appendLine("完整地址：$fullUrl")
            if (firstAddress != "手机IP") {
                appendLine(selectedRtmpAddressHint(firstAddress))
            }
            if (addresses.size > 1) {
                appendLine("候选 IP 已自动按热点/同网段优先排序；如无法连接，请点“复制乐奇填写信息”查看全部候选。")
            }
        }.trim()
    }

    private fun buildRtmpPushAddressText(streamKey: String): String {
        val addresses = localIpv4Addresses()
        val firstAddress = addresses.firstOrNull() ?: "手机IP"
        val pushUrl = "rtmp://$firstAddress:$RTMP_RECEIVER_PORT/$RTMP_PUSH_APP_NAME"
        val pullUrl = "$pushUrl/$streamKey"
        return buildString {
            appendLine("乐奇 App 填写：")
            appendLine("推流地址：$pushUrl")
            appendLine("推流码：$streamKey")
            appendLine("注意：推流地址必须带 rtmp://")
            if (firstAddress != "手机IP") {
                appendLine(selectedRtmpAddressHint(firstAddress))
            }
            appendLine()
            appendLine("如果乐奇 App 要求完整地址，可填：")
            appendLine(pullUrl)
            appendLine()
            appendLine("手机热点测试时优先使用 10.* 地址；眼镜列表里的 10.* 通常是眼镜自己的 IP，不要填眼镜 IP。")
            if (addresses.isEmpty()) {
                appendLine()
                appendLine("未读到手机局域网 IP。请先让手机连接 Wi‑Fi，或打开手机热点后再点“复制填写”。")
            } else if (addresses.size > 1) {
                appendLine()
                appendLine("候选手机 IP（已按同网段/热点优先排序）：")
                addresses.forEachIndexed { index, ip ->
                    val prefix = if (index == 0) "推荐 " else ""
                    appendLine("$prefix rtmp://$ip:$RTMP_RECEIVER_PORT/$RTMP_PUSH_APP_NAME  推流码：$streamKey")
                }
            }
        }.trim()
    }

    private fun selectedRtmpAddressHint(selectedIp: String): String {
        val remoteIp = currentRtmpRemoteIp()
        return when {
            remoteIp != null && isSameIpv4CSubnet(selectedIp, remoteIp) ->
                "自动选择：与眼镜连接同网段的手机地址（眼镜 $remoteIp）"
            selectedIp.startsWith("10.") ->
                "自动选择：热点常见 10.* 手机地址"
            selectedIp.startsWith("192.168.") ->
                "自动选择：局域网 192.168.* 手机地址"
            isPrivate172Address(selectedIp) ->
                "自动选择：局域网 172.16-31.* 手机地址"
            else ->
                "自动选择：当前可用手机地址"
        }
    }

    private fun renderRtmpReceiverSnapshot(snapshot: EmbeddedRtmpReceiver.Snapshot) {
        if (!::binding.isInitialized) {
            return
        }
        updateRtmpReceiverAddressHint(snapshot.expectedStreamKey.ifBlank {
            binding.etRtmpStreamKey.text.toString().trim().ifBlank { DEFAULT_RTMP_STREAM_KEY }
        })
        binding.tvRtmpReceiverStatus.text = buildRtmpReceiverUserStatus(snapshot)
        binding.tvMainRealtimeStatus.text = mainRealtimeStatusText(snapshot)
        checkRealtimePreviewHealth("rtmp_status")
    }

    private fun buildRtmpReceiverUserStatus(snapshot: EmbeddedRtmpReceiver.Snapshot): String {
        val serviceText = when {
            snapshot.listening -> "已启动"
            snapshot.running -> "启动中"
            else -> "未启动"
        }
        val pushText = when {
            snapshot.clientConnected -> "已连接"
            snapshot.listening -> "等待眼镜推流"
            snapshot.running -> "等待服务就绪"
            else -> "未连接"
        }
        val videoText = if (snapshot.videoTags > 0) {
            "已收到视频画面"
        } else {
            "未收到视频画面"
        }
        return buildString {
            appendLine("接收服务：$serviceText")
            appendLine("眼镜推流：$pushText")
            append("视频数据：$videoText")
            if (snapshot.remoteAddress.isNotBlank() && snapshot.clientConnected) {
                appendLine()
                append("连接设备：${snapshot.remoteAddress}")
            }
        }
    }

    private fun mainRealtimeStatusText(snapshot: EmbeddedRtmpReceiver.Snapshot): String {
        return when {
            snapshot.videoTags > 0 -> {
                val facePart = if (latestRealtimeFaceCount >= 0) {
                    val validCount = latestRealtimeValidFaceCount.coerceAtLeast(0)
                    val uploadableCount = latestRealtimeUploadableFaceCount.coerceAtLeast(0)
                    "，有效 $validCount/检出 $latestRealtimeFaceCount，可上云 $uploadableCount"
                } else {
                    ""
                }
                val crowdPart = if (isRealtimeCrowdModeActive(System.currentTimeMillis())) {
                    "，多人高峰模式"
                } else {
                    ""
                }
                val maxConcurrent = realtimeCloudMaxConcurrentRequests(System.currentTimeMillis())
                val cloudPart = if (activeRealtimeCloudRequestCount > 0) {
                    "，云端 $activeRealtimeCloudRequestCount/$maxConcurrent"
                } else {
                    ""
                }
                val now = System.currentTimeMillis()
                val recentAttempt = latestRealtimeAttemptText.isNotBlank() &&
                    now - latestRealtimeAttemptAt <= REALTIME_RESULT_STATUS_HOLD_MS &&
                    latestRealtimeAttemptAt >= latestRealtimeResultAt
                val recentResult = latestRealtimeResultNames.isNotBlank() &&
                    now - latestRealtimeResultAt <= REALTIME_RESULT_STATUS_HOLD_MS
                if (recentAttempt) {
                    "实时识别：$latestRealtimeAttemptText$facePart$crowdPart$cloudPart"
                } else if (recentResult) {
                    "实时识别：$latestRealtimeResultNames$facePart$crowdPart$cloudPart"
                } else {
                    "实时画面已连接，正在本地检测$facePart$crowdPart$cloudPart"
                }
            }
            snapshot.clientConnected -> "眼镜已连接，正在等待实时画面..."
            snapshot.listening -> "实时视频接收已启动，请在乐奇 App 开始推流"
            snapshot.running -> "正在启动实时视频接收..."
            else -> "等待眼镜实时画面。请先在设置页启动实时视频接收。"
        }
    }

    private fun checkRealtimePreviewHealth(source: String) {
        if (!isRealtimeRecognitionPageActive) {
            return
        }
        val now = System.currentTimeMillis()
        val snapshot = latestRtmpReceiverSnapshot
        if (!snapshot.running || snapshot.videoTags <= 0L) {
            return
        }
        val dataAgeMs = if (snapshot.lastDataAtMs > 0L) now - snapshot.lastDataAtMs else -1L
        val hasFreshRtmpData = snapshot.lastDataAtMs <= 0L ||
            dataAgeMs <= REALTIME_PREVIEW_HEALTH_RTMP_DATA_FRESH_MS
        if (!hasFreshRtmpData) {
            return
        }
        val receiveAgeMs = if (lastRtmpPreviewFrameReceivedAt > 0L) {
            now - lastRtmpPreviewFrameReceivedAt
        } else {
            -1L
        }
        val renderAgeMs = if (lastRtmpPreviewFrameRenderedAt > 0L) {
            now - lastRtmpPreviewFrameRenderedAt
        } else {
            -1L
        }
        val renderRunningMs = if (rtmpPreviewRenderStartedAt > 0L) {
            now - rtmpPreviewRenderStartedAt
        } else {
            -1L
        }
        val detectRunningMs = if (rtmpPreviewFaceDetectionStartedAt > 0L) {
            now - rtmpPreviewFaceDetectionStartedAt
        } else {
            -1L
        }
        when {
            lastRtmpPreviewFrameReceivedAt <= 0L &&
                snapshot.videoTags >= REALTIME_PREVIEW_HEALTH_MIN_VIDEO_TAGS -> {
                maybeLogRealtimePreviewHealth(
                    reason = "rtmp_has_video_no_activity_preview",
                    source = source,
                    now = now,
                    extra = "videoTags=${snapshot.videoTags}, dataAgeMs=$dataAgeMs"
                )
            }
            receiveAgeMs >= REALTIME_PREVIEW_RECEIVE_STALL_MS -> {
                maybeLogRealtimePreviewHealth(
                    reason = "activity_preview_receive_stall",
                    source = source,
                    now = now,
                    extra = "receiveAgeMs=$receiveAgeMs, videoTags=${snapshot.videoTags}, dataAgeMs=$dataAgeMs"
                )
            }
            lastRtmpPreviewFrameRenderedAt <= 0L &&
                lastRtmpPreviewFrameReceivedAt > 0L &&
                receiveAgeMs >= REALTIME_PREVIEW_RENDER_STALL_MS -> {
                maybeLogRealtimePreviewHealth(
                    reason = "preview_received_not_rendered",
                    source = source,
                    now = now,
                    extra = "receiveAgeMs=$receiveAgeMs, latestFrame=$latestRtmpPreviewFrameIndex"
                )
            }
            renderAgeMs >= REALTIME_PREVIEW_RENDER_STALL_MS &&
                receiveAgeMs >= 0L &&
                receiveAgeMs < REALTIME_PREVIEW_RECEIVE_STALL_MS -> {
                maybeLogRealtimePreviewHealth(
                    reason = "preview_render_stall",
                    source = source,
                    now = now,
                    extra = "renderAgeMs=$renderAgeMs, receiveAgeMs=$receiveAgeMs, " +
                        "latestFrame=$latestRtmpPreviewFrameIndex, renderedFrame=$lastRtmpPreviewRenderedFrameIndex"
                )
            }
            isRtmpPreviewRenderRunning &&
                renderRunningMs >= REALTIME_PREVIEW_RENDER_STALL_MS -> {
                maybeLogRealtimePreviewHealth(
                    reason = "render_worker_stall",
                    source = source,
                    now = now,
                    extra = "renderRunningMs=$renderRunningMs, latestFrame=$latestRtmpPreviewFrameIndex"
                )
            }
            isRtmpPreviewFaceDetectionRunning &&
                detectRunningMs >= REALTIME_PREVIEW_PROCESS_STALL_MS -> {
                maybeLogRealtimePreviewHealth(
                    reason = "detect_worker_stall",
                    source = source,
                    now = now,
                    extra = "detectRunningMs=$detectRunningMs, latestFrame=$latestRtmpPreviewFrameIndex"
                )
            }
        }
    }

    private fun maybeLogRealtimePreviewHealth(
        reason: String,
        source: String,
        now: Long,
        extra: String = ""
    ) {
        val key = "$reason|render=$isRtmpPreviewRenderRunning|detect=$isRtmpPreviewFaceDetectionRunning"
        if (now - lastRtmpPreviewHealthLogAt < REALTIME_PREVIEW_HEALTH_LOG_INTERVAL_MS &&
            key == lastRtmpPreviewHealthLogKey
        ) {
            return
        }
        lastRtmpPreviewHealthLogAt = now
        lastRtmpPreviewHealthLogKey = key
        val snapshot = latestRtmpReceiverSnapshot
        val dataAgeMs = if (snapshot.lastDataAtMs > 0L) now - snapshot.lastDataAtMs else -1L
        val receiveAgeMs = if (lastRtmpPreviewFrameReceivedAt > 0L) now - lastRtmpPreviewFrameReceivedAt else -1L
        val renderAgeMs = if (lastRtmpPreviewFrameRenderedAt > 0L) now - lastRtmpPreviewFrameRenderedAt else -1L
        val renderRunningMs = if (rtmpPreviewRenderStartedAt > 0L) now - rtmpPreviewRenderStartedAt else -1L
        val detectRunningMs = if (rtmpPreviewFaceDetectionStartedAt > 0L) now - rtmpPreviewFaceDetectionStartedAt else -1L
        recordDiagnostic(
            "实时预览健康告警: source=$source, reason=$reason, " +
                "connected=${snapshot.clientConnected}, remote=${snapshot.remoteAddress}, " +
                "videoTags=${snapshot.videoTags}, bytes=${snapshot.totalPayloadBytes}, dataAgeMs=$dataAgeMs, " +
                "latestFrame=$latestRtmpPreviewFrameIndex, renderedFrame=$lastRtmpPreviewRenderedFrameIndex, " +
                "receiveAgeMs=$receiveAgeMs, renderAgeMs=$renderAgeMs, " +
                "renderRunning=$isRtmpPreviewRenderRunning, renderRunningMs=$renderRunningMs, " +
                "detectRunning=$isRtmpPreviewFaceDetectionRunning, detectRunningMs=$detectRunningMs, " +
                "preview=${latestRtmpPreviewFrameWidth}x$latestRtmpPreviewFrameHeight/${latestRtmpPreviewFrameBytes}B" +
                if (extra.isNotBlank()) ", $extra" else ""
        )
    }

    private fun isRealtimeCloudRecognitionAllowed(): Boolean {
        if (!latestRtmpReceiverSnapshot.running) {
            return false
        }
        if (isRealtimeRecognitionPageActive) {
            return true
        }
        if (!::binding.isInitialized || binding.historyPage.visibility != View.VISIBLE) {
            return false
        }
        return hasRealtimePendingCloudWork()
    }

    private fun hasRealtimePendingCloudWork(): Boolean {
        return synchronized(realtimeTrackLock) {
            activeRealtimeCloudRequestCount > 0 ||
                realtimePersonTracks.any { it.cloudRequestInFlight || it.bestCandidate != null }
        }
    }

    private fun realtimeTrackDiagnosticsSummary(now: Long): String {
        return synchronized(realtimeTrackLock) {
            var active = 0
            var pending = 0
            var inFlight = 0
            var noFaceSuppressed = 0
            var cooldown = 0
            var historyCandidates = 0
            realtimePersonTracks.forEach { track ->
                val trackActive = now - track.lastSeenAt <= REALTIME_TRACK_STALE_MS ||
                    track.bestCandidate != null ||
                    track.cloudRequestInFlight
                if (trackActive) {
                    active += 1
                }
                if (track.bestCandidate != null && !track.cloudRequestInFlight) {
                    pending += 1
                }
                if (track.cloudRequestInFlight) {
                    inFlight += 1
                }
                if (track.noFaceSuppressedUntil > now) {
                    noFaceSuppressed += 1
                }
                if (track.lastCloudUploadAt > 0L &&
                    now - track.lastCloudUploadAt < realtimeCloudCooldownMs(track)
                ) {
                    cooldown += 1
                }
                historyCandidates += track.candidateHistory.size
            }
            "total:${realtimePersonTracks.size},active:$active,pending:$pending,inFlight:$inFlight," +
                "cooldown:$cooldown,noFaceSuppressed:$noFaceSuppressed,history:$historyCandidates"
        }
    }

    private fun currentRealtimeRecognitionSessionId(): Long {
        return realtimeRecognitionSession.get()
    }

    private fun bumpRealtimeRecognitionSession(reason: String): Long {
        val sessionId = realtimeRecognitionSession.incrementAndGet()
        recordDiagnostic("实时识别会话更新: session=$sessionId, reason=$reason")
        return sessionId
    }

    private fun isRealtimeCloudPlanStillCurrent(plan: RealtimeCloudUploadPlan): Boolean {
        return plan.sessionId == currentRealtimeRecognitionSessionId()
    }

    private fun clearRealtimeRecognitionCandidates(reason: String) {
        var removedTracks = 0
        var clearedBestCandidates = 0
        var inFlightTracks = 0
        synchronized(realtimeTrackLock) {
            val iterator = realtimePersonTracks.iterator()
            while (iterator.hasNext()) {
                val track = iterator.next()
                if (track.bestCandidate != null) {
                    clearedBestCandidates += 1
                    track.bestCandidate = null
                }
                track.candidateHistory.clear()
                if (track.cloudRequestInFlight) {
                    inFlightTracks += 1
                } else {
                    iterator.remove()
                    removedTracks += 1
                }
            }
            lastRealtimeCloudRequestAt = 0L
        }
        synchronized(realtimeCloudBudgetLock) {
            realtimeCloudHttpRequestStarts.clear()
            realtimeTrackLastRescueAt.clear()
            activeRealtimeCloudHttpRequestCount = 0
            lastRealtimeRescueHttpAt = 0L
            lastRealtimeCloudBudgetLogAt = 0L
            lastRealtimeCloudBudgetLogKey = ""
        }
        val clearedRescueCandidates = synchronized(realtimeRescueLock) {
            val count = realtimeRescueCandidates.size
            realtimeRescueCandidates.clear()
            activeRealtimeRescueRequestCount = 0
            lastRealtimeNoLocalFaceRescueCandidateAt = 0L
            count
        }
        val clearedLookbackFrames = synchronized(realtimeLookbackLock) {
            val count = realtimeLookbackFrames.size
            realtimeLookbackFrames.clear()
            lastRealtimeLookbackFrameAt = 0L
            count
        }
        lastRealtimeCrowdModeAt = 0L
        lastRealtimeCrowdModeLogged = false
        latestRealtimeOverlaySnapshot = null
        latestRealtimeFaceCount = -1
        latestRealtimeValidFaceCount = -1
        latestRealtimeUploadableFaceCount = -1
        lastRealtimeFaceDetectAt = 0L
        lastRealtimeDetectAt = 0L
        lastRealtimeDetectFrame = 0L
        lastRealtimeDetectDetectedCount = -1
        lastRealtimeDetectValidCount = -1
        lastRealtimeDetectUploadableCount = -1
        lastRealtimeDetectWaitingCount = -1
        lastRealtimeDetectLowQualityCount = -1
        lastRealtimeDetectCostMs = -1L
        lastRealtimeEvaluateCostMs = -1L
        lastRealtimeDetectBitmapWidth = 0
        lastRealtimeDetectBitmapHeight = 0
        lastRealtimeDetectBytes = 0
        lastRealtimeCloudCompletedAt = 0L
        lastRealtimeCloudTrackId = 0L
        lastRealtimeCloudFrame = 0L
        lastRealtimeCloudResult = "none"
        lastRealtimeCloudCostMs = -1L
        lastRealtimeCloudMessage = ""
        latestRealtimeAttemptText = ""
        latestRealtimeAttemptAt = 0L
        lastRealtimeLoggedFaceCount = -1
        lastRealtimeLoggedValidFaceCount = -1
        lastRealtimeLoggedUploadableFaceCount = -1
        if (removedTracks > 0 || clearedBestCandidates > 0 || inFlightTracks > 0 ||
            clearedLookbackFrames > 0 || clearedRescueCandidates > 0
        ) {
            recordDiagnostic(
                "实时识别候选清理: reason=$reason, removedTracks=$removedTracks, " +
                    "clearedCandidates=$clearedBestCandidates, inFlight=$inFlightTracks, " +
                    "lookbackFrames=$clearedLookbackFrames, rescueCandidates=$clearedRescueCandidates, " +
                    "session=${currentRealtimeRecognitionSessionId()}"
            )
        }
    }

    private fun evaluateRealtimeFaces(
        bitmap: Bitmap,
        faces: List<Face>,
        crowdModeForFrame: Boolean
    ): Map<Face, RealtimeFaceEvaluation> {
        return evaluateRealtimeFacesWithSummary(bitmap, faces, crowdModeForFrame).evaluations
    }

    private fun evaluateRealtimeFacesWithSummary(
        bitmap: Bitmap,
        faces: List<Face>,
        crowdModeForFrame: Boolean
    ): RealtimeFaceEvaluationSummary {
        if (faces.isEmpty()) {
            return RealtimeFaceEvaluationSummary.empty()
        }
        val evaluations = IdentityHashMap<Face, RealtimeFaceEvaluation>(faces.size)
        var skippedInvalid = 0
        var skippedTooSmall = 0
        var skippedSmallArea = 0
        var skippedPose = 0
        var skippedLikelyFalsePositive = 0
        var skippedQuality = 0
        var uploadableCount = 0
        val minAreaRatio = realtimeMinFaceAreaRatio(crowdModeForFrame)
        faces.forEach { face ->
            val faceRect = clippedRect(Rect(face.boundingBox), bitmap.width, bitmap.height)
            if (faceRect == null) {
                skippedInvalid += 1
                return@forEach
            }
            if (faceRect.width() < 12 || faceRect.height() < 12) {
                skippedTooSmall += 1
                return@forEach
            }
            val faceAreaRatio = faceRect.width().toFloat() * faceRect.height().toFloat() /
                (bitmap.width.toFloat() * bitmap.height.toFloat()).coerceAtLeast(1f)
            if (faceAreaRatio < minAreaRatio) {
                skippedSmallArea += 1
                return@forEach
            }
            if (kotlin.math.abs(face.headEulerAngleY) > REALTIME_MAX_UPLOAD_YAW ||
                kotlin.math.abs(face.headEulerAngleX) > REALTIME_MAX_UPLOAD_PITCH
            ) {
                skippedPose += 1
                return@forEach
            }
            val score = scoreRealtimeFaceCandidate(bitmap, face, faceRect)
            val cloudGateQuality = realtimeCloudGateQuality(score)
            val skinRatio = estimateRealtimeFaceSkinRatio(bitmap, faceRect)
            if (isLikelyRealtimeFalsePositive(
                    bitmapWidth = bitmap.width,
                    bitmapHeight = bitmap.height,
                    faceRect = faceRect,
                    faceAreaRatio = faceAreaRatio,
                    quality = score.qualityScore,
                    yaw = face.headEulerAngleY,
                    pitch = face.headEulerAngleX,
                    skinRatio = skinRatio,
                    crowdMode = crowdModeForFrame
                )
            ) {
                skippedLikelyFalsePositive += 1
                return@forEach
            }
            val cloudDecision = realtimeCloudCandidateDecision(
                faceRect = faceRect,
                faceAreaRatio = faceAreaRatio,
                quality = cloudGateQuality,
                yaw = face.headEulerAngleY,
                pitch = face.headEulerAngleX,
                skinRatio = skinRatio,
                crowdMode = crowdModeForFrame
            )
            if (cloudDecision.canUpload) {
                uploadableCount += 1
            } else {
                skippedQuality += 1
            }
            evaluations[face] = RealtimeFaceEvaluation(
                faceRect = faceRect,
                qualityScore = score.qualityScore,
                dispatchScore = score.dispatchScore,
                cloudGateQuality = cloudGateQuality,
                sharpnessScore = score.sharpnessScore,
                areaBonus = score.areaBonus,
                canUpload = cloudDecision.canUpload,
                rejectReason = cloudDecision.rejectReason,
                faceAreaRatio = faceAreaRatio,
                faceCenterX = faceRect.centerX().toFloat() / bitmap.width.toFloat(),
                faceCenterY = faceRect.centerY().toFloat() / bitmap.height.toFloat(),
                skinRatio = skinRatio
            )
        }
        return RealtimeFaceEvaluationSummary(
            evaluations = evaluations,
            detectedCount = faces.size,
            eligibleCount = evaluations.size,
            uploadableCount = uploadableCount,
            skippedInvalid = skippedInvalid,
            skippedTooSmall = skippedTooSmall,
            skippedSmallArea = skippedSmallArea,
            skippedPose = skippedPose,
            skippedLikelyFalsePositive = skippedLikelyFalsePositive,
            skippedQuality = skippedQuality
        )
    }

    private fun realtimeMinFaceAreaRatio(crowdMode: Boolean): Float {
        return if (crowdMode) {
            REALTIME_CROWD_MIN_FACE_AREA_RATIO
        } else {
            REALTIME_MIN_FACE_AREA_RATIO
        }
    }

    private fun registerRtmpReceiverBroadcasts() {
        if (isRtmpReceiverBroadcastRegistered) {
            return
        }
        RtmpReceiverService.onPreviewFrameListener = { jpegBytes, width, height, decodedFrames ->
            enqueueRtmpPreviewFrame(jpegBytes, width, height, decodedFrames)
        }
        val filter = IntentFilter().apply {
            addAction(RtmpReceiverService.ACTION_STATUS)
            addAction(RtmpReceiverService.ACTION_LOG)
            addAction(RtmpReceiverService.ACTION_PREVIEW)
        }
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
            registerReceiver(rtmpReceiverBroadcastReceiver, filter, RECEIVER_NOT_EXPORTED)
        } else {
            @Suppress("DEPRECATION")
            registerReceiver(rtmpReceiverBroadcastReceiver, filter)
        }
        isRtmpReceiverBroadcastRegistered = true
        latestRtmpReceiverSnapshot = RtmpReceiverService.latestSnapshot
        renderRtmpReceiverSnapshot(latestRtmpReceiverSnapshot)
    }

    private fun unregisterRtmpReceiverBroadcasts() {
        if (!isRtmpReceiverBroadcastRegistered) {
            RtmpReceiverService.onPreviewFrameListener = null
            return
        }
        try {
            unregisterReceiver(rtmpReceiverBroadcastReceiver)
        } catch (e: Exception) {
            recordDiagnostic("RTMP 接收服务广播注销失败", e)
        }
        isRtmpReceiverBroadcastRegistered = false
        RtmpReceiverService.onPreviewFrameListener = null
    }

    private fun rtmpSnapshotFromIntent(intent: Intent): EmbeddedRtmpReceiver.Snapshot {
        return EmbeddedRtmpReceiver.Snapshot(
            running = intent.getBooleanExtra(RtmpReceiverService.EXTRA_RUNNING, false),
            listening = intent.getBooleanExtra(RtmpReceiverService.EXTRA_LISTENING, false),
            clientConnected = intent.getBooleanExtra(RtmpReceiverService.EXTRA_CONNECTED, false),
            port = intent.getIntExtra(RtmpReceiverService.EXTRA_PORT, RTMP_RECEIVER_PORT),
            expectedStreamKey = intent.getStringExtra(RtmpReceiverService.EXTRA_STREAM_KEY).orEmpty()
                .ifBlank { DEFAULT_RTMP_STREAM_KEY },
            appName = intent.getStringExtra(RtmpReceiverService.EXTRA_APP_NAME).orEmpty(),
            streamName = intent.getStringExtra(RtmpReceiverService.EXTRA_STREAM_NAME).orEmpty(),
            remoteAddress = intent.getStringExtra(RtmpReceiverService.EXTRA_REMOTE).orEmpty(),
            videoTags = intent.getLongExtra(RtmpReceiverService.EXTRA_VIDEO_TAGS, 0L),
            audioTags = intent.getLongExtra(RtmpReceiverService.EXTRA_AUDIO_TAGS, 0L),
            metadataTags = intent.getLongExtra(RtmpReceiverService.EXTRA_METADATA_TAGS, 0L),
            totalPayloadBytes = intent.getLongExtra(RtmpReceiverService.EXTRA_BYTES, 0L),
            keyframeCount = intent.getLongExtra(RtmpReceiverService.EXTRA_KEYFRAMES, 0L),
            avcSequenceHeaderCount = intent.getLongExtra(RtmpReceiverService.EXTRA_AVC_SEQ, 0L),
            lastVideoCodec = intent.getStringExtra(RtmpReceiverService.EXTRA_VIDEO_CODEC).orEmpty(),
            lastAudioCodec = intent.getStringExtra(RtmpReceiverService.EXTRA_AUDIO_CODEC).orEmpty(),
            firstVideoAtMs = intent.getLongExtra(RtmpReceiverService.EXTRA_FIRST_VIDEO_AT, 0L),
            lastDataAtMs = intent.getLongExtra(RtmpReceiverService.EXTRA_LAST_DATA_AT, 0L),
            message = intent.getStringExtra(RtmpReceiverService.EXTRA_MESSAGE).orEmpty().ifBlank {
                "RTMP 接收服务状态已更新"
            }
        )
    }

    private fun updateRealtimeFaceCandidates(
        bitmap: Bitmap,
        faces: List<Face>,
        decodedFrames: Long,
        frameBytes: ByteArray,
        faceEvaluationSummary: RealtimeFaceEvaluationSummary,
        crowdModeForFrame: Boolean
    ) {
        val now = System.currentTimeMillis()
        val faceEvaluations = faceEvaluationSummary.evaluations
        synchronized(realtimeTrackLock) {
            realtimePersonTracks.removeAll { now - it.lastSeenAt > REALTIME_TRACK_STALE_MS }
        }
        val usedTrackIdsInFrame = mutableSetOf<Long>()
        faces.forEach { face ->
            val evaluation = faceEvaluations[face] ?: return@forEach
            val candidate = buildRealtimeFaceCandidate(
                bitmap = bitmap,
                face = face,
                evaluation = evaluation,
                decodedFrames = decodedFrames,
                now = now,
                frameBytes = frameBytes
            ) ?: return@forEach
            synchronized(realtimeTrackLock) {
                val track = findOrCreateRealtimeTrackLocked(
                    candidate = candidate,
                    now = now,
                    crowdMode = crowdModeForFrame,
                    excludedTrackIds = usedTrackIdsInFrame
                )
                usedTrackIdsInFrame.add(track.id)
                track.lastSeenAt = now
                track.trackingId = candidate.trackingId ?: track.trackingId
                track.centerX = candidate.faceCenterX
                track.centerY = candidate.faceCenterY
                track.sizeRatio = candidate.faceAreaRatio
                addRealtimeCandidateHistoryLocked(track, candidate, now)
                val oldBest = track.bestCandidate
                if (oldBest == null || isRealtimeCandidateBetterForCloud(candidate, oldBest)) {
                    track.bestCandidate = candidate
                }
            }
        }
        val activeTrackCount = synchronized(realtimeTrackLock) {
            realtimePersonTracks.count { track ->
                now - track.lastSeenAt <= REALTIME_TRACK_STALE_MS &&
                    (track.bestCandidate != null || track.cloudRequestInFlight)
            }
        }
        updateRealtimeCrowdModeState(faceEvaluationSummary.eligibleCount, activeTrackCount, now)
        maybeStartRealtimeCloudRecognition()
    }

    private fun buildRealtimeFaceCandidate(
        bitmap: Bitmap,
        face: Face,
        evaluation: RealtimeFaceEvaluation,
        decodedFrames: Long,
        now: Long,
        frameBytes: ByteArray
    ): RealtimeFaceCandidate? {
        if (!evaluation.canUpload) {
            return null
        }
        val faceRect = evaluation.faceRect
        val yaw = face.headEulerAngleY
        val pitch = face.headEulerAngleX
        return try {
            RealtimeFaceCandidate(
                createdAt = now,
                decodedFrames = decodedFrames,
                qualityScore = evaluation.qualityScore,
                dispatchScore = evaluation.dispatchScore,
                cloudGateQuality = evaluation.cloudGateQuality,
                sharpnessScore = evaluation.sharpnessScore,
                areaBonus = evaluation.areaBonus,
                frameBytes = frameBytes,
                frameWidth = bitmap.width,
                frameHeight = bitmap.height,
                faceRectInFrame = Rect(faceRect),
                faceAreaRatio = evaluation.faceAreaRatio,
                faceCenterX = evaluation.faceCenterX,
                faceCenterY = evaluation.faceCenterY,
                yaw = yaw,
                pitch = pitch,
                roll = face.headEulerAngleZ,
                skinRatio = evaluation.skinRatio,
                trackingId = face.trackingId
            )
        } catch (e: Exception) {
            recordDiagnostic("实时视频候选创建失败: frame=$decodedFrames", e)
            null
        }
    }

    private fun enqueueRealtimeRescueCandidates(
        bitmap: Bitmap,
        faces: List<Face>,
        decodedFrames: Long,
        frameBytes: ByteArray,
        faceEvaluationSummary: RealtimeFaceEvaluationSummary,
        crowdModeForFrame: Boolean
    ) {
        if (!isRealtimeRecognitionPageActive || !latestRtmpReceiverSnapshot.running || frameBytes.isEmpty()) {
            return
        }
        val now = System.currentTimeMillis()
        val rescueCandidate = buildRealtimeRescueCandidate(
            bitmap = bitmap,
            faces = faces,
            decodedFrames = decodedFrames,
            frameBytes = frameBytes,
            faceEvaluationSummary = faceEvaluationSummary,
            crowdModeForFrame = crowdModeForFrame,
            now = now
        ) ?: return
        synchronized(realtimeRescueLock) {
            trimRealtimeRescueCandidatesLocked(now)
            val candidates = (realtimeRescueCandidates.toList() + rescueCandidate)
                .distinctBy { "${it.decodedFrames}|${it.reason}|${it.sourceTrackId ?: 0L}" }
                .sortedWith(realtimeRescueComparator())
                .take(REALTIME_RESCUE_QUEUE_MAX)
            realtimeRescueCandidates.clear()
            realtimeRescueCandidates.addAll(candidates)
        }
        recordDiagnostic(
            "实时救援候选入池: reason=${rescueCandidate.reason}, priority=${rescueCandidate.priority}, " +
                "track=${rescueCandidate.sourceTrackId ?: "-"}, frame=${rescueCandidate.decodedFrames}, " +
                "faces=${rescueCandidate.localFaceCount}, maxFaceNum=${rescueCandidate.maxFaceNum}, " +
                "q=${rescueCandidate.qualityScore}, p=${rescueCandidate.dispatchScore}, " +
                "skin=${String.format(Locale.CHINA, "%.3f", rescueCandidate.skinRatio)}, " +
                "rect=${rescueCandidate.sourceFaceRect?.let { "${it.width()}x${it.height()}" } ?: "full"}"
        )
        maybeStartRealtimeFrameRescue()
    }

    private fun buildRealtimeRescueCandidate(
        bitmap: Bitmap,
        faces: List<Face>,
        decodedFrames: Long,
        frameBytes: ByteArray,
        faceEvaluationSummary: RealtimeFaceEvaluationSummary,
        crowdModeForFrame: Boolean,
        now: Long
    ): RealtimeRescueCandidate? {
        if (faceEvaluationSummary.uploadableCount > 0) {
            return null
        }
        val faceRescue = faces
            .asSequence()
            .mapNotNull { face ->
                val rect = clippedRect(Rect(face.boundingBox), bitmap.width, bitmap.height) ?: return@mapNotNull null
                val minSide = minOf(rect.width(), rect.height())
                val areaRatio = rect.width().toFloat() * rect.height().toFloat() /
                    (bitmap.width.toFloat() * bitmap.height.toFloat()).coerceAtLeast(1f)
                if (minSide < REALTIME_RESCUE_MIN_FACE_SIDE_PX ||
                    areaRatio < REALTIME_RESCUE_MIN_FACE_AREA_RATIO ||
                    abs(face.headEulerAngleY) > REALTIME_MAX_UPLOAD_YAW ||
                    abs(face.headEulerAngleX) > REALTIME_MAX_UPLOAD_PITCH
                ) {
                    return@mapNotNull null
                }
                val evaluation = faceEvaluationSummary.evaluations[face]
                val score = if (evaluation != null) {
                    RealtimeFaceScore(
                        qualityScore = evaluation.qualityScore,
                        dispatchScore = evaluation.dispatchScore,
                        sharpnessScore = evaluation.sharpnessScore,
                        areaBonus = evaluation.areaBonus
                    )
                } else {
                    scoreRealtimeFaceCandidate(bitmap, face, rect)
                }
                val skinRatio = evaluation?.skinRatio ?: estimateRealtimeFaceSkinRatio(bitmap, rect)
                val smallEnoughForRescue = minSide <= REALTIME_RESCUE_MAX_PRIMARY_FACE_SIDE_PX ||
                    evaluation?.canUpload == false ||
                    abs(face.headEulerAngleY) >= REALTIME_SIDE_PROFILE_MIN_YAW
                if (!smallEnoughForRescue) {
                    return@mapNotNull null
                }
                if (skinRatio < REALTIME_RESCUE_MIN_SKIN_RATIO &&
                    score.qualityScore < REALTIME_RESCUE_MIN_QUALITY
                ) {
                    return@mapNotNull null
                }
                val centerX = rect.centerX().toFloat() / bitmap.width.toFloat().coerceAtLeast(1f)
                val centerY = rect.centerY().toFloat() / bitmap.height.toFloat().coerceAtLeast(1f)
                val trackHint = realtimeRescueTrackHint(centerX, centerY, areaRatio, now, crowdModeForFrame)
                if (trackHint?.matchedRecently == true) {
                    return@mapNotNull null
                }
                val priority = when {
                    trackHint == null || trackHint.neverUploaded -> 0
                    now - trackHint.lastSeenAt >= REALTIME_LOST_FACE_FLUSH_MS -> 1
                    trackHint.consecutiveFailures > 0 -> 2
                    else -> 3
                }
                RealtimeRescueCandidate(
                    createdAt = now,
                    decodedFrames = decodedFrames,
                    frameBytes = frameBytes.copyOf(),
                    frameWidth = bitmap.width,
                    frameHeight = bitmap.height,
                    reason = when {
                        minSide < REALTIME_MIN_CLOUD_FACE_SIDE_PX -> "small_face_rescue"
                        abs(face.headEulerAngleY) >= REALTIME_SIDE_PROFILE_MIN_YAW -> "side_face_rescue"
                        else -> "quality_gate_rescue"
                    },
                    priority = priority,
                    sourceTrackId = trackHint?.trackId,
                    sourceFaceRect = Rect(rect),
                    qualityScore = score.qualityScore,
                    dispatchScore = score.dispatchScore,
                    skinRatio = skinRatio,
                    localFaceCount = faces.size,
                    maxFaceNum = faces.size.coerceIn(1, REALTIME_RESCUE_CLOUD_MAX_FACE_NUM)
                )
            }
            .sortedWith(realtimeRescueComparator())
            .firstOrNull()
        if (faceRescue != null) {
            return faceRescue
        }
        if (faces.isEmpty() && now - lastRealtimeNoLocalFaceRescueCandidateAt >= REALTIME_RESCUE_NO_LOCAL_FACE_INTERVAL_MS) {
            val analysis = analyzeVideoRescueRegion(bitmap, emptyList())
            if (analysis.skinRatio >= REALTIME_RESCUE_NO_LOCAL_MIN_SKIN_RATIO) {
                lastRealtimeNoLocalFaceRescueCandidateAt = now
                return RealtimeRescueCandidate(
                    createdAt = now,
                    decodedFrames = decodedFrames,
                    frameBytes = frameBytes.copyOf(),
                    frameWidth = bitmap.width,
                    frameHeight = bitmap.height,
                    reason = "no_local_face_skin_rescue",
                    priority = 4,
                    sourceTrackId = null,
                    sourceFaceRect = analysis.regionRect?.toPixelRect(bitmap.width, bitmap.height),
                    qualityScore = 0,
                    dispatchScore = (analysis.skinRatio * VIDEO_RESCUE_SKIN_SCORE_WEIGHT).roundToInt(),
                    skinRatio = analysis.skinRatio,
                    localFaceCount = 0,
                    maxFaceNum = minOf(3, REALTIME_RESCUE_CLOUD_MAX_FACE_NUM)
                )
            }
        }
        return null
    }

    private fun realtimeRescueTrackHint(
        centerX: Float,
        centerY: Float,
        areaRatio: Float,
        now: Long,
        crowdMode: Boolean
    ): RealtimeRescueTrackHint? {
        return synchronized(realtimeTrackLock) {
            realtimePersonTracks
                .filter { now - it.lastSeenAt <= REALTIME_TRACK_STALE_MS }
                .mapNotNull { track ->
                    val dx = track.centerX - centerX
                    val dy = track.centerY - centerY
                    val distance = sqrt(dx * dx + dy * dy)
                    val centerLimit = if (crowdMode) {
                        REALTIME_CROWD_TRACK_MAX_CENTER_DISTANCE
                    } else {
                        REALTIME_TRACK_MAX_CENTER_DISTANCE
                    }
                    val sizeLimit = if (crowdMode) {
                        REALTIME_CROWD_TRACK_MAX_SIZE_RATIO
                    } else {
                        REALTIME_TRACK_MAX_SIZE_RATIO
                    }
                    if (distance > centerLimit ||
                        realtimeSizeRatio(track.sizeRatio, areaRatio) > sizeLimit
                    ) {
                        return@mapNotNull null
                    }
                    track to distance
                }
                .minByOrNull { it.second }
                ?.first
                ?.let { track ->
                    RealtimeRescueTrackHint(
                        trackId = track.id,
                        lastSeenAt = track.lastSeenAt,
                        neverUploaded = track.lastCloudUploadAt <= 0L,
                        matchedRecently = track.lastMatchedNames.isNotBlank() &&
                            track.lastCloudUploadAt > 0L &&
                            now - track.lastCloudUploadAt < REALTIME_RECORD_DUPLICATE_WINDOW_MS,
                        consecutiveFailures = track.consecutiveNoFaceCount + track.consecutiveNoMatchCount
                    )
                }
        }
    }

    private fun trimRealtimeRescueCandidatesLocked(now: Long) {
        val iterator = realtimeRescueCandidates.iterator()
        while (iterator.hasNext()) {
            val candidate = iterator.next()
            if (now - candidate.createdAt > REALTIME_RESCUE_CANDIDATE_MAX_AGE_MS) {
                iterator.remove()
            }
        }
        while (realtimeRescueCandidates.size > REALTIME_RESCUE_QUEUE_MAX) {
            realtimeRescueCandidates.removeLast()
        }
    }

    private fun realtimeRescueComparator(): Comparator<RealtimeRescueCandidate> {
        return compareBy<RealtimeRescueCandidate> { it.priority }
            .thenByDescending { it.dispatchScore }
            .thenByDescending { it.qualityScore }
            .thenByDescending { it.skinRatio }
            .thenBy { it.createdAt }
    }

    private fun maybeStartRealtimeFrameRescue() {
        if (!isRealtimeCloudRecognitionAllowed()) {
            return
        }
        val now = System.currentTimeMillis()
        val plan = synchronized(realtimeRescueLock) {
            trimRealtimeRescueCandidatesLocked(now)
            if (activeRealtimeRescueRequestCount >= REALTIME_RESCUE_MAX_IN_FLIGHT) {
                return
            }
            val candidate = realtimeRescueCandidates
                .sortedWith(realtimeRescueComparator())
                .firstOrNull() ?: return
            val permit = acquireRealtimeCloudHttpBudget(
                kind = "frame_rescue",
                trackId = candidate.sourceTrackId,
                rescue = true,
                now = now
            ) ?: return
            realtimeRescueCandidates.remove(candidate)
            activeRealtimeRescueRequestCount += 1
            RealtimeRescueUploadPlan(
                sessionId = currentRealtimeRecognitionSessionId(),
                candidate = candidate,
                budgetPermit = permit
            )
        }
        startRealtimeFrameRescueRecognition(plan)
    }

    private fun startRealtimeFrameRescueRecognition(plan: RealtimeRescueUploadPlan) {
        var budgetPermit: RealtimeCloudBudgetPermit? = plan.budgetPermit
        val rescue = plan.candidate
        recordDiagnostic(
            "实时救援云端识别入队: session=${plan.sessionId}, reason=${rescue.reason}, " +
                "track=${rescue.sourceTrackId ?: "-"}, frame=${rescue.decodedFrames}, " +
                "priority=${rescue.priority}, maxFaceNum=${rescue.maxFaceNum}, " +
                "q=${rescue.qualityScore}, p=${rescue.dispatchScore}, " +
                "skin=${String.format(Locale.CHINA, "%.3f", rescue.skinRatio)}, " +
                "ageMs=${System.currentTimeMillis() - rescue.createdAt}"
        )
        executeRealtimeCloudWorker("实时视频整帧救援") {
            try {
                if (plan.sessionId != currentRealtimeRecognitionSessionId()) {
                    recordDiagnostic(
                        "实时救援云端识别丢弃: session=${plan.sessionId}, " +
                            "currentSession=${currentRealtimeRecognitionSessionId()}, reason=会话已过期"
                    )
                    return@executeRealtimeCloudWorker
                }
                val upload = prepareRealtimeRescueUploadPayload(rescue)
                if (upload == null) {
                    recordDiagnostic(
                        "实时救援上传图生成失败: frame=${rescue.decodedFrames}, reason=${rescue.reason}"
                    )
                    return@executeRealtimeCloudWorker
                }
                val startedAt = System.currentTimeMillis()
                val permitForSearch = budgetPermit
                budgetPermit = null
                val result = searchRealtimeFaceOnCloudWithBudget(
                    "data:image/jpeg;base64,${Base64.encodeToString(upload.uploadBytes, Base64.NO_WRAP)}",
                    rescue.maxFaceNum,
                    "实时视频救援 frame=${rescue.decodedFrames} reason=${rescue.reason}",
                    kind = "frame_rescue",
                    trackId = rescue.sourceTrackId,
                    rescue = true,
                    existingPermit = permitForSearch
                )
                if (result == null) {
                    recordDiagnostic(
                        "实时救援云端识别跳过: frame=${rescue.decodedFrames}, reason=请求预算不足"
                    )
                    return@executeRealtimeCloudWorker
                }
                recordDiagnostic(
                    "实时救援云端识别返回: frame=${rescue.decodedFrames}, reason=${rescue.reason}, " +
                        "experts=${result.experts.size}, maxFaceNum=${rescue.maxFaceNum}, " +
                        "costMs=${System.currentTimeMillis() - startedAt}, message=${result.message.take(80)}"
                )
                val candidate = rescue.toRealtimeFaceCandidate()
                updateRealtimeCloudSummary(
                    trackId = rescue.sourceTrackId ?: 0L,
                    frame = rescue.decodedFrames,
                    result = when {
                        result.experts.isNotEmpty() -> "rescue_success(${result.experts.size})"
                        isNoFaceCloudResult(result) -> "rescue_noFace"
                        else -> "rescue_noMatch"
                    },
                    costMs = System.currentTimeMillis() - startedAt,
                    message = result.message
                )
                handleRealtimeCloudResult(rescue.sourceTrackId ?: 0L, candidate, upload, result)
            } finally {
                budgetPermit?.let {
                    releaseRealtimeCloudHttpBudget(it)
                    budgetPermit = null
                }
                synchronized(realtimeRescueLock) {
                    activeRealtimeRescueRequestCount = (activeRealtimeRescueRequestCount - 1).coerceAtLeast(0)
                }
                maybeStartRealtimeCloudRecognition()
                maybeStartRealtimeFrameRescue()
            }
        }
    }

    private fun prepareRealtimeRescueUploadPayload(rescue: RealtimeRescueCandidate): RealtimeUploadPayload? {
        val frameBitmap = BitmapFactory.decodeByteArray(rescue.frameBytes, 0, rescue.frameBytes.size)
        if (frameBitmap == null) {
            recordDiagnostic(
                "实时救援上传图准备失败: 原始帧解码失败 frame=${rescue.decodedFrames}, bytes=${rescue.frameBytes.size}"
            )
            return null
        }
        var uploadBitmap: Bitmap? = null
        return try {
            uploadBitmap = resizeBitmapToMaxSide(frameBitmap, VIDEO_MAX_UPLOAD_IMAGE_SIDE)
            val bitmapForUpload = uploadBitmap ?: frameBitmap
            val uploadBytes = bitmapToJpegBytes(bitmapForUpload, FACE_UPLOAD_JPEG_QUALITY)
            val sourceRect = Rect(0, 0, frameBitmap.width, frameBitmap.height)
            val localRect = rescue.sourceFaceRect
                ?.let {
                    scalePixelRectToFaceRect(
                        it,
                        frameBitmap.width,
                        frameBitmap.height,
                        bitmapForUpload.width,
                        bitmapForUpload.height
                    )
                }
                ?: FaceRect(0f, 0f, bitmapForUpload.width.toFloat(), bitmapForUpload.height.toFloat())
            RealtimeUploadPayload(
                uploadBytes = uploadBytes,
                uploadWidth = bitmapForUpload.width,
                uploadHeight = bitmapForUpload.height,
                localFaceRect = localRect,
                sourceCropRect = faceRectFromPixelRect(sourceRect),
                cropMode = "frame_rescue",
                cropWidth = sourceRect.width(),
                cropHeight = sourceRect.height()
            )
        } catch (e: Exception) {
            recordDiagnostic("实时救援上传图准备异常: frame=${rescue.decodedFrames}", e)
            null
        } finally {
            if (uploadBitmap != null && uploadBitmap !== frameBitmap) {
                try {
                    uploadBitmap.recycle()
                } catch (_: Exception) {
                }
            }
            try {
                frameBitmap.recycle()
            } catch (_: Exception) {
            }
        }
    }

    private fun RealtimeRescueCandidate.toRealtimeFaceCandidate(): RealtimeFaceCandidate {
        val rect = sourceFaceRect ?: Rect(0, 0, frameWidth.coerceAtLeast(1), frameHeight.coerceAtLeast(1))
        val areaRatio = rect.width().toFloat() * rect.height().toFloat() /
            (frameWidth.toFloat() * frameHeight.toFloat()).coerceAtLeast(1f)
        return RealtimeFaceCandidate(
            createdAt = createdAt,
            decodedFrames = decodedFrames,
            qualityScore = qualityScore,
            dispatchScore = dispatchScore,
            cloudGateQuality = qualityScore,
            sharpnessScore = qualityScore,
            areaBonus = 0,
            frameBytes = frameBytes,
            frameWidth = frameWidth,
            frameHeight = frameHeight,
            faceRectInFrame = Rect(rect),
            faceAreaRatio = areaRatio,
            faceCenterX = rect.centerX().toFloat() / frameWidth.toFloat().coerceAtLeast(1f),
            faceCenterY = rect.centerY().toFloat() / frameHeight.toFloat().coerceAtLeast(1f),
            yaw = 0f,
            pitch = 0f,
            roll = 0f,
            skinRatio = skinRatio,
            trackingId = null
        )
    }

    private fun isLikelyRealtimeFalsePositive(
        bitmapWidth: Int,
        bitmapHeight: Int,
        faceRect: Rect,
        faceAreaRatio: Float,
        quality: Int,
        yaw: Float,
        pitch: Float,
        skinRatio: Float,
        crowdMode: Boolean
    ): Boolean {
        if (bitmapWidth <= 0 || bitmapHeight <= 0 || faceRect.width() <= 0 || faceRect.height() <= 0) {
            return true
        }
        val minSide = minOf(faceRect.width(), faceRect.height())
        val maxSide = maxOf(faceRect.width(), faceRect.height())
        val aspectRatio = maxSide.toFloat() / minSide.toFloat().coerceAtLeast(1f)
        if (aspectRatio > REALTIME_MAX_FACE_BOX_ASPECT_RATIO) {
            return true
        }
        if (minSide < REALTIME_MIN_FACE_BOX_SIDE_PX) {
            return true
        }
        val smallSideLimit = if (crowdMode) {
            REALTIME_CROWD_SMALL_FACE_SIDE_PX
        } else {
            REALTIME_SMALL_FACE_SIDE_PX
        }
        val smallAreaLimit = if (crowdMode) {
            REALTIME_CROWD_SMALL_FACE_AREA_RATIO
        } else {
            REALTIME_SMALL_FACE_AREA_RATIO
        }
        val isSmallFace = minSide < smallSideLimit || faceAreaRatio < smallAreaLimit
        val touchesEdge = faceRect.left <= REALTIME_FACE_EDGE_MARGIN_PX ||
            faceRect.top <= REALTIME_FACE_EDGE_MARGIN_PX ||
            faceRect.right >= bitmapWidth - REALTIME_FACE_EDGE_MARGIN_PX ||
            faceRect.bottom >= bitmapHeight - REALTIME_FACE_EDGE_MARGIN_PX
        if (touchesEdge && isSmallFace) {
            return true
        }
        if (isSmallFace && skinRatio < REALTIME_SMALL_FACE_MIN_SKIN_RATIO) {
            return true
        }
        if (isSmallFace && quality < REALTIME_SMALL_FACE_MIN_QUALITY) {
            return true
        }
        if (abs(yaw) >= REALTIME_TINY_SIDE_FACE_YAW &&
            (minSide < REALTIME_TINY_SIDE_FACE_MIN_SIDE_PX ||
                skinRatio < REALTIME_TINY_SIDE_FACE_MIN_SKIN_RATIO)
        ) {
            return true
        }
        if (abs(pitch) >= REALTIME_TINY_FACE_MAX_PITCH &&
            isSmallFace &&
            quality < REALTIME_TINY_FACE_HIGH_PITCH_MIN_QUALITY
        ) {
            return true
        }
        return false
    }

    private fun estimateRealtimeFaceSkinRatio(bitmap: Bitmap, faceRect: Rect): Float {
        val rect = clippedRect(faceRect, bitmap.width, bitmap.height) ?: return 0f
        if (rect.width() <= 0 || rect.height() <= 0) {
            return 0f
        }
        val sampleSide = REALTIME_FACE_SKIN_SAMPLE_SIDE
        val stepX = maxOf(1, rect.width() / sampleSide)
        val stepY = maxOf(1, rect.height() / sampleSide)
        var total = 0
        var skin = 0
        var y = rect.top
        while (y < rect.bottom) {
            var x = rect.left
            while (x < rect.right) {
                val color = try {
                    bitmap.getPixel(x, y)
                } catch (_: Exception) {
                    0
                }
                if (isBroadSkinTonePixel(color)) {
                    skin += 1
                }
                total += 1
                x += stepX
            }
            y += stepY
        }
        return if (total <= 0) 0f else skin.toFloat() / total.toFloat()
    }

    private fun isBroadSkinTonePixel(color: Int): Boolean {
        val r = (color shr 16) and 0xFF
        val g = (color shr 8) and 0xFF
        val b = color and 0xFF
        val max = maxOf(r, g, b)
        val min = minOf(r, g, b)
        if (max < 35 || max - min < 8) {
            return false
        }
        val y = (77 * r + 150 * g + 29 * b) shr 8
        val cb = ((-43 * r - 85 * g + 128 * b) shr 8) + 128
        val cr = ((128 * r - 107 * g - 21 * b) shr 8) + 128
        val ycbcrSkin = y >= 35 && cb in 65..155 && cr in 105..200
        val rgbSkin = r >= 35 &&
            g >= 25 &&
            b >= 18 &&
            r >= (g * 0.70f).roundToInt() &&
            r >= (b * 0.60f).roundToInt()
        return ycbcrSkin || rgbSkin
    }

    private fun realtimeCloudCandidateDecision(
        faceRect: Rect,
        faceAreaRatio: Float,
        quality: Int,
        yaw: Float,
        pitch: Float,
        skinRatio: Float,
        crowdMode: Boolean
    ): RealtimeCloudCandidateDecision {
        val minAreaRatio = if (crowdMode) {
            REALTIME_CROWD_MIN_FACE_AREA_RATIO
        } else {
            REALTIME_MIN_FACE_AREA_RATIO
        }
        if (faceAreaRatio < minAreaRatio) {
            return RealtimeCloudCandidateDecision(false, "脸太小")
        }
        if (abs(yaw) > REALTIME_MAX_UPLOAD_YAW || abs(pitch) > REALTIME_MAX_UPLOAD_PITCH) {
            return RealtimeCloudCandidateDecision(false, "角度大")
        }
        val minSide = minOf(faceRect.width(), faceRect.height())
        if (minSide < REALTIME_HARD_MIN_CLOUD_FACE_SIDE_PX) {
            return RealtimeCloudCandidateDecision(false, "脸太小")
        }
        val minCloudSide = if (crowdMode) {
            REALTIME_CROWD_MIN_CLOUD_FACE_SIDE_PX
        } else {
            REALTIME_MIN_CLOUD_FACE_SIDE_PX
        }
        if (minSide < minCloudSide) {
            val exceptionalTinyFace = quality >= REALTIME_TINY_CLOUD_FACE_MIN_QUALITY &&
                abs(yaw) <= REALTIME_TINY_CLOUD_FACE_MAX_YAW &&
                abs(pitch) <= REALTIME_TINY_CLOUD_FACE_MAX_PITCH &&
                skinRatio >= REALTIME_TINY_CLOUD_FACE_MIN_SKIN_RATIO
            if (!exceptionalTinyFace) {
                return RealtimeCloudCandidateDecision(false, "脸偏小")
            }
        }
        val sideProfile = abs(yaw) >= REALTIME_SIDE_PROFILE_MIN_YAW
        val minQuality = if (sideProfile) {
            if (crowdMode) REALTIME_CROWD_SIDE_PROFILE_MIN_UPLOAD_QUALITY else REALTIME_SIDE_PROFILE_MIN_UPLOAD_QUALITY
        } else {
            if (crowdMode) REALTIME_CROWD_MIN_UPLOAD_QUALITY else REALTIME_MIN_UPLOAD_QUALITY
        }
        if (quality < minQuality) {
            return RealtimeCloudCandidateDecision(false, if (sideProfile) "侧脸质量低" else "质量低")
        }
        return RealtimeCloudCandidateDecision(true, "")
    }

    private fun findOrCreateRealtimeTrackLocked(
        candidate: RealtimeFaceCandidate,
        now: Long,
        crowdMode: Boolean,
        excludedTrackIds: Set<Long> = emptySet()
    ): RealtimePersonTrack {
        candidate.trackingId?.let { trackingId ->
            realtimePersonTracks.firstOrNull {
                it.id !in excludedTrackIds &&
                    it.trackingId == trackingId &&
                    now - it.lastSeenAt <= REALTIME_TRACK_STALE_MS &&
                    isRealtimeTrackGeometryCompatible(
                        track = it,
                        candidate = candidate,
                        now = now,
                        crowdMode = crowdMode,
                        trackingIdMatched = true
                    )
            }?.let { return it }
        }
        val matched = realtimePersonTracks
            .filter { it.id !in excludedTrackIds && now - it.lastSeenAt <= REALTIME_TRACK_MATCH_GAP_MS }
            .minByOrNull { track ->
                val distance = realtimeTrackDistance(track, candidate)
                if (isRealtimeTrackGeometryCompatible(track, candidate, now, crowdMode, trackingIdMatched = false)) {
                    distance
                } else {
                    Float.MAX_VALUE
                }
            }
            ?.takeIf {
                isRealtimeTrackGeometryCompatible(it, candidate, now, crowdMode, trackingIdMatched = false)
            }
        if (matched != null) {
            return matched
        }
        val track = RealtimePersonTrack(
            id = ++realtimeTrackSequence,
            trackingId = candidate.trackingId,
            firstSeenAt = now,
            lastSeenAt = now,
            centerX = candidate.faceCenterX,
            centerY = candidate.faceCenterY,
            sizeRatio = candidate.faceAreaRatio
        )
        realtimePersonTracks.add(track)
        return track
    }

    private fun realtimeTrackDistance(track: RealtimePersonTrack, candidate: RealtimeFaceCandidate): Float {
        return kotlin.math.sqrt(
            (track.centerX - candidate.faceCenterX) * (track.centerX - candidate.faceCenterX) +
                (track.centerY - candidate.faceCenterY) * (track.centerY - candidate.faceCenterY)
        )
    }

    private fun isRealtimeTrackGeometryCompatible(
        track: RealtimePersonTrack,
        candidate: RealtimeFaceCandidate,
        now: Long,
        crowdMode: Boolean,
        trackingIdMatched: Boolean
    ): Boolean {
        val gapMs = now - track.lastSeenAt
        val baseCenterDistance = if (crowdMode) {
            REALTIME_CROWD_TRACK_MAX_CENTER_DISTANCE
        } else {
            REALTIME_TRACK_MAX_CENTER_DISTANCE
        }
        val baseSizeRatio = if (crowdMode) {
            REALTIME_CROWD_TRACK_MAX_SIZE_RATIO
        } else {
            REALTIME_TRACK_MAX_SIZE_RATIO
        }
        val relaxedByFreshTrackingId = trackingIdMatched && gapMs <= REALTIME_TRACK_ID_TRUST_GAP_MS
        val centerLimit = if (relaxedByFreshTrackingId) {
            baseCenterDistance * REALTIME_TRACK_ID_CENTER_RELAX_RATIO
        } else {
            baseCenterDistance
        }
        val sizeLimit = if (relaxedByFreshTrackingId) {
            baseSizeRatio * REALTIME_TRACK_ID_SIZE_RELAX_RATIO
        } else {
            baseSizeRatio
        }
        return realtimeTrackDistance(track, candidate) <= centerLimit &&
            realtimeSizeRatio(track.sizeRatio, candidate.faceAreaRatio) <= sizeLimit
    }

    private fun realtimeSizeRatio(left: Float, right: Float): Float {
        val minValue = minOf(left, right).coerceAtLeast(0.0001f)
        val maxValue = maxOf(left, right).coerceAtLeast(minValue)
        return maxValue / minValue
    }

    private fun addRealtimeCandidateHistoryLocked(
        track: RealtimePersonTrack,
        candidate: RealtimeFaceCandidate,
        now: Long
    ) {
        track.candidateHistory.addLast(candidate)
        trimRealtimeCandidateHistoryLocked(track, now)
    }

    private fun trimRealtimeCandidateHistoryLocked(track: RealtimePersonTrack, now: Long) {
        while (track.candidateHistory.size > REALTIME_TRACK_CANDIDATE_HISTORY_MAX) {
            track.candidateHistory.removeFirst()
        }
        while (true) {
            val first = track.candidateHistory.peekFirst() ?: break
            if (now - first.createdAt <= REALTIME_TRACK_CANDIDATE_HISTORY_MS) {
                break
            }
            track.candidateHistory.removeFirst()
        }
    }

    private fun isRealtimeCandidateBetterForCloud(
        candidate: RealtimeFaceCandidate,
        currentBest: RealtimeFaceCandidate
    ): Boolean {
        val qualityGain = candidate.qualityScore - currentBest.qualityScore
        val suitabilityGain = realtimeCandidateCloudSuitabilityScore(candidate) -
            realtimeCandidateCloudSuitabilityScore(currentBest)
        if (qualityGain >= REALTIME_BEST_CANDIDATE_QUALITY_GAIN) {
            return true
        }
        if (suitabilityGain >= REALTIME_BEST_CANDIDATE_SUITABILITY_GAIN) {
            return true
        }
        val closeQuality = candidate.qualityScore >= currentBest.qualityScore - REALTIME_BEST_CANDIDATE_CLOSE_QUALITY_GAP
        val poseImproved =
            abs(candidate.yaw) + REALTIME_BEST_CANDIDATE_POSE_GAIN_DEGREES < abs(currentBest.yaw) ||
                abs(candidate.pitch) + REALTIME_BEST_CANDIDATE_POSE_GAIN_DEGREES < abs(currentBest.pitch)
        val sizeImproved = candidate.faceAreaRatio >= currentBest.faceAreaRatio * REALTIME_BEST_CANDIDATE_AREA_RATIO
        return closeQuality && (poseImproved || sizeImproved)
    }

    private fun realtimeCandidateCloudSuitabilityScore(candidate: RealtimeFaceCandidate): Int {
        val posePenalty = (abs(candidate.yaw) * 6f + abs(candidate.pitch) * 8f + abs(candidate.roll) * 3f).roundToInt()
        val edgePenalty = if (isRealtimeCandidateTouchingFrameEdge(candidate)) 220 else 0
        val skinPenalty = if (candidate.skinRatio < REALTIME_SMALL_FACE_MIN_SKIN_RATIO) 120 else 0
        return candidate.dispatchScore - posePenalty - edgePenalty - skinPenalty
    }

    private fun realtimeCloudGateQuality(score: RealtimeFaceScore): Int {
        return (score.qualityScore + minOf(score.areaBonus, REALTIME_FACE_AREA_GATE_BONUS_MAX))
            .coerceAtLeast(0)
    }

    private fun isRealtimeCandidateTouchingFrameEdge(candidate: RealtimeFaceCandidate): Boolean {
        return candidate.faceRectInFrame.left <= REALTIME_FACE_EDGE_MARGIN_PX ||
            candidate.faceRectInFrame.top <= REALTIME_FACE_EDGE_MARGIN_PX ||
            candidate.faceRectInFrame.right >= candidate.frameWidth - REALTIME_FACE_EDGE_MARGIN_PX ||
            candidate.faceRectInFrame.bottom >= candidate.frameHeight - REALTIME_FACE_EDGE_MARGIN_PX
    }

    private fun updateRealtimeCrowdModeState(currentValidFaceCount: Int, activeTrackCount: Int, now: Long) {
        if (currentValidFaceCount >= REALTIME_CROWD_MODE_MIN_FACES ||
            activeTrackCount >= REALTIME_CROWD_MODE_MIN_TRACKS
        ) {
            lastRealtimeCrowdModeAt = now
        }
        val active = isRealtimeCrowdModeActive(now)
        if (active != lastRealtimeCrowdModeLogged) {
            lastRealtimeCrowdModeLogged = active
            val maxConcurrent = realtimeCloudMaxConcurrentRequests(now)
            val collectWindow = realtimeCloudCollectWindowMs(now)
            val dispatchInterval = realtimeCloudDispatchIntervalMs(now)
            recordDiagnostic(
                "实时多人高峰模式${if (active) "开启" else "关闭"}: " +
                    "validFaces=$currentValidFaceCount, tracks=$activeTrackCount, " +
                    "maxCloud=$maxConcurrent, collectMs=$collectWindow, dispatchMs=$dispatchInterval"
            )
        }
    }

    private fun isRealtimeCrowdModeActive(now: Long): Boolean {
        return lastRealtimeCrowdModeAt > 0L && now - lastRealtimeCrowdModeAt <= REALTIME_CROWD_MODE_HOLD_MS
    }

    private fun realtimeCloudMaxConcurrentRequests(now: Long): Int {
        return if (isRealtimeCrowdModeActive(now)) {
            REALTIME_CROWD_CLOUD_MAX_CONCURRENT_REQUESTS
        } else {
            REALTIME_CLOUD_MAX_CONCURRENT_REQUESTS
        }
    }

    private fun realtimeCloudCollectWindowMs(now: Long): Long {
        return if (isRealtimeCrowdModeActive(now)) {
            REALTIME_CROWD_CLOUD_COLLECT_WINDOW_MS
        } else {
            REALTIME_CLOUD_COLLECT_WINDOW_MS
        }
    }

    private fun realtimeCloudDispatchIntervalMs(now: Long): Long {
        return if (isRealtimeCrowdModeActive(now)) {
            REALTIME_CROWD_CLOUD_DISPATCH_INTERVAL_MS
        } else {
            REALTIME_CLOUD_DISPATCH_INTERVAL_MS
        }
    }

    private fun realtimeImmediateUploadQuality(now: Long): Int {
        return if (isRealtimeCrowdModeActive(now)) {
            REALTIME_CROWD_IMMEDIATE_UPLOAD_QUALITY
        } else {
            REALTIME_IMMEDIATE_UPLOAD_QUALITY
        }
    }

    private fun trimRealtimeCloudBudgetLocked(now: Long) {
        while (true) {
            val first = realtimeCloudHttpRequestStarts.peekFirst() ?: break
            if (now - first <= REALTIME_CLOUD_HTTP_ROLLING_WINDOW_MS) {
                break
            }
            realtimeCloudHttpRequestStarts.removeFirst()
        }
        val iterator = realtimeTrackLastRescueAt.iterator()
        while (iterator.hasNext()) {
            val entry = iterator.next()
            if (now - entry.value > REALTIME_RESCUE_TRACK_NO_FACE_COOLDOWN_MS * 3) {
                iterator.remove()
            }
        }
    }

    private fun realtimeCloudBudgetAvailableSlots(now: Long): Int {
        return synchronized(realtimeCloudBudgetLock) {
            trimRealtimeCloudBudgetLocked(now)
            val activeSlots = REALTIME_CLOUD_HTTP_MAX_IN_FLIGHT - activeRealtimeCloudHttpRequestCount
            val rollingSlots = REALTIME_CLOUD_HTTP_ROLLING_MAX_REQUESTS - realtimeCloudHttpRequestStarts.size
            minOf(activeSlots, rollingSlots).coerceAtLeast(0)
        }
    }

    private fun acquireRealtimeCloudHttpBudget(
        kind: String,
        trackId: Long?,
        rescue: Boolean,
        now: Long = System.currentTimeMillis()
    ): RealtimeCloudBudgetPermit? {
        synchronized(realtimeCloudBudgetLock) {
            trimRealtimeCloudBudgetLocked(now)
            val blockReason = when {
                activeRealtimeCloudHttpRequestCount >= REALTIME_CLOUD_HTTP_MAX_IN_FLIGHT ->
                    "http_inflight_full"
                realtimeCloudHttpRequestStarts.size >= REALTIME_CLOUD_HTTP_ROLLING_MAX_REQUESTS ->
                    "rolling_window_full"
                rescue && now - lastRealtimeRescueHttpAt < REALTIME_RESCUE_MIN_INTERVAL_MS ->
                    "rescue_interval"
                rescue && trackId != null &&
                    now - (realtimeTrackLastRescueAt[trackId] ?: 0L) < REALTIME_RESCUE_TRACK_NO_FACE_COOLDOWN_MS ->
                    "track_rescue_cooldown"
                else -> ""
            }
            if (blockReason.isNotBlank()) {
                maybeLogRealtimeCloudBudgetBlocked(
                    kind = kind,
                    trackId = trackId,
                    rescue = rescue,
                    reason = blockReason,
                    now = now
                )
                return null
            }
            activeRealtimeCloudHttpRequestCount += 1
            realtimeCloudHttpRequestStarts.addLast(now)
            if (rescue) {
                lastRealtimeRescueHttpAt = now
                if (trackId != null) {
                    realtimeTrackLastRescueAt[trackId] = now
                }
            }
            return RealtimeCloudBudgetPermit(
                kind = kind,
                trackId = trackId,
                rescue = rescue,
                startedAt = now
            )
        }
    }

    private fun releaseRealtimeCloudHttpBudget(permit: RealtimeCloudBudgetPermit) {
        synchronized(realtimeCloudBudgetLock) {
            activeRealtimeCloudHttpRequestCount = (activeRealtimeCloudHttpRequestCount - 1).coerceAtLeast(0)
        }
    }

    private fun maybeLogRealtimeCloudBudgetBlocked(
        kind: String,
        trackId: Long?,
        rescue: Boolean,
        reason: String,
        now: Long
    ) {
        val key = "$kind|$trackId|$rescue|$reason"
        if (now - lastRealtimeCloudBudgetLogAt < REALTIME_CLOUD_BUDGET_LOG_INTERVAL_MS &&
            key == lastRealtimeCloudBudgetLogKey
        ) {
            return
        }
        lastRealtimeCloudBudgetLogAt = now
        lastRealtimeCloudBudgetLogKey = key
        val snapshot = synchronized(realtimeCloudBudgetLock) {
            trimRealtimeCloudBudgetLocked(now)
            "httpActive=$activeRealtimeCloudHttpRequestCount/$REALTIME_CLOUD_HTTP_MAX_IN_FLIGHT, " +
                "rolling=${realtimeCloudHttpRequestStarts.size}/$REALTIME_CLOUD_HTTP_ROLLING_MAX_REQUESTS, " +
                "rescueSinceMs=${if (lastRealtimeRescueHttpAt > 0L) now - lastRealtimeRescueHttpAt else -1}"
        }
        recordDiagnostic(
            "实时云端请求预算拦截: kind=$kind, track=${trackId ?: "-"}, " +
                "rescue=$rescue, reason=$reason, $snapshot"
        )
    }

    private fun searchRealtimeFaceOnCloudWithBudget(
        imageDataUrl: String,
        maxFaceNum: Int,
        description: String,
        kind: String,
        trackId: Long?,
        rescue: Boolean,
        existingPermit: RealtimeCloudBudgetPermit? = null
    ): CloudFaceSearchResult? {
        val permit = existingPermit ?: acquireRealtimeCloudHttpBudget(
            kind = kind,
            trackId = trackId,
            rescue = rescue
        ) ?: return null
        return try {
            searchFaceOnCloudSync(imageDataUrl, maxFaceNum, description)
        } finally {
            releaseRealtimeCloudHttpBudget(permit)
        }
    }

    private fun maybeStartRealtimeCloudRecognition() {
        if (!isRealtimeCloudRecognitionAllowed()) {
            return
        }
        val now = System.currentTimeMillis()
        val sessionId = currentRealtimeRecognitionSessionId()
        val plans = synchronized(realtimeTrackLock) {
            val crowdMode = isRealtimeCrowdModeActive(now)
            val maxConcurrent = realtimeCloudMaxConcurrentRequests(now)
            val dispatchInterval = realtimeCloudDispatchIntervalMs(now)
            val collectWindow = realtimeCloudCollectWindowMs(now)
            val immediateQuality = realtimeImmediateUploadQuality(now)
            val pendingTracks = realtimePersonTracks.filter { track ->
                !track.cloudRequestInFlight && track.bestCandidate != null
            }
            val pendingCount = pendingTracks.size
            if (activeRealtimeCloudRequestCount >= maxConcurrent) {
                maybeLogRealtimeCloudScheduleWait(
                    reason = "并发已满",
                    now = now,
                    pendingCount = pendingCount,
                    activeCount = activeRealtimeCloudRequestCount,
                    maxConcurrent = maxConcurrent,
                    crowdMode = crowdMode,
                    collectWindow = collectWindow,
                    dispatchInterval = dispatchInterval,
                    detail = "active=$activeRealtimeCloudRequestCount/$maxConcurrent"
                )
                return
            }
            if (now - lastRealtimeCloudRequestAt < dispatchInterval) {
                maybeLogRealtimeCloudScheduleWait(
                    reason = "调度间隔未到",
                    now = now,
                    pendingCount = pendingCount,
                    activeCount = activeRealtimeCloudRequestCount,
                    maxConcurrent = maxConcurrent,
                    crowdMode = crowdMode,
                    collectWindow = collectWindow,
                    dispatchInterval = dispatchInterval,
                    detail = "sinceLastMs=${now - lastRealtimeCloudRequestAt}"
                )
                return
            }
            val planSlots = (maxConcurrent - activeRealtimeCloudRequestCount).coerceAtLeast(0)
            val budgetSlots = realtimeCloudBudgetAvailableSlots(now)
            if (budgetSlots <= 0) {
                maybeLogRealtimeCloudScheduleWait(
                    reason = "请求预算不足",
                    now = now,
                    pendingCount = pendingCount,
                    activeCount = activeRealtimeCloudRequestCount,
                    maxConcurrent = maxConcurrent,
                    crowdMode = crowdMode,
                    collectWindow = collectWindow,
                    dispatchInterval = dispatchInterval,
                    detail = "httpActive=$activeRealtimeCloudHttpRequestCount/$REALTIME_CLOUD_HTTP_MAX_IN_FLIGHT"
                )
                return
            }
            val availableSlots = minOf(planSlots, budgetSlots).coerceAtLeast(0)
            if (availableSlots <= 0) {
                maybeLogRealtimeCloudScheduleWait(
                    reason = "无可用槽位",
                    now = now,
                    pendingCount = pendingCount,
                    activeCount = activeRealtimeCloudRequestCount,
                    maxConcurrent = maxConcurrent,
                    crowdMode = crowdMode,
                    collectWindow = collectWindow,
                    dispatchInterval = dispatchInterval
                )
                return
            }
            var blockedCollectWindow = 0
            var blockedCooldown = 0
            var blockedBoth = 0
            var blockedNoFaceSuppress = 0
            var blockedLostFace = 0
            val readyPairs = pendingTracks
                .mapNotNull { track ->
                    val candidate = track.bestCandidate ?: return@mapNotNull null
                    val candidateAgeMs = now - candidate.createdAt
                    if (candidateAgeMs > REALTIME_CANDIDATE_MAX_AGE_MS) {
                        recordDiagnostic(
                "实时云端候选丢弃: track=${track.id}, reason=候选过期, " +
                                "ageMs=$candidateAgeMs, frame=${candidate.decodedFrames}, " +
                                "q=${candidate.qualityScore}, p=${candidate.dispatchScore}, " +
                                "area=${String.format(Locale.CHINA, "%.4f", candidate.faceAreaRatio)}, " +
                                "rect=${candidate.faceRectInFrame.width()}x${candidate.faceRectInFrame.height()}"
                        )
                        track.bestCandidate = null
                        return@mapNotNull null
                    }
                    if (isRealtimeNoFaceSuppressed(track, candidate, now)) {
                        blockedNoFaceSuppress += 1
                        return@mapNotNull null
                    }
                    val lostFaceFlush = now - track.lastSeenAt >= REALTIME_LOST_FACE_FLUSH_MS
                    val oldEnough = now - track.firstSeenAt >= collectWindow ||
                        candidate.qualityScore >= immediateQuality ||
                        (crowdMode && now - track.lastSeenAt >= REALTIME_CROWD_LOST_FACE_UPLOAD_MS) ||
                        lostFaceFlush
                    val cooldownMs = realtimeCloudCooldownMs(track)
                    val cooldownDone = now - track.lastCloudUploadAt >= cooldownMs
                    val qualityJump = isRealtimeQualityJumpCandidate(track, candidate, now)
                    val lostFaceCooldownBypass = isRealtimeLostFaceCooldownBypassAllowed(track, candidate, now)
                    val canUploadPlan = cooldownDone || qualityJump || lostFaceCooldownBypass
                    if (oldEnough && canUploadPlan) {
                        track to candidate
                    } else {
                        val collectBlocked = !oldEnough
                        val cooldownBlocked = !cooldownDone && !qualityJump && !lostFaceCooldownBypass
                        when {
                            collectBlocked && cooldownBlocked -> blockedBoth += 1
                            collectBlocked -> blockedCollectWindow += 1
                            cooldownBlocked -> blockedCooldown += 1
                        }
                        if (now - track.lastSeenAt >= REALTIME_LOST_FACE_FLUSH_MS) {
                            blockedLostFace += 1
                        }
                        null
                    }
                }
            if (readyPairs.isEmpty()) {
                val newest = pendingTracks
                    .mapNotNull { it.bestCandidate }
                    .maxByOrNull { it.qualityScore }
                maybeLogRealtimeCloudScheduleWait(
                    reason = "候选未满足上传条件",
                    now = now,
                    pendingCount = pendingCount,
                    activeCount = activeRealtimeCloudRequestCount,
                    maxConcurrent = maxConcurrent,
                    crowdMode = crowdMode,
                    collectWindow = collectWindow,
                    dispatchInterval = dispatchInterval,
                    detail = "collectBlocked=$blockedCollectWindow, cooldownBlocked=$blockedCooldown, both=$blockedBoth" +
                        ", noFaceBlocked=$blockedNoFaceSuppress" +
                        ", lostFaceWaiting=$blockedLostFace" +
                        if (newest != null) {
                            ", bestQ=${newest.qualityScore}, bestGateQ=${newest.cloudGateQuality}, " +
                                "bestP=${newest.dispatchScore}, " +
                                "bestAgeMs=${now - newest.createdAt}, bestFrame=${newest.decodedFrames}"
                        } else {
                            ""
                        }
                )
            }
            readyPairs
                .sortedWith(
                    compareBy<Pair<RealtimePersonTrack, RealtimeFaceCandidate>> {
                        realtimeCloudDispatchPriority(it.first)
                    }
                        .thenByDescending { it.second.dispatchScore }
                        .thenByDescending { it.second.qualityScore }
                        .thenByDescending { it.second.faceAreaRatio }
                )
                .take(availableSlots)
                .mapIndexedNotNull { index, (track, candidate) ->
                    val budgetPermit = acquireRealtimeCloudHttpBudget(
                        kind = "primary",
                        trackId = track.id,
                        rescue = false,
                        now = now
                    ) ?: return@mapIndexedNotNull null
                    val inCooldown = track.lastCloudUploadAt > 0L &&
                        now - track.lastCloudUploadAt < realtimeCloudCooldownMs(track)
                    val lostFaceFlush = now - track.lastSeenAt >= REALTIME_LOST_FACE_FLUSH_MS
                    val lostFaceCooldownBypass = isRealtimeLostFaceCooldownBypassAllowed(track, candidate, now)
                    val crowdLostFace = crowdMode && now - track.lastSeenAt >= REALTIME_CROWD_LOST_FACE_UPLOAD_MS
                    val reason = when {
                        lostFaceFlush && inCooldown && lostFaceCooldownBypass ->
                            "lost_face_flush_cooldown_bypass(prevQ=${track.lastCloudUploadQuality})"
                        lostFaceFlush && inCooldown -> "lost_face_flush_quality_jump(prevQ=${track.lastCloudUploadQuality})"
                        lostFaceFlush -> "lost_face_flush"
                        crowdLostFace && inCooldown -> "crowd_lost_face_quality_jump(prevQ=${track.lastCloudUploadQuality})"
                        crowdLostFace -> "crowd_lost_face"
                        inCooldown -> "quality_jump(prevQ=${track.lastCloudUploadQuality})"
                        crowdMode -> "crowd_peak"
                        else -> "cooldown_ready"
                    }
                    track.lastCloudUploadAt = now
                    track.lastCloudUploadQuality = candidate.qualityScore
                    track.lastCloudUploadAreaRatio = candidate.faceAreaRatio
                    track.lastCloudUploadFaceWidth = candidate.faceRectInFrame.width()
                    track.lastCloudUploadFaceHeight = candidate.faceRectInFrame.height()
                    track.bestCandidate = null
                    track.cloudRequestInFlight = true
                    activeRealtimeCloudRequestCount += 1
                    RealtimeCloudUploadPlan(
                        sessionId = sessionId,
                        trackId = track.id,
                        candidate = candidate,
                        reason = reason,
                        activeCountAtStart = activeRealtimeCloudRequestCount,
                        maxConcurrent = maxConcurrent,
                        crowdMode = crowdMode,
                        batchIndex = index + 1,
                        noFaceCountAtStart = track.consecutiveNoFaceCount,
                        noFaceSuppressedUntilAtStart = track.noFaceSuppressedUntil,
                        initialBudgetPermit = budgetPermit
                    )
                }
                .also {
                    if (it.isNotEmpty()) {
                        lastRealtimeCloudRequestAt = now
                    }
                }
        }
        if (plans.isEmpty()) {
            return
        }
        plans.forEach { plan ->
            startRealtimeCloudRecognition(plan)
        }
    }

    private fun maybeLogRealtimeCloudScheduleWait(
        reason: String,
        now: Long,
        pendingCount: Int,
        activeCount: Int,
        maxConcurrent: Int,
        crowdMode: Boolean,
        collectWindow: Long,
        dispatchInterval: Long,
        detail: String = ""
    ) {
        if (pendingCount <= 0) {
            return
        }
        val key = "$reason|p=$pendingCount|a=$activeCount|m=$maxConcurrent|crowd=$crowdMode|$detail"
        if (now - lastRealtimeCloudScheduleWaitLogAt < REALTIME_CLOUD_SCHEDULE_WAIT_LOG_INTERVAL_MS &&
            key == lastRealtimeCloudScheduleWaitLogKey
        ) {
            return
        }
        lastRealtimeCloudScheduleWaitLogAt = now
        lastRealtimeCloudScheduleWaitLogKey = key
        recordDiagnostic(
            "实时云端调度等待: reason=$reason, pending=$pendingCount, " +
                "active=$activeCount/$maxConcurrent, crowd=$crowdMode, " +
                "collectMs=$collectWindow, dispatchMs=$dispatchInterval" +
                if (detail.isNotBlank()) ", $detail" else ""
        )
    }

    private fun isRealtimeNoFaceSuppressed(
        track: RealtimePersonTrack,
        candidate: RealtimeFaceCandidate,
        now: Long
    ): Boolean {
        if (track.noFaceSuppressedUntil <= now) {
            return false
        }
        val qualityGain = candidate.qualityScore - track.lastNoFaceQuality
        val qualityRatio = candidate.qualityScore.toFloat() /
            track.lastNoFaceQuality.toFloat().coerceAtLeast(1f)
        val areaRatio = candidate.faceAreaRatio /
            track.lastNoFaceAreaRatio.coerceAtLeast(0.000001f)
        val absoluteHighQuality = isRealtimeNoFaceAbsoluteHighQualityBreakthrough(candidate)
        if (isRealtimeNoFaceBreakthrough(track, candidate)) {
            recordDiagnostic(
                "实时 NoFace 抑制被新候选突破: track=${track.id}, " +
                    "noFaceCount=${track.consecutiveNoFaceCount}, suppressLeftMs=${track.noFaceSuppressedUntil - now}, " +
                    "prevQ=${track.lastNoFaceQuality}, newQ=${candidate.qualityScore}, " +
                    "qualityGain=$qualityGain, qualityRatio=${String.format(Locale.CHINA, "%.2f", qualityRatio)}, " +
                    "areaRatio=${String.format(Locale.CHINA, "%.2f", areaRatio)}, " +
                    "prevRect=${track.lastNoFaceFaceWidth}x${track.lastNoFaceFaceHeight}, " +
                    "newRect=${candidate.faceRectInFrame.width()}x${candidate.faceRectInFrame.height()}, " +
                    "absoluteHighQuality=$absoluteHighQuality"
            )
            track.noFaceSuppressedUntil = 0L
            return false
        }
        if (now - track.lastNoFaceSuppressLogAt >= REALTIME_NO_FACE_SUPPRESS_LOG_INTERVAL_MS) {
            track.lastNoFaceSuppressLogAt = now
            recordDiagnostic(
                "实时 NoFace 抑制上传: track=${track.id}, noFaceCount=${track.consecutiveNoFaceCount}, " +
                    "leftMs=${track.noFaceSuppressedUntil - now}, frame=${candidate.decodedFrames}, " +
                    "q=${candidate.qualityScore}, lastNoFaceQ=${track.lastNoFaceQuality}, " +
                    "area=${String.format(Locale.CHINA, "%.4f", candidate.faceAreaRatio)}, " +
                    "rect=${candidate.faceRectInFrame.width()}x${candidate.faceRectInFrame.height()}, " +
                    "lastRect=${track.lastNoFaceFaceWidth}x${track.lastNoFaceFaceHeight}"
            )
        }
        return true
    }

    private fun isRealtimeNoFaceBreakthrough(track: RealtimePersonTrack, candidate: RealtimeFaceCandidate): Boolean {
        if (track.noFaceSuppressedUntil <= 0L) {
            return true
        }
        val qualityGain = candidate.qualityScore - track.lastNoFaceQuality
        val qualityRatio = candidate.qualityScore.toFloat() /
            track.lastNoFaceQuality.toFloat().coerceAtLeast(1f)
        val areaRatio = candidate.faceAreaRatio /
            track.lastNoFaceAreaRatio.coerceAtLeast(0.000001f)
        val sizeImproved = areaRatio >= REALTIME_NO_FACE_SUPPRESS_AREA_BREAK_RATIO ||
            candidate.faceRectInFrame.width() >= track.lastNoFaceFaceWidth + REALTIME_NO_FACE_SUPPRESS_SIDE_BREAK_PX ||
            candidate.faceRectInFrame.height() >= track.lastNoFaceFaceHeight + REALTIME_NO_FACE_SUPPRESS_SIDE_BREAK_PX
        val qualityImproved = qualityGain >= REALTIME_NO_FACE_SUPPRESS_QUALITY_BREAK_GAIN ||
            qualityRatio >= REALTIME_NO_FACE_SUPPRESS_QUALITY_BREAK_RATIO
        return sizeImproved || qualityImproved || isRealtimeNoFaceAbsoluteHighQualityBreakthrough(candidate)
    }

    private fun isRealtimeNoFaceAbsoluteHighQualityBreakthrough(candidate: RealtimeFaceCandidate): Boolean {
        val minSide = minOf(candidate.faceRectInFrame.width(), candidate.faceRectInFrame.height())
        return candidate.qualityScore >= REALTIME_NO_FACE_BREAK_HIGH_QUALITY &&
            abs(candidate.yaw) <= REALTIME_NO_FACE_BREAK_MAX_YAW &&
            abs(candidate.pitch) <= REALTIME_NO_FACE_BREAK_MAX_PITCH &&
            minSide >= REALTIME_MIN_CLOUD_FACE_SIDE_PX
    }

    private fun updateRealtimeCloudSummary(
        trackId: Long,
        frame: Long,
        result: String,
        costMs: Long,
        message: String
    ) {
        lastRealtimeCloudCompletedAt = System.currentTimeMillis()
        lastRealtimeCloudTrackId = trackId
        lastRealtimeCloudFrame = frame
        lastRealtimeCloudResult = result
        lastRealtimeCloudCostMs = costMs
        lastRealtimeCloudMessage = message.take(120)
    }

    private fun updateRealtimeAttemptStatus(text: String) {
        latestRealtimeAttemptText = text.take(80)
        latestRealtimeAttemptAt = System.currentTimeMillis()
        runOnUiThread {
            if (::binding.isInitialized && isRealtimeRecognitionPageActive) {
                binding.tvMainRealtimeStatus.text = mainRealtimeStatusText(latestRtmpReceiverSnapshot)
            }
        }
    }

    private fun realtimeCloudDispatchPriority(track: RealtimePersonTrack): Int {
        val base = when {
            track.lastCloudUploadAt <= 0L -> 0
            track.lastMatchedNames.isBlank() -> 1
            else -> 2
        }
        val failurePenalty = if (track.lastCloudUploadAt <= 0L) {
            0
        } else {
            (track.consecutiveNoFaceCount + track.consecutiveNoMatchCount)
                .coerceIn(0, REALTIME_CLOUD_FAILURE_PRIORITY_PENALTY_MAX)
        }
        return base + failurePenalty
    }

    private fun shouldUseRealtimeWideUploadFirst(
        plan: RealtimeCloudUploadPlan,
        candidate: RealtimeFaceCandidate
    ): Boolean {
        val minSide = minOf(candidate.faceRectInFrame.width(), candidate.faceRectInFrame.height())
        val smallOrUnstableFace = minSide <= REALTIME_WIDE_FIRST_MAX_FACE_SIDE_PX ||
            abs(candidate.yaw) >= REALTIME_SIDE_PROFILE_MIN_YAW ||
            isRealtimeCandidateTouchingFrameEdge(candidate)
        return plan.noFaceCountAtStart > 0 ||
            smallOrUnstableFace
    }

    private fun shouldRetryRealtimePrimaryAfterWideNoMatch(
        candidate: RealtimeFaceCandidate,
        upload: RealtimeUploadPayload,
        result: CloudFaceSearchResult
    ): Boolean {
        if (upload.cropMode != "wide_retry" || result.experts.isNotEmpty()) {
            return false
        }
        val minSide = minOf(candidate.faceRectInFrame.width(), candidate.faceRectInFrame.height())
        val isNoFace = isNoFaceCloudResult(result)
        if (isNoFace && minSide < REALTIME_WIDE_NO_MATCH_PRIMARY_RETRY_MIN_FACE_SIDE_PX) {
            return false
        }
        val minQualityLimit = if (isNoFace) 250 else REALTIME_WIDE_NO_MATCH_PRIMARY_RETRY_MIN_QUALITY
        val minDispatchLimit = if (isNoFace) 400 else REALTIME_WIDE_NO_MATCH_PRIMARY_RETRY_MIN_DISPATCH_SCORE
        return minSide >= REALTIME_WIDE_NO_MATCH_PRIMARY_RETRY_MIN_FACE_SIDE_PX &&
            (candidate.qualityScore >= minQualityLimit || candidate.dispatchScore >= minDispatchLimit)
    }

    private fun startRealtimeCloudRecognition(plan: RealtimeCloudUploadPlan) {
        var candidate = plan.candidate
        var initialBudgetPermit: RealtimeCloudBudgetPermit? = plan.initialBudgetPermit
        recordDiagnostic(
                "实时云端识别候选入队: session=${plan.sessionId}, track=${plan.trackId}, reason=${plan.reason}, " +
                "mode=${if (plan.crowdMode) "crowd" else "normal"}, batch=${plan.batchIndex}, " +
                "active=${plan.activeCountAtStart}/${plan.maxConcurrent}, frame=${candidate.decodedFrames}, " +
                "q=${candidate.qualityScore}, gateQ=${candidate.cloudGateQuality}, " +
                "p=${candidate.dispatchScore}, sharp=${candidate.sharpnessScore}, " +
                "areaBonus=${candidate.areaBonus}, area=${String.format(Locale.CHINA, "%.4f", candidate.faceAreaRatio)}, " +
                "yaw=${candidate.yaw.roundToInt()}, ageMs=${System.currentTimeMillis() - candidate.createdAt}, " +
                "faceRect=${candidate.faceRectInFrame.width()}x${candidate.faceRectInFrame.height()}, " +
                "noFaceCount=${plan.noFaceCountAtStart}, " +
                "suppressedLeftMs=${(plan.noFaceSuppressedUntilAtStart - System.currentTimeMillis()).coerceAtLeast(0L)}"
        )
        runOnUiThread {
            if (::binding.isInitialized) {
                binding.tvMainRealtimeStatus.text =
                    if (plan.crowdMode) {
                        "多人高峰识别中... (${plan.activeCountAtStart}/${plan.maxConcurrent})"
                    } else {
                        "正在云端识别当前人脸... (${plan.activeCountAtStart}/${plan.maxConcurrent})"
                    }
            }
        }
        executeRealtimeCloudWorker("实时视频云端识别") {
            try {
                if (!isRealtimeCloudPlanStillCurrent(plan)) {
                    recordDiagnostic(
                        "实时云端识别候选丢弃: session=${plan.sessionId}, currentSession=${currentRealtimeRecognitionSessionId()}, " +
                            "track=${plan.trackId}, reason=会话已过期"
                    )
                    return@executeRealtimeCloudWorker
                }
                candidate = selectRealtimeLookbackCandidate(
                    trackId = plan.trackId,
                    original = candidate,
                    crowdMode = plan.crowdMode
                )
                if (!isRealtimeCloudPlanStillCurrent(plan)) {
                    recordDiagnostic(
                        "实时云端识别候选丢弃: session=${plan.sessionId}, currentSession=${currentRealtimeRecognitionSessionId()}, " +
                            "track=${plan.trackId}, frame=${candidate.decodedFrames}, reason=回看后会话已过期"
                    )
                    return@executeRealtimeCloudWorker
                }
                val preferWideUpload = shouldUseRealtimeWideUploadFirst(plan, candidate)
                val upload = prepareRealtimeUploadPayload(candidate, wideRetry = preferWideUpload)
                if (upload == null) {
                    updateRealtimeCloudSummary(
                        trackId = plan.trackId,
                        frame = candidate.decodedFrames,
                        result = "upload_failed",
                        costMs = -1L,
                        message = "上传图生成失败"
                    )
                    recordDiagnostic(
                        "实时云端识别候选上传图生成失败: track=${plan.trackId}, frame=${candidate.decodedFrames}"
                    )
                    return@executeRealtimeCloudWorker
                }
                recordDiagnostic(
                        "实时云端识别候选采用: session=${plan.sessionId}, track=${plan.trackId}, reason=${plan.reason}, " +
                        "frame=${candidate.decodedFrames}, q=${candidate.qualityScore}, " +
                        "gateQ=${candidate.cloudGateQuality}, p=${candidate.dispatchScore}, wideFirst=$preferWideUpload, " +
                        "ageMs=${System.currentTimeMillis() - candidate.createdAt}, " +
                        "faceRect=${candidate.faceRectInFrame.width()}x${candidate.faceRectInFrame.height()}, " +
                        "crop=${upload.cropWidth}x${upload.cropHeight}, mode=${upload.cropMode}, " +
                        "upload=${upload.uploadWidth}x${upload.uploadHeight}, bytes=${upload.uploadBytes.size}"
                )
                val base64 = Base64.encodeToString(upload.uploadBytes, Base64.NO_WRAP)
                val cloudStartedAt = System.currentTimeMillis()
                val initialPermit = initialBudgetPermit
                initialBudgetPermit = null
                var result = searchRealtimeFaceOnCloudWithBudget(
                    "data:image/jpeg;base64,$base64",
                    1,
                    "实时视频 track=${plan.trackId} frame=${candidate.decodedFrames} mode=${if (plan.crowdMode) "crowd" else "normal"}",
                    kind = "primary",
                    trackId = plan.trackId,
                    rescue = false,
                    existingPermit = initialPermit
                ) ?: run {
                    updateRealtimeCloudSummary(
                        trackId = plan.trackId,
                        frame = candidate.decodedFrames,
                        result = "budget_blocked",
                        costMs = -1L,
                        message = "实时云端请求预算不足"
                    )
                    recordDiagnostic(
                        "实时云端识别跳过: track=${plan.trackId}, frame=${candidate.decodedFrames}, reason=请求预算不足"
                    )
                    return@executeRealtimeCloudWorker
                }
                recordDiagnostic(
                    "实时云端识别返回: track=${plan.trackId}, frame=${candidate.decodedFrames}, " +
                        "experts=${result.experts.size}, costMs=${System.currentTimeMillis() - cloudStartedAt}, " +
                        "message=${result.message.take(80)}"
                )
                var finalUpload = upload
                if (result.experts.isEmpty() && isNoFaceCloudResult(result) && !preferWideUpload) {
                    recordDiagnostic(
                        "实时云端识别触发大范围重试: track=${plan.trackId}, frame=${candidate.decodedFrames}, " +
                            "firstMessage=${result.message}, firstUpload=${upload.uploadWidth}x${upload.uploadHeight}, " +
                            "firstCrop=${upload.cropWidth}x${upload.cropHeight}"
                    )
                    val retryUpload = prepareRealtimeUploadPayload(candidate, wideRetry = true)
                    if (retryUpload != null) {
                        recordDiagnostic(
                            "实时云端识别重试候选采用: track=${plan.trackId}, frame=${candidate.decodedFrames}, " +
                                "mode=${retryUpload.cropMode}, crop=${retryUpload.cropWidth}x${retryUpload.cropHeight}, " +
                                "upload=${retryUpload.uploadWidth}x${retryUpload.uploadHeight}, bytes=${retryUpload.uploadBytes.size}"
                        )
                        val retryStartedAt = System.currentTimeMillis()
                        val retryResult = searchRealtimeFaceOnCloudWithBudget(
                            "data:image/jpeg;base64,${Base64.encodeToString(retryUpload.uploadBytes, Base64.NO_WRAP)}",
                            1,
                            "实时视频重试 track=${plan.trackId} frame=${candidate.decodedFrames} mode=${if (plan.crowdMode) "crowd" else "normal"}",
                            kind = "wide_retry",
                            trackId = plan.trackId,
                            rescue = false
                        )
                        if (retryResult != null) {
                            result = retryResult
                            recordDiagnostic(
                                "实时云端识别重试返回: track=${plan.trackId}, frame=${candidate.decodedFrames}, " +
                                    "experts=${result.experts.size}, costMs=${System.currentTimeMillis() - retryStartedAt}, " +
                                    "message=${result.message.take(80)}"
                            )
                            finalUpload = retryUpload
                        } else {
                            recordDiagnostic(
                                "实时云端识别大范围重试跳过: track=${plan.trackId}, frame=${candidate.decodedFrames}, reason=请求预算不足"
                            )
                        }
                    } else {
                        recordDiagnostic(
                            "实时云端识别大范围重试跳过: track=${plan.trackId}, frame=${candidate.decodedFrames}, reason=重试上传图生成失败"
                        )
                    }
                }
                if (result.experts.isEmpty() &&
                    shouldRetryRealtimePrimaryAfterWideNoMatch(candidate, finalUpload, result)
                ) {
                    recordDiagnostic(
                        "实时云端识别触发主裁剪重试: track=${plan.trackId}, frame=${candidate.decodedFrames}, " +
                            "firstMessage=${result.message}, firstMode=${finalUpload.cropMode}, " +
                            "faceRect=${candidate.faceRectInFrame.width()}x${candidate.faceRectInFrame.height()}, " +
                            "q=${candidate.qualityScore}, p=${candidate.dispatchScore}"
                    )
                    val primaryRetryUpload = prepareRealtimeUploadPayload(candidate, wideRetry = false)
                    if (primaryRetryUpload != null) {
                        recordDiagnostic(
                            "实时云端识别主裁剪重试候选采用: track=${plan.trackId}, frame=${candidate.decodedFrames}, " +
                                "mode=${primaryRetryUpload.cropMode}, crop=${primaryRetryUpload.cropWidth}x${primaryRetryUpload.cropHeight}, " +
                                "upload=${primaryRetryUpload.uploadWidth}x${primaryRetryUpload.uploadHeight}, bytes=${primaryRetryUpload.uploadBytes.size}"
                        )
                        val primaryRetryStartedAt = System.currentTimeMillis()
                        val primaryRetryResult = searchRealtimeFaceOnCloudWithBudget(
                            "data:image/jpeg;base64,${Base64.encodeToString(primaryRetryUpload.uploadBytes, Base64.NO_WRAP)}",
                            1,
                            "实时视频主裁剪重试 track=${plan.trackId} frame=${candidate.decodedFrames} mode=${if (plan.crowdMode) "crowd" else "normal"}",
                            kind = "primary_retry",
                            trackId = plan.trackId,
                            rescue = false
                        )
                        if (primaryRetryResult != null) {
                            result = primaryRetryResult
                            recordDiagnostic(
                                "实时云端识别主裁剪重试返回: track=${plan.trackId}, frame=${candidate.decodedFrames}, " +
                                    "experts=${result.experts.size}, costMs=${System.currentTimeMillis() - primaryRetryStartedAt}, " +
                                    "message=${result.message.take(80)}"
                            )
                            finalUpload = primaryRetryUpload
                        } else {
                            recordDiagnostic(
                                "实时云端识别主裁剪重试跳过: track=${plan.trackId}, frame=${candidate.decodedFrames}, reason=请求预算不足"
                            )
                        }
                    } else {
                        recordDiagnostic(
                            "实时云端识别主裁剪重试跳过: track=${plan.trackId}, frame=${candidate.decodedFrames}, reason=主裁剪上传图生成失败"
                        )
                    }
                }
                val finalCloudCostMs = System.currentTimeMillis() - cloudStartedAt
                val summaryResult = when {
                    result.experts.isNotEmpty() -> "success(${result.experts.size})"
                    isNoFaceCloudResult(result) -> "noFace"
                    else -> "noMatch"
                }
                updateRealtimeCloudSummary(
                    trackId = plan.trackId,
                    frame = candidate.decodedFrames,
                    result = summaryResult,
                    costMs = finalCloudCostMs,
                    message = result.message
                )
                if (!isRealtimeCloudPlanStillCurrent(plan)) {
                    recordDiagnostic(
                        "实时云端识别结果丢弃: session=${plan.sessionId}, currentSession=${currentRealtimeRecognitionSessionId()}, " +
                            "track=${plan.trackId}, frame=${candidate.decodedFrames}, experts=${result.experts.size}, " +
                            "reason=会话已过期"
                    )
                    return@executeRealtimeCloudWorker
                }
                handleRealtimeCloudResult(plan.trackId, candidate, finalUpload, result)
            } finally {
                initialBudgetPermit?.let {
                    releaseRealtimeCloudHttpBudget(it)
                    initialBudgetPermit = null
                }
                synchronized(realtimeTrackLock) {
                    activeRealtimeCloudRequestCount = (activeRealtimeCloudRequestCount - 1).coerceAtLeast(0)
                    realtimePersonTracks.firstOrNull { it.id == plan.trackId }?.let { track ->
                        track.cloudRequestInFlight = false
                        if (!isRealtimeRecognitionPageActive && track.bestCandidate == null) {
                            realtimePersonTracks.remove(track)
                            recordDiagnostic(
                                "实时云端识别完成后清理非活跃页面轨迹: session=${plan.sessionId}, track=${plan.trackId}"
                            )
                        }
                    }
                }
                maybeStartRealtimeCloudRecognition()
                maybeStartRealtimeFrameRescue()
            }
        }
    }

    private fun selectRealtimeLookbackCandidate(
        trackId: Long,
        original: RealtimeFaceCandidate,
        crowdMode: Boolean
    ): RealtimeFaceCandidate {
        val historySelection = selectRealtimeHistoryCandidate(trackId, original)
        val best = historySelection.candidate ?: original
        val selected = historySelection.candidate != null
        recordDiagnostic(
            "实时回看候选: track=$trackId, mlRecheck=false, selected=$selected, " +
                "source=${if (selected) "history" else "current"}, crowd=$crowdMode, " +
                "historySize=${historySelection.historySize}, reason=${historySelection.reason}, " +
                "oldFrame=${original.decodedFrames}, bestFrame=${best.decodedFrames}, " +
                "oldQ=${original.qualityScore}, bestQ=${best.qualityScore}, " +
                "oldP=${original.dispatchScore}, bestP=${best.dispatchScore}, " +
                "qualityGain=${historySelection.qualityGain}, suitabilityGain=${historySelection.suitabilityGain}"
        )
        return best
    }

    private fun selectRealtimeHistoryCandidate(
        trackId: Long,
        original: RealtimeFaceCandidate
    ): RealtimeHistorySelection {
        val now = System.currentTimeMillis()
        val history = synchronized(realtimeTrackLock) {
            val track = realtimePersonTracks.firstOrNull { it.id == trackId }
            if (track == null) {
                emptyList()
            } else {
                trimRealtimeCandidateHistoryLocked(track, now)
                track.candidateHistory
                    .filter { abs(it.createdAt - original.createdAt) <= REALTIME_TRACK_CANDIDATE_HISTORY_MS }
                    .filter { isRealtimeHistoryCandidateSamePerson(original, it) }
                .toList()
            }
        }
        if (history.isEmpty()) {
            return RealtimeHistorySelection(
                candidate = null,
                historySize = 0,
                qualityGain = 0,
                suitabilityGain = 0,
                reason = "history_empty"
            )
        }
        val best = history.maxWithOrNull(
            compareBy<RealtimeFaceCandidate> { realtimeCandidateCloudSuitabilityScore(it) }
                .thenBy { it.qualityScore }
                .thenBy { it.faceAreaRatio }
        ) ?: return RealtimeHistorySelection(
            candidate = null,
            historySize = history.size,
            qualityGain = 0,
            suitabilityGain = 0,
            reason = "history_no_best"
        )
        if (best.decodedFrames == original.decodedFrames && best.createdAt == original.createdAt) {
            return RealtimeHistorySelection(
                candidate = null,
                historySize = history.size,
                qualityGain = 0,
                suitabilityGain = 0,
                reason = "same_frame"
            )
        }
        val qualityGain = best.qualityScore - original.qualityScore
        val suitabilityGain = realtimeCandidateCloudSuitabilityScore(best) -
            realtimeCandidateCloudSuitabilityScore(original)
        val selected = qualityGain >= REALTIME_LOOKBACK_MIN_QUALITY_GAIN ||
            best.qualityScore.toFloat() / original.qualityScore.toFloat().coerceAtLeast(1f) >=
            REALTIME_LOOKBACK_MIN_QUALITY_RATIO ||
            suitabilityGain >= REALTIME_LOOKBACK_MIN_SUITABILITY_GAIN
        if (selected) {
            return RealtimeHistorySelection(
                candidate = best,
                historySize = history.size,
                qualityGain = qualityGain,
                suitabilityGain = suitabilityGain,
                reason = "history_better"
            )
        }
        return RealtimeHistorySelection(
            candidate = null,
            historySize = history.size,
            qualityGain = qualityGain,
            suitabilityGain = suitabilityGain,
            reason = "history_not_better"
        )
    }

    private fun isRealtimeHistoryCandidateSamePerson(
        reference: RealtimeFaceCandidate,
        candidate: RealtimeFaceCandidate
    ): Boolean {
        val dx = reference.faceCenterX - candidate.faceCenterX
        val dy = reference.faceCenterY - candidate.faceCenterY
        val centerDistance = kotlin.math.sqrt(dx * dx + dy * dy)
        return centerDistance <= REALTIME_LOOKBACK_MAX_CENTER_DISTANCE * 1.25f &&
            realtimeSizeRatio(reference.faceAreaRatio, candidate.faceAreaRatio) <=
            REALTIME_LOOKBACK_MAX_SIZE_RATIO
    }

    private fun realtimeLookbackFramesForCandidate(candidate: RealtimeFaceCandidate): List<RealtimeLookbackFrame> {
        val now = System.currentTimeMillis()
        return synchronized(realtimeLookbackLock) {
            trimRealtimeLookbackFramesLocked(now)
            realtimeLookbackFrames
                .asSequence()
                .filter { it.decodedFrames != candidate.decodedFrames }
                .filter { abs(it.receivedAt - candidate.createdAt) <= REALTIME_LOOKBACK_WINDOW_MS }
                .toList()
                .takeLast(REALTIME_LOOKBACK_MAX_FRAMES)
        }
    }

    private fun realtimeLookbackFrameCount(): Int {
        val now = System.currentTimeMillis()
        return synchronized(realtimeLookbackLock) {
            trimRealtimeLookbackFramesLocked(now)
            realtimeLookbackFrames.size
        }
    }

    private fun isRealtimeLookbackSamePerson(
        reference: RealtimeFaceCandidate,
        evaluation: RealtimeFaceEvaluation
    ): Boolean {
        val dx = reference.faceCenterX - evaluation.faceCenterX
        val dy = reference.faceCenterY - evaluation.faceCenterY
        val centerDistance = kotlin.math.sqrt(dx * dx + dy * dy)
        return centerDistance <= REALTIME_LOOKBACK_MAX_CENTER_DISTANCE &&
            realtimeSizeRatio(reference.faceAreaRatio, evaluation.faceAreaRatio) <=
            REALTIME_LOOKBACK_MAX_SIZE_RATIO
    }

    private fun prepareRealtimeUploadPayload(candidate: RealtimeFaceCandidate, wideRetry: Boolean): RealtimeUploadPayload? {
        val frameBitmap = BitmapFactory.decodeByteArray(candidate.frameBytes, 0, candidate.frameBytes.size)
        if (frameBitmap == null) {
            recordDiagnostic("实时上传图准备失败: 原始帧解码失败 frame=${candidate.decodedFrames}, bytes=${candidate.frameBytes.size}")
            return null
        }
        return try {
            val faceRect = clippedRect(Rect(candidate.faceRectInFrame), frameBitmap.width, frameBitmap.height)
            if (faceRect == null) {
                recordDiagnostic(
                    "实时上传图准备失败: 人脸框越界 frame=${candidate.decodedFrames}, " +
                        "rect=${candidate.faceRectInFrame}"
                )
                return null
            }
            val uploadImage = buildRealtimeFaceUploadImageFromRect(
                sourceBitmap = frameBitmap,
                faceRect = faceRect,
                maxUploadSide = VIDEO_MAX_UPLOAD_IMAGE_SIDE,
                wideRetry = wideRetry
            )
            try {
                val uploadBytes = bitmapToJpegBytes(uploadImage.bitmap, FACE_UPLOAD_JPEG_QUALITY)
                val localRect = uploadImage.localFaceRects.firstOrNull() ?: FaceRect(
                    0f,
                    0f,
                    uploadImage.bitmap.width.toFloat(),
                    uploadImage.bitmap.height.toFloat()
                )
                RealtimeUploadPayload(
                    uploadBytes = uploadBytes,
                    uploadWidth = uploadImage.bitmap.width,
                    uploadHeight = uploadImage.bitmap.height,
                    localFaceRect = localRect,
                    sourceCropRect = faceRectFromPixelRect(uploadImage.sourceCropRect),
                    cropMode = if (wideRetry) "wide_retry" else "primary",
                    cropWidth = uploadImage.sourceCropRect.width(),
                    cropHeight = uploadImage.sourceCropRect.height()
                )
            } finally {
                try {
                    uploadImage.bitmap.recycle()
                } catch (_: Exception) {
                }
            }
        } catch (e: Exception) {
            recordDiagnostic("实时上传图准备异常: frame=${candidate.decodedFrames}", e)
            null
        } finally {
            try {
                frameBitmap.recycle()
            } catch (_: Exception) {
            }
        }
    }

    private fun realtimeCloudCooldownMs(track: RealtimePersonTrack): Long {
        if (track.lastCloudUploadAt <= 0L) {
            return 0L
        }
        return if (track.lastCloudUploadMatched) {
            REALTIME_CLOUD_PERSON_COOLDOWN_MS
        } else if (track.lastCloudUploadNoFace) {
            0L
        } else {
            REALTIME_CLOUD_NO_MATCH_RETRY_COOLDOWN_MS
        }
    }

    private fun realtimeCloudCooldownLeftMs(track: RealtimePersonTrack, now: Long): Long {
        val cooldownMs = realtimeCloudCooldownMs(track)
        if (cooldownMs <= 0L || track.lastCloudUploadAt <= 0L) {
            return 0L
        }
        return (track.lastCloudUploadAt + cooldownMs - now).coerceAtLeast(0L)
    }

    private fun isRealtimeLostFaceCooldownBypassAllowed(
        track: RealtimePersonTrack,
        candidate: RealtimeFaceCandidate,
        now: Long
    ): Boolean {
        if (now - track.lastSeenAt < REALTIME_LOST_FACE_FLUSH_MS) {
            return false
        }
        if (track.lastCloudUploadAt <= 0L || realtimeCloudCooldownLeftMs(track, now) <= 0L) {
            return false
        }
        if (track.lastCloudUploadMatched || track.lastCloudUploadNoFace) {
            return false
        }
        val minSide = minOf(candidate.faceRectInFrame.width(), candidate.faceRectInFrame.height())
        if (minSide < REALTIME_LOST_FACE_COOLDOWN_BYPASS_MIN_SIDE_PX) {
            return false
        }
        return candidate.cloudGateQuality >= REALTIME_LOST_FACE_COOLDOWN_BYPASS_MIN_GATE_QUALITY ||
            candidate.dispatchScore >= REALTIME_LOST_FACE_COOLDOWN_BYPASS_MIN_DISPATCH_SCORE ||
            candidate.qualityScore >= REALTIME_LOST_FACE_COOLDOWN_BYPASS_MIN_QUALITY
    }

    private fun isRealtimeQualityOrSizeJumpCandidate(
        track: RealtimePersonTrack,
        candidate: RealtimeFaceCandidate,
        now: Long
    ): Boolean {
        val previousQuality = track.lastCloudUploadQuality
        if (track.lastCloudUploadAt <= 0L || previousQuality <= 0) {
            return false
        }
        val absoluteGain = candidate.qualityScore - previousQuality
        val relativeGain = candidate.qualityScore.toFloat() / previousQuality.toFloat().coerceAtLeast(1f)
        val qualitySignificant = absoluteGain >= REALTIME_QUALITY_JUMP_MIN_GAIN ||
            relativeGain >= REALTIME_QUALITY_JUMP_MIN_RATIO
        val previousArea = track.lastCloudUploadAreaRatio.coerceAtLeast(0.000001f)
        val areaGainRatio = candidate.faceAreaRatio / previousArea
        val sideGain = maxOf(
            candidate.faceRectInFrame.width() - track.lastCloudUploadFaceWidth,
            candidate.faceRectInFrame.height() - track.lastCloudUploadFaceHeight
        )
        val sizeSignificant = track.lastCloudUploadAreaRatio > 0f &&
            (areaGainRatio >= REALTIME_SIZE_JUMP_MIN_AREA_RATIO ||
                sideGain >= REALTIME_SIZE_JUMP_MIN_SIDE_GAIN_PX)
        return qualitySignificant ||
            sizeSignificant ||
            isRealtimeLostHighQualityCooldownBreak(track, candidate, now)
    }

    private fun isRealtimeLostHighQualityCooldownBreak(
        track: RealtimePersonTrack,
        candidate: RealtimeFaceCandidate,
        now: Long
    ): Boolean {
        if (track.lastCloudUploadMatched) {
            return false
        }
        if (now - track.lastSeenAt < REALTIME_LOST_FACE_FLUSH_MS) {
            return false
        }
        val minSide = minOf(candidate.faceRectInFrame.width(), candidate.faceRectInFrame.height())
        return candidate.qualityScore >= REALTIME_LOST_FACE_COOLDOWN_BREAK_QUALITY &&
            candidate.cloudGateQuality >= REALTIME_LOST_FACE_COOLDOWN_BREAK_GATE_QUALITY &&
            minSide >= REALTIME_MIN_CLOUD_FACE_SIDE_PX &&
            candidate.faceAreaRatio >= REALTIME_LOST_FACE_COOLDOWN_BREAK_MIN_AREA
    }

    private fun isRealtimeQualityJumpCandidate(
        track: RealtimePersonTrack,
        candidate: RealtimeFaceCandidate,
        now: Long
    ): Boolean {
        if (track.lastCloudUploadAt <= 0L) {
            return false
        }
        val previousQuality = track.lastCloudUploadQuality
        if (previousQuality <= 0) {
            return false
        }
        val absoluteGain = candidate.qualityScore - previousQuality
        val relativeGain = candidate.qualityScore.toFloat() / previousQuality.toFloat().coerceAtLeast(1f)
        val qualitySignificant = absoluteGain >= REALTIME_QUALITY_JUMP_MIN_GAIN ||
            relativeGain >= REALTIME_QUALITY_JUMP_MIN_RATIO
        val previousArea = track.lastCloudUploadAreaRatio.coerceAtLeast(0.000001f)
        val areaGainRatio = candidate.faceAreaRatio / previousArea
        val sideGain = maxOf(
            candidate.faceRectInFrame.width() - track.lastCloudUploadFaceWidth,
            candidate.faceRectInFrame.height() - track.lastCloudUploadFaceHeight
        )
        val sizeSignificant = track.lastCloudUploadAreaRatio > 0f &&
            (areaGainRatio >= REALTIME_SIZE_JUMP_MIN_AREA_RATIO ||
                sideGain >= REALTIME_SIZE_JUMP_MIN_SIDE_GAIN_PX)
        val lostHighQuality = isRealtimeLostHighQualityCooldownBreak(track, candidate, now)
        val significant = isRealtimeQualityOrSizeJumpCandidate(track, candidate, now)
        if (significant) {
            val reason = when {
                qualitySignificant && sizeSignificant -> "质量和尺寸提升"
                qualitySignificant -> "质量提升"
                lostHighQuality -> "离场高质量候选"
                else -> "尺寸提升"
            }
            recordDiagnostic(
                "实时同人${reason}，允许冷却期内二次识别: track=${track.id}, " +
                    "prevQ=$previousQuality, newQ=${candidate.qualityScore}, " +
                    "gain=$absoluteGain, ratio=${String.format(Locale.CHINA, "%.2f", relativeGain)}, " +
                    "prevArea=${String.format(Locale.CHINA, "%.4f", track.lastCloudUploadAreaRatio)}, " +
                    "newArea=${String.format(Locale.CHINA, "%.4f", candidate.faceAreaRatio)}, " +
                    "areaRatio=${String.format(Locale.CHINA, "%.2f", areaGainRatio)}, " +
                    "prevRect=${track.lastCloudUploadFaceWidth}x${track.lastCloudUploadFaceHeight}, " +
                    "newRect=${candidate.faceRectInFrame.width()}x${candidate.faceRectInFrame.height()}, " +
                    "sideGain=$sideGain, sinceLastMs=${now - track.lastCloudUploadAt}, " +
                    "lostMs=${now - track.lastSeenAt}"
            )
        }
        return significant
    }

    private fun isNoFaceCloudResult(result: CloudFaceSearchResult): Boolean {
        val message = result.message
        return message.contains("NoFace", ignoreCase = true) ||
            message.contains("没有人脸") ||
            message.contains("未检测到人脸")
    }

    private fun handleRealtimeCloudResult(
        trackId: Long,
        candidate: RealtimeFaceCandidate,
        upload: RealtimeUploadPayload,
        result: CloudFaceSearchResult
    ) {
        if (result.experts.isEmpty()) {
            val noFace = isNoFaceCloudResult(result)
            synchronized(realtimeTrackLock) {
                realtimePersonTracks.firstOrNull { it.id == trackId }?.let { track ->
                    track.lastCloudUploadMatched = false
                    track.lastCloudUploadNoFace = noFace
                    if (!noFace) {
                        track.consecutiveNoMatchCount += 1
                        track.consecutiveNoFaceCount = 0
                        track.noFaceSuppressedUntil = 0L
                    }
                }
            }
            recordRealtimeNoFaceResult(
                trackId = trackId,
                candidate = candidate,
                noFace = noFace,
                message = result.message
            )
            recordDiagnostic(
                    "实时云端识别未匹配: track=$trackId, frame=${candidate.decodedFrames}, " +
                    "q=${candidate.qualityScore}, gateQ=${candidate.cloudGateQuality}, " +
                    "p=${candidate.dispatchScore}, cropMode=${upload.cropMode}, " +
                    "crop=${upload.cropWidth}x${upload.cropHeight}, upload=${upload.uploadWidth}x${upload.uploadHeight}, " +
                    "message=${result.message}"
            )
            updateRealtimeAttemptStatus(
                if (noFace) {
                    "云端未检测到人脸，等待更好角度"
                } else {
                    "云端未匹配专家，等待更好画面"
                }
            )
            return
        }
        val expertsWithRects = result.experts.mapIndexed { index, expert ->
            if (expert.faceRect != null) {
                expert
            } else {
                if (index == 0) {
                    recordDiagnostic(
                        "实时云端未返回人脸框，使用本地上传图人脸框: track=$trackId, " +
                            "rect=${upload.localFaceRect.x},${upload.localFaceRect.y}," +
                            "${upload.localFaceRect.width},${upload.localFaceRect.height}"
                    )
                }
                expert.copy(faceRect = upload.localFaceRect)
            }
        }
        val names = expertsWithRects.joinToString("，") { it.name }
        latestRealtimeAttemptText = ""
        latestRealtimeAttemptAt = 0L
        recordDiagnostic(
            "实时云端识别成功: track=$trackId, experts=${expertsWithRects.size}, names=$names, " +
                "frame=${candidate.decodedFrames}, q=${candidate.qualityScore}, gateQ=${candidate.cloudGateQuality}, " +
                "p=${candidate.dispatchScore}, cropMode=${upload.cropMode}, " +
                "crop=${upload.cropWidth}x${upload.cropHeight}, upload=${upload.uploadWidth}x${upload.uploadHeight}"
        )
        saveRealtimeExpertRecords(trackId, candidate, upload, expertsWithRects)
        synchronized(realtimeTrackLock) {
            realtimePersonTracks.firstOrNull { it.id == trackId }?.let { track ->
                track.lastMatchedNames = names
                track.lastCloudUploadMatched = true
                track.lastCloudUploadNoFace = false
                track.consecutiveNoFaceCount = 0
                track.consecutiveNoMatchCount = 0
                track.noFaceSuppressedUntil = 0L
                track.lastNoFaceSuppressLogAt = 0L
                track.lastNoFaceAt = 0L
                track.lastNoFaceQuality = 0
                track.lastNoFaceAreaRatio = 0f
                track.lastNoFaceFaceWidth = 0
                track.lastNoFaceFaceHeight = 0
            }
        }
        runOnUiThread {
            if (!::binding.isInitialized) {
                return@runOnUiThread
            }
            if (!isRealtimeRecognitionPageActive) {
                recordDiagnostic("实时云端识别结果已忽略: track=$trackId, reason=page_inactive, names=$names")
                return@runOnUiThread
            }
            capturedFrameBytes = upload.uploadBytes
            lastLocalFaceCrop = BitmapFactory.decodeByteArray(upload.uploadBytes, 0, upload.uploadBytes.size)
            realtimeExpertsByTrack.remove(trackId)
            realtimeExpertsByTrack[trackId] = expertsWithRects
            while (realtimeExpertsByTrack.size > REALTIME_MAX_RESULT_TRACKS) {
                val firstKey = realtimeExpertsByTrack.keys.firstOrNull() ?: break
                realtimeExpertsByTrack.remove(firstKey)
            }
            matchedExpertsList.clear()
            matchedExpertsList.addAll(realtimeExpertsByTrack.values.flatten())
            currentDisplayIndex = (matchedExpertsList.size - expertsWithRects.size).coerceAtLeast(0)
            latestRealtimeResultNames = names
            latestRealtimeResultAt = System.currentTimeMillis()
            binding.tvMainRealtimeStatus.text = mainRealtimeStatusText(latestRtmpReceiverSnapshot)
            showExpertInfoAt(currentDisplayIndex)
        }
    }

    private fun recordRealtimeNoFaceResult(
        trackId: Long,
        candidate: RealtimeFaceCandidate,
        noFace: Boolean,
        message: String
    ) {
        if (!noFace) {
            return
        }
        val now = System.currentTimeMillis()
        synchronized(realtimeTrackLock) {
            val track = realtimePersonTracks.firstOrNull { it.id == trackId } ?: return
            track.consecutiveNoFaceCount += 1
            track.lastNoFaceAt = now
            track.lastNoFaceQuality = candidate.qualityScore
            track.lastNoFaceAreaRatio = candidate.faceAreaRatio
            track.lastNoFaceFaceWidth = candidate.faceRectInFrame.width()
            track.lastNoFaceFaceHeight = candidate.faceRectInFrame.height()
            track.lastNoFaceSuppressLogAt = now
            val suppressMs = (REALTIME_NO_FACE_SUPPRESS_BASE_MS * track.consecutiveNoFaceCount)
                .coerceAtMost(REALTIME_NO_FACE_SUPPRESS_MAX_MS)
            track.noFaceSuppressedUntil = now + suppressMs
            recordDiagnostic(
                    "实时 NoFace 反馈记录: track=$trackId, count=${track.consecutiveNoFaceCount}, " +
                    "suppressMs=$suppressMs, frame=${candidate.decodedFrames}, " +
                    "q=${candidate.qualityScore}, gateQ=${candidate.cloudGateQuality}, p=${candidate.dispatchScore}, " +
                    "area=${String.format(Locale.CHINA, "%.4f", candidate.faceAreaRatio)}, " +
                    "rect=${candidate.faceRectInFrame.width()}x${candidate.faceRectInFrame.height()}, " +
                    "message=${message.take(80)}"
            )
        }
    }

    private fun saveRealtimeExpertRecords(
        trackId: Long,
        candidate: RealtimeFaceCandidate,
        upload: RealtimeUploadPayload,
        experts: List<ExpertInfo>
    ): Int {
        val now = System.currentTimeMillis()
        var added = 0
        experts.forEachIndexed { index, expert ->
            val expertWithRect = if (expert.faceRect != null) {
                expert
            } else {
                recordDiagnostic(
                    "实时云端未返回人脸框，保存记录时使用本地上传图人脸框: track=$trackId, " +
                        "name=${expert.name}, rect=${upload.localFaceRect.x},${upload.localFaceRect.y}," +
                        "${upload.localFaceRect.width},${upload.localFaceRect.height}"
                )
                expert.copy(faceRect = upload.localFaceRect)
            }
            val dedupeKey = realtimeExpertDedupeKey(expertWithRect)
            if (!markRealtimeExpertRecordSaveAllowed(dedupeKey, now)) {
                recordDiagnostic(
                    "实时识别记录保存跳过: track=$trackId, name=${expertWithRect.name}, " +
                        "reason=同一专家${REALTIME_RECORD_DUPLICATE_WINDOW_MS / 1000}s内已保存"
                )
                updateRealtimeAttemptStatus(
                    "已识别 ${expertWithRect.name}，${REALTIME_RECORD_DUPLICATE_WINDOW_MS / 1000}s内不重复保存"
                )
                return@forEachIndexed
            }
            try {
                val recordId = "${now}_${Random().nextInt(100000)}"
                val record = RecognitionRecord(
                    id = recordId,
                    createdAt = now - index * 10L,
                    updatedAt = now,
                    status = STATUS_SUCCESS,
                    statusText = "实时识别成功"
                )
                record.originalImagePath = saveHistoryImage(recordId, "original", candidate.frameBytes)
                record.uploadImagePath = saveHistoryImage(recordId, "upload", upload.uploadBytes)
                record.originalWidth = candidate.frameWidth
                record.originalHeight = candidate.frameHeight
                record.uploadWidth = upload.uploadWidth
                record.uploadHeight = upload.uploadHeight
                record.faceRectImageWidth = upload.uploadWidth
                record.faceRectImageHeight = upload.uploadHeight
                record.uploadSourceRect = upload.sourceCropRect
                record.localFaceRects.add(upload.localFaceRect)
                record.experts.add(expertWithRect)

                val cropRect = expertWithRect.faceRect
                if (cropRect != null) {
                    val crop = cropAndSaveBestFaceImage(
                        upload.uploadBytes,
                        candidate.frameBytes,
                        cropRect,
                        recordId
                    )
                    if (crop != null) {
                        record.uploadImagePath = crop.path
                        record.uploadWidth = crop.width
                        record.uploadHeight = crop.height
                    }
                }

                synchronized(recognitionRecords) {
                    recognitionRecords.add(0, record)
                }
                publishRecognitionRecordIfNeeded(record, "实时识别")
                added += 1
                recordDiagnostic(
                    "实时识别结果已保存: track=$trackId, recordId=$recordId, " +
                        "name=${expertWithRect.name}, score=${expertWithRect.score}, frame=${candidate.decodedFrames}"
                )
            } catch (e: Exception) {
                synchronized(realtimeRecordLock) {
                    realtimeSavedExpertAt.remove(dedupeKey)
                }
                recordDiagnostic(
                    "实时识别记录保存异常: track=$trackId, name=${expertWithRect.name}",
                    e
                )
            }
        }
        if (added > 0) {
            saveRecognitionRecords()
            runOnUiThread {
                renderHistoryListIfVisible()
            }
        }
        return added
    }

    private fun markRealtimeExpertRecordSaveAllowed(dedupeKey: String, now: Long): Boolean {
        pruneRealtimeRecordDedupe(now)
        val recentHistoryAt = synchronized(recognitionRecords) {
            recognitionRecords
                .asSequence()
                .filter { record ->
                    record.status == STATUS_SUCCESS &&
                        now - record.createdAt in 0 until REALTIME_RECORD_DUPLICATE_WINDOW_MS
                }
                .filter { record ->
                    record.experts.any { realtimeExpertDedupeKey(it) == dedupeKey }
                }
                .maxOfOrNull { it.createdAt } ?: 0L
        }
        synchronized(realtimeRecordLock) {
            val recentRuntimeAt = realtimeSavedExpertAt[dedupeKey] ?: 0L
            val recentAt = maxOf(recentRuntimeAt, recentHistoryAt)
            if (recentAt > 0L && now - recentAt < REALTIME_RECORD_DUPLICATE_WINDOW_MS) {
                realtimeSavedExpertAt[dedupeKey] = recentAt
                return false
            }
            realtimeSavedExpertAt[dedupeKey] = now
            return true
        }
    }

    private fun pruneRealtimeRecordDedupe(now: Long) {
        synchronized(realtimeRecordLock) {
            val iterator = realtimeSavedExpertAt.iterator()
            while (iterator.hasNext()) {
                val entry = iterator.next()
                if (now - entry.value > REALTIME_RECORD_DEDUPE_CACHE_MS) {
                    iterator.remove()
                }
            }
        }
    }

    private fun realtimeExpertDedupeKey(expert: ExpertInfo): String {
        val idCard = expert.idCard.orEmpty().trim()
        if (idCard.isNotBlank() && idCard != "-") {
            return "id:$idCard"
        }
        val phone = expert.phone.trim()
        if (phone.isNotBlank() && phone != "-") {
            return "phone:$phone"
        }
        val photoPath = expert.photoPath.trim()
        if (photoPath.isNotBlank()) {
            return "photo:$photoPath"
        }
        return "name:${expert.name.trim()}|company:${expert.company.trim()}"
    }

    private fun enqueueRtmpPreviewFrame(jpegBytes: ByteArray, width: Int, height: Int, decodedFrames: Long) {
        if (isFinishing || isDestroyed || jpegBytes.isEmpty()) {
            return
        }
        val shouldPost = synchronized(rtmpPreviewFrameDispatchLock) {
            pendingRtmpPreviewFrame = RtmpPreviewFramePacket(
                jpegBytes = jpegBytes,
                width = width,
                height = height,
                decodedFrames = decodedFrames
            )
            if (isRtmpPreviewFrameDispatchPosted) {
                false
            } else {
                isRtmpPreviewFrameDispatchPosted = true
                true
            }
        }
        if (shouldPost) {
            mainHandler.post {
                drainLatestRtmpPreviewFrame()
            }
        }
    }

    private fun drainLatestRtmpPreviewFrame() {
        if (isFinishing || isDestroyed) {
            synchronized(rtmpPreviewFrameDispatchLock) {
                pendingRtmpPreviewFrame = null
                isRtmpPreviewFrameDispatchPosted = false
            }
            return
        }
        val frame = synchronized(rtmpPreviewFrameDispatchLock) {
            val latest = pendingRtmpPreviewFrame
            pendingRtmpPreviewFrame = null
            if (latest == null) {
                isRtmpPreviewFrameDispatchPosted = false
            }
            latest
        } ?: return
        handleRtmpPreviewFrame(frame.jpegBytes, frame.decodedFrames, frame.width, frame.height)
        val shouldPostNext = synchronized(rtmpPreviewFrameDispatchLock) {
            if (pendingRtmpPreviewFrame != null) {
                true
            } else {
                isRtmpPreviewFrameDispatchPosted = false
                false
            }
        }
        if (shouldPostNext) {
            mainHandler.post {
                drainLatestRtmpPreviewFrame()
            }
        }
    }

    private fun handleRtmpPreviewFrame(intent: Intent) {
        val jpegBytes = intent.getByteArrayExtra(RtmpReceiverService.EXTRA_PREVIEW_JPEG) ?: return
        val decodedFrames = intent.getLongExtra(RtmpReceiverService.EXTRA_DECODED_FRAMES, 0L)
        val width = intent.getIntExtra(RtmpReceiverService.EXTRA_PREVIEW_WIDTH, 0)
        val height = intent.getIntExtra(RtmpReceiverService.EXTRA_PREVIEW_HEIGHT, 0)
        handleRtmpPreviewFrame(jpegBytes, decodedFrames, width, height)
    }

    private fun handleRtmpPreviewFrame(jpegBytes: ByteArray, decodedFrames: Long, width: Int = 0, height: Int = 0) {
        latestRtmpPreviewFrameIndex = decodedFrames
        val now = System.currentTimeMillis()
        lastRtmpPreviewFrameReceivedAt = now
        latestRtmpPreviewFrameBytes = jpegBytes.size
        latestRtmpPreviewFrameWidth = width
        latestRtmpPreviewFrameHeight = height
        checkRealtimePreviewHealth("preview_frame")
        rememberRealtimeLookbackFrame(jpegBytes, decodedFrames, now)
        maybeStartRealtimePreviewDetection(jpegBytes, decodedFrames, now)
        renderRealtimePreviewFrame(jpegBytes, decodedFrames)
    }

    private fun rememberRealtimeLookbackFrame(jpegBytes: ByteArray, decodedFrames: Long, now: Long) {
        if (!REALTIME_ENABLE_ML_LOOKBACK_RECHECK) {
            return
        }
        if (!isRealtimeRecognitionPageActive || jpegBytes.isEmpty()) {
            return
        }
        synchronized(realtimeLookbackLock) {
            trimRealtimeLookbackFramesLocked(now)
            if (now - lastRealtimeLookbackFrameAt < REALTIME_LOOKBACK_FRAME_INTERVAL_MS) {
                return
            }
            realtimeLookbackFrames.addLast(
                RealtimeLookbackFrame(
                    receivedAt = now,
                    decodedFrames = decodedFrames,
                    jpegBytes = jpegBytes.copyOf()
                )
            )
            lastRealtimeLookbackFrameAt = now
            trimRealtimeLookbackFramesLocked(now)
        }
    }

    private fun trimRealtimeLookbackFramesLocked(now: Long) {
        while (realtimeLookbackFrames.size > REALTIME_LOOKBACK_MAX_FRAMES) {
            realtimeLookbackFrames.removeFirst()
        }
        while (true) {
            val first = realtimeLookbackFrames.peekFirst() ?: break
            if (now - first.receivedAt <= REALTIME_LOOKBACK_WINDOW_MS) {
                break
            }
            realtimeLookbackFrames.removeFirst()
        }
    }

    private fun renderRealtimePreviewFrame(jpegBytes: ByteArray, decodedFrames: Long) {
        if (isRtmpPreviewRenderRunning) {
            val now = System.currentTimeMillis()
            val startedAt = rtmpPreviewRenderStartedAt
            if (startedAt > 0L && now - startedAt > REALTIME_PREVIEW_RENDER_STALL_MS) {
                recordDiagnostic(
                    "实时视频预览渲染锁超时，释放并跳过旧帧: " +
                        "runningMs=${now - startedAt}, latestFrame=$decodedFrames, " +
                        "lastRenderedFrame=$lastRtmpPreviewRenderedFrameIndex, " +
                        "lastRenderedAgeMs=${if (lastRtmpPreviewFrameRenderedAt > 0L) now - lastRtmpPreviewFrameRenderedAt else -1}"
                )
                isRtmpPreviewRenderRunning = false
                rtmpPreviewRenderStartedAt = 0L
            } else {
                maybeLogRealtimePreviewHealth(
                    reason = "render_worker_busy",
                    source = "render_skip",
                    now = now,
                    extra = "latestFrame=$decodedFrames, runningMs=${if (startedAt > 0L) now - startedAt else -1}"
                )
                return
            }
        }
        rtmpPreviewRenderStartedAt = System.currentTimeMillis()
        isRtmpPreviewRenderRunning = true
        executeWorker("实时视频画面预览") {
            var decodedBitmap: Bitmap? = null
            try {
                val bitmap = BitmapFactory.decodeByteArray(
                    jpegBytes,
                    0,
                    jpegBytes.size,
                    BitmapFactory.Options().apply { inMutable = true }
                )
                if (bitmap == null) {
                    recordDiagnostic("实时视频预览帧解码失败: bytes=${jpegBytes.size}")
                    return@executeWorker
                }
                decodedBitmap = bitmap
                val overlay = drawRealtimeOverlaySnapshot(bitmap, latestRealtimeOverlaySnapshot)
                publishRealtimePreviewBitmap(
                    overlay = overlay,
                    decodedFrames = decodedFrames,
                    statusText = latestRealtimeOverlaySnapshot
                        ?.takeIf { System.currentTimeMillis() - it.createdAt <= REALTIME_OVERLAY_HOLD_MS }
                        ?.statusText
                )
                if (overlay !== bitmap) {
                    try {
                        bitmap.recycle()
                    } catch (_: Exception) {
                    }
                    decodedBitmap = null
                }
            } catch (e: Exception) {
                recordDiagnostic("实时视频预览渲染异常: frame=$decodedFrames", e)
            } finally {
                if (decodedBitmap != null && !::binding.isInitialized) {
                    try {
                        decodedBitmap.recycle()
                    } catch (_: Exception) {
                    }
                }
                isRtmpPreviewRenderRunning = false
                rtmpPreviewRenderStartedAt = 0L
            }
        }
    }

    private fun maybeStartRealtimePreviewDetection(jpegBytes: ByteArray, decodedFrames: Long, now: Long) {
        if (now - lastRealtimeFaceDetectAt < REALTIME_PREVIEW_DETECT_INTERVAL_MS) {
            return
        }
        if (isRtmpPreviewFaceDetectionRunning) {
            val startedAt = rtmpPreviewFaceDetectionStartedAt
            if (startedAt > 0L && now - startedAt > REALTIME_PREVIEW_PROCESS_STALL_MS) {
                recordDiagnostic(
                    "实时视频预览处理锁超时，释放并跳过旧帧: " +
                        "runningMs=${now - startedAt}, latestFrame=$decodedFrames"
                )
                isRtmpPreviewFaceDetectionRunning = false
                rtmpPreviewFaceDetectionStartedAt = 0L
            } else {
                return
            }
        }
        isRtmpPreviewFaceDetectionRunning = true
        rtmpPreviewFaceDetectionStartedAt = now
        lastRealtimeFaceDetectAt = now
        val detectionToken = rtmpPreviewFaceDetectionToken + 1L
        rtmpPreviewFaceDetectionToken = detectionToken
        executeWorker("实时视频本地检脸") {
            var bitmap: Bitmap? = null
            try {
                val decodeOptions = BitmapFactory.Options().apply {
                    inMutable = true
                }
                bitmap = BitmapFactory.decodeByteArray(jpegBytes, 0, jpegBytes.size, decodeOptions)
                val detectionBitmap = bitmap
                if (detectionBitmap == null) {
                    recordDiagnostic("实时视频预览帧解码失败: bytes=${jpegBytes.size}")
                    return@executeWorker
                }
                val detectStartedAt = System.currentTimeMillis()
                val faces = try {
                    Tasks.await(
                        getRealtimeFaceDetector().process(InputImage.fromBitmap(detectionBitmap, 0)),
                        REALTIME_PREVIEW_FACE_DETECT_TIMEOUT_MS,
                        TimeUnit.MILLISECONDS
                    )
                } catch (e: Exception) {
                    recordDiagnostic("实时视频本地人脸检测异常: frame=$decodedFrames", e)
                    emptyList<Face>()
                }
                val detectCostMs = System.currentTimeMillis() - detectStartedAt
                if (rtmpPreviewFaceDetectionToken != detectionToken) {
                    recordDiagnostic(
                        "实时视频本地检脸结果丢弃: reason=过期检测任务, " +
                            "frame=$decodedFrames, token=$detectionToken, current=$rtmpPreviewFaceDetectionToken, " +
                            "detectMs=$detectCostMs"
                    )
                    return@executeWorker
                }
                val detectionFinishedAt = System.currentTimeMillis()
                val heldCrowdMode = isRealtimeCrowdModeActive(detectionFinishedAt)
                val evaluateStartedAt = System.currentTimeMillis()
                var crowdModeForFrame = heldCrowdMode
                var faceEvaluationSummary = evaluateRealtimeFacesWithSummary(
                    bitmap = detectionBitmap,
                    faces = faces,
                    crowdModeForFrame = crowdModeForFrame
                )
                if (!crowdModeForFrame) {
                    val normalEligibleEnough = faceEvaluationSummary.eligibleCount >= REALTIME_CROWD_MODE_MIN_FACES
                    if (normalEligibleEnough) {
                        crowdModeForFrame = true
                        faceEvaluationSummary = evaluateRealtimeFacesWithSummary(
                            bitmap = detectionBitmap,
                            faces = faces,
                            crowdModeForFrame = true
                        )
                    } else if (faces.size >= REALTIME_CROWD_MODE_MIN_FACES) {
                        val crowdProbeSummary = evaluateRealtimeFacesWithSummary(
                            bitmap = detectionBitmap,
                            faces = faces,
                            crowdModeForFrame = true
                        )
                        if (crowdProbeSummary.eligibleCount >= REALTIME_CROWD_MODE_MIN_FACES) {
                            crowdModeForFrame = true
                            faceEvaluationSummary = crowdProbeSummary
                        }
                    }
                }
                val evaluateCostMs = System.currentTimeMillis() - evaluateStartedAt
                if (rtmpPreviewFaceDetectionToken != detectionToken) {
                    recordDiagnostic(
                        "实时视频本地检脸评估丢弃: reason=过期检测任务, " +
                            "frame=$decodedFrames, token=$detectionToken, current=$rtmpPreviewFaceDetectionToken, " +
                            "detectMs=$detectCostMs, evalMs=$evaluateCostMs"
                    )
                    return@executeWorker
                }
                val faceEvaluations = faceEvaluationSummary.evaluations
                latestRealtimeFaceCount = faceEvaluationSummary.detectedCount
                latestRealtimeValidFaceCount = faceEvaluationSummary.eligibleCount
                latestRealtimeUploadableFaceCount = faceEvaluationSummary.uploadableCount
                if (isRealtimeRecognitionPageActive && latestRtmpReceiverSnapshot.running) {
                    updateRealtimeFaceCandidates(
                        bitmap = detectionBitmap,
                        faces = faces,
                        decodedFrames = decodedFrames,
                        frameBytes = jpegBytes,
                        faceEvaluationSummary = faceEvaluationSummary,
                        crowdModeForFrame = crowdModeForFrame
                    )
                    enqueueRealtimeRescueCandidates(
                        bitmap = detectionBitmap,
                        faces = faces,
                        decodedFrames = decodedFrames,
                        frameBytes = jpegBytes,
                        faceEvaluationSummary = faceEvaluationSummary,
                        crowdModeForFrame = crowdModeForFrame
                    )
                } else {
                    maybeStartRealtimeCloudRecognition()
                }
                val bitmapWidth = detectionBitmap.width
                val bitmapHeight = detectionBitmap.height
                val overlaySnapshot = buildRealtimeOverlaySnapshot(
                    frameWidth = bitmapWidth,
                    frameHeight = bitmapHeight,
                    faces = faces,
                    faceEvaluations = faceEvaluations,
                    crowdModeForFrame = crowdModeForFrame
                )
                lastRealtimeDetectAt = System.currentTimeMillis()
                lastRealtimeDetectFrame = decodedFrames
                lastRealtimeDetectDetectedCount = faceEvaluationSummary.detectedCount
                lastRealtimeDetectValidCount = faceEvaluationSummary.eligibleCount
                lastRealtimeDetectUploadableCount = overlaySnapshot.readyCount
                lastRealtimeDetectWaitingCount = overlaySnapshot.waitingCount
                lastRealtimeDetectLowQualityCount = overlaySnapshot.lowQualityCount
                lastRealtimeDetectCostMs = detectCostMs
                lastRealtimeEvaluateCostMs = evaluateCostMs
                lastRealtimeDetectBitmapWidth = bitmapWidth
                lastRealtimeDetectBitmapHeight = bitmapHeight
                lastRealtimeDetectBytes = jpegBytes.size
                latestRealtimeUploadableFaceCount = overlaySnapshot.readyCount
                latestRealtimeOverlaySnapshot = overlaySnapshot
                val statusText = overlaySnapshot.statusText
                runOnUiThread {
                    if (::binding.isInitialized) {
                        binding.tvMainRealtimePreviewStatus.text = statusText
                        binding.tvMainRealtimeStatus.text = mainRealtimeStatusText(latestRtmpReceiverSnapshot)
                        if (binding.settingsPage.visibility == View.VISIBLE) {
                            binding.tvRealtimeStreamStatus.text = statusText
                        }
                    }
                }
                val nowForLog = System.currentTimeMillis()
                if (nowForLog - lastRealtimeFaceLogAt >= REALTIME_FACE_LOG_INTERVAL_MS ||
                    faces.size != lastRealtimeLoggedFaceCount ||
                    faceEvaluationSummary.eligibleCount != lastRealtimeLoggedValidFaceCount ||
                    overlaySnapshot.readyCount != lastRealtimeLoggedUploadableFaceCount ||
                    decodedFrames % REALTIME_MAIN_PREVIEW_LOG_EVERY_FRAMES == 0L
                ) {
                    lastRealtimeFaceLogAt = nowForLog
                    lastRealtimeLoggedFaceCount = faces.size
                    lastRealtimeLoggedValidFaceCount = faceEvaluationSummary.eligibleCount
                    lastRealtimeLoggedUploadableFaceCount = overlaySnapshot.readyCount
                    val minAreaText = String.format(
                        Locale.CHINA,
                        "%.4f",
                        realtimeMinFaceAreaRatio(crowdModeForFrame)
                    )
                    recordDiagnostic(
                        "实时视频本地检脸: decodedFrames=$decodedFrames, " +
                            "detected=${faceEvaluationSummary.detectedCount}, " +
                            "valid=${faceEvaluationSummary.eligibleCount}, " +
                            "uploadable=${overlaySnapshot.readyCount}, wait=${overlaySnapshot.waitingCount}, " +
                            "localQualified=${faceEvaluationSummary.uploadableCount}, " +
                            "skipInvalid=${faceEvaluationSummary.skippedInvalid}, " +
                            "skipTiny=${faceEvaluationSummary.skippedTooSmall}, " +
                            "skipArea=${faceEvaluationSummary.skippedSmallArea}, " +
                            "skipPose=${faceEvaluationSummary.skippedPose}, " +
                            "skipFalse=${faceEvaluationSummary.skippedLikelyFalsePositive}, " +
                            "skipQuality=${faceEvaluationSummary.skippedQuality}, " +
                            "crowd=$crowdModeForFrame, heldCrowd=$heldCrowdMode, minArea=$minAreaText, " +
                            "detectMs=$detectCostMs, evalMs=$evaluateCostMs, " +
                            "mlLookback=$REALTIME_ENABLE_ML_LOOKBACK_RECHECK, " +
                            "bitmap=${bitmapWidth}x$bitmapHeight, bytes=${jpegBytes.size}"
                    )
                }
            } catch (e: Exception) {
                recordDiagnostic("实时视频预览处理异常: frame=$decodedFrames", e)
            } finally {
                try {
                    bitmap?.recycle()
                } catch (_: Exception) {
                }
                if (rtmpPreviewFaceDetectionToken == detectionToken) {
                    isRtmpPreviewFaceDetectionRunning = false
                    rtmpPreviewFaceDetectionStartedAt = 0L
                }
            }
        }
    }

    private fun publishRealtimePreviewBitmap(overlay: Bitmap, decodedFrames: Long, statusText: String?) {
        runOnUiThread {
            if (!::binding.isInitialized || isFinishing || isDestroyed) {
                try {
                    overlay.recycle()
                } catch (_: Exception) {
                }
                return@runOnUiThread
            }
            currentRtmpPreviewBitmap = overlay
            binding.ivPreview.setImageBitmap(overlay)
            lastRtmpPreviewFrameRenderedAt = System.currentTimeMillis()
            lastRtmpPreviewRenderedFrameIndex = decodedFrames
            statusText?.let {
                binding.tvMainRealtimePreviewStatus.text = it
            }
            binding.tvMainRealtimeStatus.text = mainRealtimeStatusText(latestRtmpReceiverSnapshot)
            if (binding.settingsPage.visibility == View.VISIBLE) {
                binding.ivRealtimeStreamPreview.setImageBitmap(overlay)
                statusText?.let {
                    binding.tvRealtimeStreamStatus.text = it
                }
            }
        }
    }

    private fun localIpv4Addresses(): List<String> {
        return localIpv4AddressCandidates(currentRtmpRemoteIp()).map { it.address }
    }

    private fun localIpv4AddressCandidates(peerIp: String? = null): List<LocalIpv4Candidate> {
        return try {
            Collections.list(NetworkInterface.getNetworkInterfaces())
                .filter { iface ->
                    try {
                        iface.isUp && !iface.isLoopback
                    } catch (_: SocketException) {
                        false
                    }
                }
                .flatMap { iface ->
                    val interfaceName = listOf(iface.name, iface.displayName)
                        .filter { it.isNotBlank() }
                        .distinct()
                        .joinToString("/")
                    Collections.list(iface.inetAddresses)
                        .filterIsInstance<Inet4Address>()
                        .map { address ->
                            LocalIpv4Candidate(
                                address = address.hostAddress.orEmpty(),
                                interfaceName = interfaceName
                            )
                        }
                }
                .filter { candidate ->
                    candidate.address.isNotBlank() &&
                        !candidate.address.startsWith("127.") &&
                        !candidate.address.startsWith("169.254.") &&
                        ipv4Octets(candidate.address) != null
                }
                .distinctBy { it.address }
                .sortedWith(
                    compareByDescending<LocalIpv4Candidate> {
                        scoreRtmpLocalAddressCandidate(it, peerIp)
                    }.thenBy { it.address }
                )
        } catch (e: Exception) {
            recordDiagnostic("读取手机局域网 IP 失败", e)
            emptyList()
        }
    }

    private fun scoreRtmpLocalAddressCandidate(candidate: LocalIpv4Candidate, peerIp: String?): Int {
        val ip = candidate.address
        val interfaceName = candidate.interfaceName.lowercase(Locale.ROOT)
        var score = 0
        if (peerIp != null && isSameIpv4CSubnet(ip, peerIp)) {
            score += 10_000
        }
        if (ip.startsWith("10.")) {
            score += 600
        } else if (ip.startsWith("192.168.")) {
            score += 420
        } else if (isPrivate172Address(ip)) {
            score += 360
        }
        if (interfaceName.contains("wlan") ||
            interfaceName.contains("ap") ||
            interfaceName.contains("p2p") ||
            interfaceName.contains("tether") ||
            interfaceName.contains("hotspot")
        ) {
            score += 160
        }
        if (interfaceName.contains("tun") ||
            interfaceName.contains("tap") ||
            interfaceName.contains("vpn") ||
            interfaceName.contains("ppp") ||
            interfaceName.contains("wg") ||
            interfaceName.contains("tailscale") ||
            interfaceName.contains("zerotier")
        ) {
            score -= 900
        }
        return score
    }

    private fun currentRtmpRemoteIp(): String? {
        return extractIpv4Address(latestRtmpReceiverSnapshot.remoteAddress)
    }

    private fun extractIpv4Address(text: String): String? {
        return Regex("""\d{1,3}(?:\.\d{1,3}){3}""")
            .find(text)
            ?.value
            ?.takeIf { ipv4Octets(it) != null }
    }

    private fun isSameIpv4CSubnet(left: String, right: String): Boolean {
        val leftOctets = ipv4Octets(left) ?: return false
        val rightOctets = ipv4Octets(right) ?: return false
        return leftOctets[0] == rightOctets[0] &&
            leftOctets[1] == rightOctets[1] &&
            leftOctets[2] == rightOctets[2]
    }

    private fun isPrivate172Address(ip: String): Boolean {
        val octets = ipv4Octets(ip) ?: return false
        return octets[0] == 172 && octets[1] in 16..31
    }

    private fun ipv4Octets(ip: String): IntArray? {
        val parts = ip.split(".")
        if (parts.size != 4) {
            return null
        }
        val octets = IntArray(4)
        parts.forEachIndexed { index, part ->
            val value = part.toIntOrNull() ?: return null
            if (value !in 0..255) {
                return null
            }
            octets[index] = value
        }
        return octets
    }

    private fun formatByteCount(bytes: Long): String {
        if (bytes < 1024L) {
            return "${bytes}B"
        }
        val kb = bytes / 1024.0
        if (kb < 1024.0) {
            return String.format(Locale.CHINA, "%.1fKB", kb)
        }
        val mb = kb / 1024.0
        if (mb < 1024.0) {
            return String.format(Locale.CHINA, "%.2fMB", mb)
        }
        return String.format(Locale.CHINA, "%.2fGB", mb / 1024.0)
    }

    private fun startRealtimeStreamTest() {
        if (isRealtimeStreamRunning) {
            Toast.makeText(this, "实时流测试正在运行", Toast.LENGTH_SHORT).show()
            return
        }
        if (isVideoRecognitionRunning || isGalleryBatchRunning || isMatchingRequestRunning || pendingGlassCapture) {
            Toast.makeText(this, "当前有识别任务正在运行，请结束后再测试实时流", Toast.LENGTH_SHORT).show()
            recordDiagnostic(
                "实时流测试启动被拦截: video=$isVideoRecognitionRunning, " +
                    "gallery=$isGalleryBatchRunning, matching=$isMatchingRequestRunning, capture=$pendingGlassCapture"
            )
            return
        }

        val streamUrl = binding.etRealtimeStreamUrl.text.toString().trim()
        val scheme = try {
            Uri.parse(streamUrl).scheme?.lowercase(Locale.ROOT)
        } catch (_: Exception) {
            null
        }
        if (streamUrl.isBlank() || scheme !in setOf("rtmp", "rtsp", "http", "https")) {
            Toast.makeText(this, "请填写 rtmp/rtsp/http/https 视频流地址", Toast.LENGTH_SHORT).show()
            updateRealtimeStreamStatus("请先填写有效的视频流地址")
            return
        }

        val runId = System.currentTimeMillis()
        activeRealtimeStreamRunId = runId
        realtimeStreamStopRequested = false
        isRealtimeStreamRunning = true
        updateRealtimeStreamStatus("正在打开实时流...")
        recordDiagnostic(
            "实时流测试启动: runId=$runId, url=${maskStreamUrlForDiagnostics(streamUrl)}, " +
                "cloud=false, saveRecord=false, detector=local"
        )

        executeWorker("实时流本地检脸测试") {
            runRealtimeStreamDecodeProbe(streamUrl, runId)
        }
    }

    private fun stopRealtimeStreamTest(reason: String) {
        if (!isRealtimeStreamRunning && !realtimeStreamStopRequested) {
            return
        }
        realtimeStreamStopRequested = true
        recordDiagnostic("实时流测试停止请求: runId=$activeRealtimeStreamRunId, reason=$reason")
        updateRealtimeStreamStatus("正在停止实时流测试...")
    }

    private fun finishRealtimeStreamTest(runId: Long, message: String) {
        if (activeRealtimeStreamRunId != runId) {
            return
        }
        isRealtimeStreamRunning = false
        realtimeStreamStopRequested = false
        updateRealtimeStreamStatus(message)
        recordDiagnostic("实时流测试结束: runId=$runId, message=$message")
    }

    private fun updateRealtimeStreamStatus(text: String) {
        Log.d(TAG, "Realtime stream status: $text")
        runOnUiThread {
            if (::binding.isInitialized) {
                binding.tvRealtimeStreamStatus.text = text
            }
        }
    }

    private fun getRealtimeFaceDetector(): FaceDetector {
        realtimeFaceDetector?.let { return it }
        val detector = createRealtimeFaceDetector()
        realtimeFaceDetector = detector
        return detector
    }

    private fun getLookbackFaceDetectorLocked(): FaceDetector {
        lookbackFaceDetector?.let { return it }
        val detector = FaceDetection.getClient(
            FaceDetectorOptions.Builder()
                .setPerformanceMode(FaceDetectorOptions.PERFORMANCE_MODE_ACCURATE)
                .setLandmarkMode(FaceDetectorOptions.LANDMARK_MODE_NONE)
                .setContourMode(FaceDetectorOptions.CONTOUR_MODE_NONE)
                .setClassificationMode(FaceDetectorOptions.CLASSIFICATION_MODE_NONE)
                .setMinFaceSize(0.04f)
                .build()
        )
        lookbackFaceDetector = detector
        return detector
    }

    private fun closeLookbackFaceDetector() {
        synchronized(lookbackFaceDetectorLock) {
            try {
                lookbackFaceDetector?.close()
            } catch (_: Exception) {
            } finally {
                lookbackFaceDetector = null
            }
        }
    }

    private fun createRealtimeFaceDetector(): FaceDetector {
        return FaceDetection.getClient(
            FaceDetectorOptions.Builder()
                .setPerformanceMode(FaceDetectorOptions.PERFORMANCE_MODE_ACCURATE)
                .setLandmarkMode(FaceDetectorOptions.LANDMARK_MODE_NONE)
                .setContourMode(FaceDetectorOptions.CONTOUR_MODE_NONE)
                .setClassificationMode(FaceDetectorOptions.CLASSIFICATION_MODE_NONE)
                .setMinFaceSize(0.04f)
                .enableTracking()
                .build()
        )
    }

    private fun runRealtimeStreamDecodeProbe(streamUrl: String, runId: Long) {
        val extractor = MediaExtractor()
        var codec: MediaCodec? = null
        var decodedFrames = 0
        var inspectedFrames = 0
        var faceHitFrames = 0
        val startedAt = System.currentTimeMillis()

        try {
            updateRealtimeStreamStatus("正在连接流: ${maskStreamUrlForDiagnostics(streamUrl)}")
            extractor.setDataSource(streamUrl, emptyMap<String, String>())

            var videoTrack = -1
            var format: MediaFormat? = null
            for (trackIndex in 0 until extractor.trackCount) {
                val candidate = extractor.getTrackFormat(trackIndex)
                val mime = candidate.getString(MediaFormat.KEY_MIME).orEmpty()
                if (mime.startsWith("video/")) {
                    videoTrack = trackIndex
                    format = candidate
                    break
                }
            }
            if (videoTrack < 0 || format == null) {
                finishRealtimeStreamTest(runId, "实时流未找到视频轨道")
                return
            }

            val mime = format.getString(MediaFormat.KEY_MIME).orEmpty()
            val width = if (format.containsKey(MediaFormat.KEY_WIDTH)) format.getInteger(MediaFormat.KEY_WIDTH) else 0
            val height = if (format.containsKey(MediaFormat.KEY_HEIGHT)) format.getInteger(MediaFormat.KEY_HEIGHT) else 0
            val rotationDegrees = if (format.containsKey(MediaFormat.KEY_ROTATION)) {
                format.getInteger(MediaFormat.KEY_ROTATION)
            } else {
                0
            }
            recordDiagnostic(
                "实时流视频轨道: runId=$runId, mime=$mime, size=${width}x$height, rotation=$rotationDegrees"
            )

            format.setInteger(
                MediaFormat.KEY_COLOR_FORMAT,
                android.media.MediaCodecInfo.CodecCapabilities.COLOR_FormatYUV420Flexible
            )
            extractor.selectTrack(videoTrack)
            codec = MediaCodec.createDecoderByType(mime)
            codec.configure(format, null, null, 0)
            codec.start()

            val bufferInfo = MediaCodec.BufferInfo()
            var inputDone = false
            var outputDone = false
            var idleLoops = 0
            var lastInspectAt = 0L
            val detector = getRealtimeFaceDetector()

            while (!outputDone &&
                !realtimeStreamStopRequested &&
                activeRealtimeStreamRunId == runId &&
                idleLoops < REALTIME_STREAM_MAX_IDLE_LOOPS &&
                inspectedFrames < REALTIME_STREAM_MAX_INSPECTED_FRAMES &&
                System.currentTimeMillis() - startedAt < REALTIME_STREAM_MAX_TEST_DURATION_MS
            ) {
                var madeProgress = false

                if (!inputDone) {
                    val inputIndex = codec.dequeueInputBuffer(REALTIME_STREAM_CODEC_TIMEOUT_US)
                    if (inputIndex >= 0) {
                        val inputBuffer = codec.getInputBuffer(inputIndex)
                        val sampleSize = if (inputBuffer != null) {
                            extractor.readSampleData(inputBuffer, 0)
                        } else {
                            -1
                        }
                        if (sampleSize < 0) {
                            codec.queueInputBuffer(
                                inputIndex,
                                0,
                                0,
                                0L,
                                MediaCodec.BUFFER_FLAG_END_OF_STREAM
                            )
                            inputDone = true
                        } else {
                            codec.queueInputBuffer(
                                inputIndex,
                                0,
                                sampleSize,
                                extractor.sampleTime.coerceAtLeast(0L),
                                0
                            )
                            extractor.advance()
                        }
                        madeProgress = true
                    }
                }

                when (val outputIndex = codec.dequeueOutputBuffer(bufferInfo, REALTIME_STREAM_CODEC_TIMEOUT_US)) {
                    MediaCodec.INFO_TRY_AGAIN_LATER -> Unit
                    MediaCodec.INFO_OUTPUT_FORMAT_CHANGED -> {
                        recordDiagnostic("实时流解码输出格式: ${codec.outputFormat}")
                        madeProgress = true
                    }
                    else -> if (outputIndex >= 0) {
                        madeProgress = true
                        decodedFrames += 1
                        val now = System.currentTimeMillis()
                        val shouldInspect = bufferInfo.size > 0 &&
                            now - lastInspectAt >= REALTIME_STREAM_DETECT_INTERVAL_MS
                        if (shouldInspect) {
                            val image = codec.getOutputImage(outputIndex)
                            if (image != null) {
                                image.use {
                                    var bitmap = yuvImageToScaledBitmap(it, REALTIME_STREAM_PREVIEW_MAX_SIDE)
                                    bitmap = applyVideoRotation(bitmap, rotationDegrees)
                                    val faces = try {
                                        Tasks.await(detector.process(InputImage.fromBitmap(bitmap, 0)))
                                    } catch (e: Exception) {
                                        recordDiagnostic("实时流本地人脸检测异常: runId=$runId", e)
                                        emptyList<Face>()
                                    }
                                    inspectedFrames += 1
                                    lastInspectAt = now
                                    if (faces.isNotEmpty()) {
                                        faceHitFrames += 1
                                    }
                                    val preview = drawRealtimeFaceOverlay(bitmap, faces)
                                    runOnUiThread {
                                        if (activeRealtimeStreamRunId == runId && ::binding.isInitialized) {
                                            binding.ivRealtimeStreamPreview.setImageBitmap(preview)
                                            binding.tvRealtimeStreamStatus.text =
                                                "解码 $decodedFrames 帧，检测 $inspectedFrames 帧，人脸帧 $faceHitFrames，当前 ${faces.size} 张脸"
                                        }
                                    }
                                    if (faces.isNotEmpty() || inspectedFrames % REALTIME_STREAM_LOG_EVERY_INSPECTIONS == 0) {
                                        recordDiagnostic(
                                            "实时流本地检测: runId=$runId, decoded=$decodedFrames, " +
                                                "inspected=$inspectedFrames, currentFaces=${faces.size}, " +
                                                "faceHitFrames=$faceHitFrames, bitmap=${bitmap.width}x${bitmap.height}"
                                        )
                                    }
                                }
                            }
                        }
                        outputDone = bufferInfo.flags and MediaCodec.BUFFER_FLAG_END_OF_STREAM != 0
                        codec.releaseOutputBuffer(outputIndex, false)
                    }
                }

                idleLoops = if (madeProgress) 0 else idleLoops + 1
            }

            val elapsedMs = System.currentTimeMillis() - startedAt
            val reason = when {
                realtimeStreamStopRequested -> "已停止"
                inspectedFrames >= REALTIME_STREAM_MAX_INSPECTED_FRAMES -> "达到测试帧数上限"
                elapsedMs >= REALTIME_STREAM_MAX_TEST_DURATION_MS -> "达到测试时长上限"
                outputDone -> "流已结束"
                idleLoops >= REALTIME_STREAM_MAX_IDLE_LOOPS -> "解码等待超时"
                else -> "测试结束"
            }
            finishRealtimeStreamTest(
                runId,
                "$reason：解码 $decodedFrames 帧，检测 $inspectedFrames 帧，人脸帧 $faceHitFrames"
            )
        } catch (e: Exception) {
            recordDiagnostic(
                "实时流原生解码失败: runId=$runId, url=${maskStreamUrlForDiagnostics(streamUrl)}；" +
                    "若 VLC/服务器可播放但这里失败，下一步需接入专用 RTMP/FFmpeg/ExoPlayer 扩展",
                e
            )
            finishRealtimeStreamTest(runId, "实时流打开失败，已记录诊断日志")
        } finally {
            try {
                codec?.stop()
            } catch (_: Exception) {
            }
            try {
                codec?.release()
            } catch (_: Exception) {
            }
            try {
                extractor.release()
            } catch (_: Exception) {
            }
        }
    }

    private fun buildRealtimeOverlaySnapshot(
        frameWidth: Int,
        frameHeight: Int,
        faces: List<Face>,
        faceEvaluations: Map<Face, RealtimeFaceEvaluation>,
        crowdModeForFrame: Boolean
    ): RealtimeOverlaySnapshot {
        var readyCount = 0
        var waitingCount = 0
        var lowQualityCount = 0
        val now = System.currentTimeMillis()
        val boxes = faces.mapIndexedNotNull { index, face ->
            val evaluation = faceEvaluations[face] ?: return@mapIndexedNotNull null
            val overlayState = realtimeOverlayState(
                face = face,
                evaluation = evaluation,
                crowdModeForFrame = crowdModeForFrame,
                now = now
            )
            when {
                overlayState.readyForCloud -> readyCount += 1
                overlayState.waiting -> waitingCount += 1
                else -> lowQualityCount += 1
            }
            val sideLabel = if (abs(face.headEulerAngleY) >= REALTIME_SIDE_PROFILE_MIN_YAW) "侧脸 " else ""
            val label = "#${index + 1} ${overlayState.label} " +
                "${sideLabel}q=${evaluation.qualityScore}"
            RealtimeOverlayBox(
                rect = Rect(evaluation.faceRect),
                color = overlayState.color,
                label = label
            )
        }
        val detectedCount = faces.size
        val validCount = faceEvaluations.size
        val statusText = if (detectedCount == 0) {
            "本地人脸 0 张"
        } else {
            "有效 $validCount/检出 $detectedCount，蓝 $readyCount/黄 $waitingCount/红 $lowQualityCount；" +
                "蓝框将上云，黄框等待/冷却，红框质量不足" +
                if (crowdModeForFrame) "；多人高峰模式" else ""
        }
        return RealtimeOverlaySnapshot(
            boxes = boxes,
            frameWidth = frameWidth,
            frameHeight = frameHeight,
            createdAt = System.currentTimeMillis(),
            statusText = statusText,
            readyCount = readyCount,
            waitingCount = waitingCount,
            lowQualityCount = lowQualityCount
        )
    }

    private fun realtimeOverlayState(
        face: Face,
        evaluation: RealtimeFaceEvaluation,
        crowdModeForFrame: Boolean,
        now: Long
    ): RealtimeOverlayState {
        if (!evaluation.canUpload) {
            if (evaluation.rejectReason == "脸偏小") {
                return RealtimeOverlayState(
                    color = REALTIME_FACE_BOX_WAITING_COLOR,
                    label = "待靠近",
                    readyForCloud = false,
                    waiting = true
                )
            }
            return RealtimeOverlayState(
                color = REALTIME_FACE_BOX_LOW_QUALITY_COLOR,
                label = evaluation.rejectReason.ifBlank { "暂不适合" },
                readyForCloud = false,
                waiting = false
            )
        }
        if (!isRealtimeCloudRecognitionAllowed()) {
            return RealtimeOverlayState(
                color = REALTIME_FACE_BOX_WAITING_COLOR,
                label = "本地可用",
                readyForCloud = false,
                waiting = true
            )
        }
        val track = synchronized(realtimeTrackLock) {
            findRealtimeTrackForOverlayLocked(face.trackingId, evaluation, now, crowdModeForFrame)
        }
        if (track == null) {
            return RealtimeOverlayState(
                color = REALTIME_FACE_BOX_WAITING_COLOR,
                label = "待跟踪",
                readyForCloud = false,
                waiting = true
            )
        }
        if (track.cloudRequestInFlight) {
            return RealtimeOverlayState(
                color = REALTIME_FACE_BOX_READY_COLOR,
                label = "识别中",
                readyForCloud = true,
                waiting = false
            )
        }
        val candidate = track.bestCandidate
        if (candidate == null) {
            val cooldownLeftMs = realtimeCloudCooldownLeftMs(track, now)
            return RealtimeOverlayState(
                color = REALTIME_FACE_BOX_WAITING_COLOR,
                label = if (cooldownLeftMs > 0L) "冷却${(cooldownLeftMs / 1000L).coerceAtLeast(1L)}s" else "待候选",
                readyForCloud = false,
                waiting = true
            )
        }
        if (track.noFaceSuppressedUntil > now && !isRealtimeNoFaceBreakthrough(track, candidate)) {
            return RealtimeOverlayState(
                color = REALTIME_FACE_BOX_WAITING_COLOR,
                label = "NoFace暂缓",
                readyForCloud = false,
                waiting = true
            )
        }
        val collectWindow = realtimeCloudCollectWindowMs(now)
        val immediateQuality = realtimeImmediateUploadQuality(now)
        val lostFaceFlush = now - track.lastSeenAt >= REALTIME_LOST_FACE_FLUSH_MS
        val oldEnough = now - track.firstSeenAt >= collectWindow ||
            candidate.qualityScore >= immediateQuality ||
            (crowdModeForFrame && now - track.lastSeenAt >= REALTIME_CROWD_LOST_FACE_UPLOAD_MS) ||
            lostFaceFlush
        if (!oldEnough) {
            return RealtimeOverlayState(
                color = REALTIME_FACE_BOX_WAITING_COLOR,
                label = "积累中",
                readyForCloud = false,
                waiting = true
            )
        }
        val cooldownLeftMs = realtimeCloudCooldownLeftMs(track, now)
        val canBreakCooldown = isRealtimeQualityOrSizeJumpCandidate(track, candidate, now)
        return if (cooldownLeftMs <= 0L || canBreakCooldown) {
            RealtimeOverlayState(
                color = REALTIME_FACE_BOX_READY_COLOR,
                label = "可上云",
                readyForCloud = true,
                waiting = false
            )
        } else {
            RealtimeOverlayState(
                color = REALTIME_FACE_BOX_WAITING_COLOR,
                label = "冷却${(cooldownLeftMs / 1000L).coerceAtLeast(1L)}s",
                readyForCloud = false,
                waiting = true
            )
        }
    }

    private fun findRealtimeTrackForOverlayLocked(
        trackingId: Int?,
        evaluation: RealtimeFaceEvaluation,
        now: Long,
        crowdMode: Boolean
    ): RealtimePersonTrack? {
        val maxCenterDistance = if (crowdMode) {
            REALTIME_CROWD_TRACK_MAX_CENTER_DISTANCE
        } else {
            REALTIME_TRACK_MAX_CENTER_DISTANCE
        }
        val maxSizeRatio = if (crowdMode) {
            REALTIME_CROWD_TRACK_MAX_SIZE_RATIO
        } else {
            REALTIME_TRACK_MAX_SIZE_RATIO
        }
        if (trackingId != null) {
            realtimePersonTracks.firstOrNull {
                it.trackingId == trackingId && now - it.lastSeenAt <= REALTIME_TRACK_STALE_MS
            }?.let { return it }
        }
        return realtimePersonTracks
            .asSequence()
            .filter { now - it.lastSeenAt <= REALTIME_TRACK_MATCH_GAP_MS }
            .map { track ->
                val dx = track.centerX - evaluation.faceCenterX
                val dy = track.centerY - evaluation.faceCenterY
                val distance = kotlin.math.sqrt(dx * dx + dy * dy)
                track to distance
            }
            .filter { (track, distance) ->
                distance <= maxCenterDistance &&
                    realtimeSizeRatio(track.sizeRatio, evaluation.faceAreaRatio) <= maxSizeRatio
            }
            .minByOrNull { it.second }
            ?.first
    }

    private fun drawRealtimeOverlaySnapshot(bitmap: Bitmap, snapshot: RealtimeOverlaySnapshot?): Bitmap {
        if (snapshot == null ||
            snapshot.boxes.isEmpty() ||
            System.currentTimeMillis() - snapshot.createdAt > REALTIME_OVERLAY_HOLD_MS
        ) {
            return bitmap
        }
        return try {
            val overlay = if (bitmap.isMutable) {
                bitmap
            } else {
                bitmap.copy(Bitmap.Config.ARGB_8888, true)
            }
            val canvas = Canvas(overlay)
            val scaleX = overlay.width.toFloat() / snapshot.frameWidth.toFloat().coerceAtLeast(1f)
            val scaleY = overlay.height.toFloat() / snapshot.frameHeight.toFloat().coerceAtLeast(1f)
            val rectPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
                style = Paint.Style.STROKE
                strokeWidth = maxOf(3f, minOf(overlay.width, overlay.height) / 180f)
            }
            val labelBgPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
                style = Paint.Style.FILL
            }
            val textPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
                style = Paint.Style.FILL
                textSize = maxOf(18f, minOf(overlay.width, overlay.height) / 24f)
                color = Color.WHITE
            }
            snapshot.boxes.forEach { box ->
                val rect = Rect(
                    (box.rect.left * scaleX).roundToInt().coerceIn(0, overlay.width),
                    (box.rect.top * scaleY).roundToInt().coerceIn(0, overlay.height),
                    (box.rect.right * scaleX).roundToInt().coerceIn(0, overlay.width),
                    (box.rect.bottom * scaleY).roundToInt().coerceIn(0, overlay.height)
                )
                if (rect.width() <= 0 || rect.height() <= 0) {
                    return@forEach
                }
                rectPaint.color = box.color
                canvas.drawRect(rect, rectPaint)
                val labelPadding = maxOf(4f, textPaint.textSize / 5f)
                val labelWidth = textPaint.measureText(box.label) + labelPadding * 2f
                val labelHeight = textPaint.textSize + labelPadding * 2f
                val labelLeft = rect.left.toFloat().coerceAtMost((overlay.width - labelWidth).coerceAtLeast(0f))
                val labelTop = (rect.top.toFloat() - labelHeight).takeIf { it >= 0f } ?: rect.top.toFloat()
                labelBgPaint.color = Color.argb(190, Color.red(box.color), Color.green(box.color), Color.blue(box.color))
                canvas.drawRect(labelLeft, labelTop, labelLeft + labelWidth, labelTop + labelHeight, labelBgPaint)
                canvas.drawText(
                    box.label,
                    labelLeft + labelPadding,
                    labelTop + labelPadding + textPaint.textSize * 0.82f,
                    textPaint
                )
            }
            overlay
        } catch (e: Exception) {
            recordDiagnostic("实时流预览标注失败", e)
            bitmap
        }
    }

    private fun drawRealtimeFaceOverlay(
        bitmap: Bitmap,
        faces: List<Face>,
        faceEvaluations: Map<Face, RealtimeFaceEvaluation>? = null,
        crowdModeForFrame: Boolean? = null
    ): Bitmap {
        if (faces.isEmpty()) {
            return bitmap
        }
        var crowdMode = crowdModeForFrame ?: isRealtimeCrowdModeActive(System.currentTimeMillis())
        val evaluations = faceEvaluations ?: run {
            var summary = evaluateRealtimeFacesWithSummary(bitmap, faces, crowdMode)
            if (crowdModeForFrame == null && !crowdMode) {
                if (summary.eligibleCount >= REALTIME_CROWD_MODE_MIN_FACES) {
                    crowdMode = true
                    summary = evaluateRealtimeFacesWithSummary(bitmap, faces, true)
                } else if (faces.size >= REALTIME_CROWD_MODE_MIN_FACES) {
                    val crowdProbeSummary = evaluateRealtimeFacesWithSummary(bitmap, faces, true)
                    if (crowdProbeSummary.eligibleCount >= REALTIME_CROWD_MODE_MIN_FACES) {
                        crowdMode = true
                        summary = crowdProbeSummary
                    }
                }
            }
            summary.evaluations
        }
        val snapshot = buildRealtimeOverlaySnapshot(bitmap.width, bitmap.height, faces, evaluations, crowdMode)
        return drawRealtimeOverlaySnapshot(bitmap, snapshot)
    }

    private fun maskStreamUrlForDiagnostics(rawUrl: String): String {
        return try {
            val uri = Uri.parse(rawUrl)
            val scheme = uri.scheme ?: "stream"
            val host = uri.host ?: return rawUrl.take(24) + if (rawUrl.length > 24) "..." else ""
            val port = if (uri.port > 0) ":${uri.port}" else ""
            val segments = uri.pathSegments.orEmpty()
            val safePath = if (segments.isEmpty()) {
                ""
            } else {
                "/" + segments.take(2).joinToString("/") + if (segments.size > 2) "/***" else ""
            }
            "$scheme://$host$port$safePath"
        } catch (_: Exception) {
            rawUrl.take(24) + if (rawUrl.length > 24) "..." else ""
        }
    }

    private fun updateVideoProgress(

        batchId: Long,

        text: String,

        progress: Int,

        max: Int,

        finished: Boolean

    ) {

        runOnUiThread {

            if (activeVideoBatchId != batchId) {

                return@runOnUiThread

            }

            binding.videoProgressPanel.visibility = View.VISIBLE

            binding.tvVideoProgress.text = text

            binding.videoBatchProgress.max = max.coerceAtLeast(1)

            binding.videoBatchProgress.progress = progress.coerceIn(0, max.coerceAtLeast(1))

            if (finished) {

                mainHandler.postDelayed({

                    if (activeVideoBatchId == batchId && !isVideoRecognitionRunning) {

                        binding.videoProgressPanel.visibility = View.GONE

                        recordDiagnostic("视频识别进度隐藏: batchId=$batchId")

                    }

                }, VIDEO_PROGRESS_HIDE_DELAY_MS)

            }

        }

    }

        private fun finishVideoRecognition(batchId: Long, message: String, foundCount: Int) {
        isVideoRecognitionRunning = false
        updateVideoProgress(batchId, message, 1, 1, finished = true)
        runOnUiThread {
            val outcome = when {
                foundCount > 0 -> "发现专家 ${foundCount} 人"
                message.contains("未检测到") || message.contains("未发现可识别") -> "未识别到人脸"
                else -> "未匹配到专家"
            }
            if (foundCount > 0) {
                playResultBeep(success = true)
                speakOut("视频识别完成，发现${foundCount}名专家")
                Toast.makeText(this, "视频识别完成，发现 ${foundCount} 名专家", Toast.LENGTH_SHORT).show()
            } else {
                playResultBeep(success = false)
                speakOut("视频识别完成，${outcome}")
                Toast.makeText(this, "视频识别完成，${outcome}", Toast.LENGTH_SHORT).show()
            }
        }
    }

    private fun processVideoForExperts(video: GalleryVideo, batchId: Long) {

        val startedAt = System.currentTimeMillis()

        val retriever = MediaMetadataRetriever()

        try {

            retriever.setDataSource(this, video.uri)

            val durationMs = readVideoDurationMs(retriever, video.durationMs)

            val quickSampleTimes = buildVideoQuickSampleTimes(durationMs)

            val faceHitTimes = mutableListOf<Long>()

            val candidates = mutableListOf<VideoFaceCandidate>()
            val rescueObservations = mutableListOf<VideoRescueObservation>()

            val processQuickFrame: (Int, Long, Long, Bitmap) -> Unit = { index, targetTimeMs, actualTimeMs, frame ->
                updateVideoProgress(
                    batchId,
                    "正在快速扫脸 ${index + 1}/${quickSampleTimes.size}",
                    index,
                    quickSampleTimes.size,
                    finished = false
                )
                try {
                    val detectionBitmap = resizeBitmapToMaxSide(frame, VIDEO_QUICK_PROCESS_MAX_SIDE)
                    val faces = Tasks.await(videoFaceDetector.process(InputImage.fromBitmap(detectionBitmap, 0)))
                    if (faces.isNotEmpty()) {
                        faceHitTimes.add(targetTimeMs)
                        val faceDetails = faces.joinToString(
                            prefix = "[",
                            postfix = "]",
                            limit = 4,
                            truncated = "..."
                        ) { face ->
                            "id=${face.trackingId ?: "-"},yaw=${face.headEulerAngleY.roundToInt()}," +
                                "pitch=${face.headEulerAngleX.roundToInt()}," +
                                "rect=${face.boundingBox.width()}x${face.boundingBox.height()}"
                        }
                        recordDiagnostic(
                            "视频快速扫脸命中: targetMs=$targetTimeMs, actualMs=$actualTimeMs, faces=${faces.size}, " +
                                "frame=${frame.width}x${frame.height}, detection=${detectionBitmap.width}x${detectionBitmap.height}, " +
                            "details=$faceDetails"
                        )
                    }
                    rescueObservations.add(
                        buildVideoRescueObservation(
                            frame,
                            detectionBitmap,
                            faces,
                            targetTimeMs
                        )
                    )
                    if (detectionBitmap !== frame) {
                        detectionBitmap.recycle()
                    }
                } finally {
                    frame.recycle()
                }
            }

            recordDiagnostic(

                "视频快速扫脸开始: name=${video.displayName}, durationMs=$durationMs, " +

                    "quickSamples=${quickSampleTimes.size}, first=${quickSampleTimes.firstOrNull() ?: 0}, " +

                    "last=${quickSampleTimes.lastOrNull() ?: 0}, mode=sequential-first"

            )

            val sequentialProcessedTimes = scanVideoFramesSequential(
                video.uri,
                quickSampleTimes,
                VIDEO_QUICK_DECODE_MAX_SIDE,
                processQuickFrame
            )
            val fallbackTimes = quickSampleTimes.filterNot { it in sequentialProcessedTimes }
            if (fallbackTimes.isNotEmpty()) {
                recordDiagnostic(
                    "视频快速扫脸回退取帧: processed=${sequentialProcessedTimes.size}, " +
                        "fallback=${fallbackTimes.size}, total=${quickSampleTimes.size}"
                )
            }
            fallbackTimes.forEach { timeMs ->
                val index = quickSampleTimes.indexOf(timeMs)
                val frame = extractVideoFrame(retriever, timeMs, precise = true, maxSide = VIDEO_QUICK_DECODE_MAX_SIDE)
                if (frame == null) {
                    recordDiagnostic("视频快速抽帧失败: timeMs=$timeMs")
                } else {
                    processQuickFrame(index, timeMs, timeMs, frame)
                }
            }

            if (faceHitTimes.isEmpty()) {
                recordDiagnostic(
                    "视频快速扫脸未命中，将尝试云端救援帧: quickSamples=${quickSampleTimes.size}, " +
                        "rescueObservations=${rescueObservations.size}, costMs=${System.currentTimeMillis() - startedAt}"
                )
            }

            // 每个粗扫命中都应进入精扫窗口。侧脸等困难角度可能没有稳定 trackingId，
            // 不能因为其他人脸拿到了 trackingId 就忽略这些命中时刻。
            val fineSampleTimes = if (faceHitTimes.isEmpty()) {
                emptyList()
            } else {
                buildVideoFocusedSampleTimes(faceHitTimes, durationMs)
            }

            recordDiagnostic(

                "视频加密抽帧开始: hitTimes=${faceHitTimes.size}, fineSamples=${fineSampleTimes.size}, " +

                    "first=${fineSampleTimes.firstOrNull() ?: 0}, last=${fineSampleTimes.lastOrNull() ?: 0}"

            )

            fineSampleTimes.forEachIndexed { index, timeMs ->

                updateVideoProgress(

                    batchId,

                    "正在精选清晰人脸 ${index + 1}/${fineSampleTimes.size}",

                    index,

                    fineSampleTimes.size,

                    finished = false

                )

                val frame = extractVideoFrame(retriever, timeMs, precise = true, maxSide = 960)

                if (frame == null) {

                    recordDiagnostic("视频加密抽帧失败: timeMs=$timeMs")

                    return@forEachIndexed

                }

                try {

                    val detectionBitmap = resizeBitmapToMaxSide(frame, VIDEO_FINE_PROCESS_MAX_SIDE)

                    val faces = Tasks.await(videoFaceDetector.process(InputImage.fromBitmap(detectionBitmap, 0)))

                    if (faces.isNotEmpty()) {

                        recordDiagnostic(

                            "视频加密帧本地检测: timeMs=$timeMs, faces=${faces.size}, " +

                                "frame=${frame.width}x${frame.height}, detection=${detectionBitmap.width}x${detectionBitmap.height}"

                        )

                    }

                    faces.forEach { face ->

                        val candidate = buildVideoFaceCandidate(video, frame, detectionBitmap, face, timeMs)

                        if (candidate != null) {

                            candidates.add(candidate)

                        }

                    }

                    if (detectionBitmap !== frame) {

                        detectionBitmap.recycle()

                    }

                } finally {

                    frame.recycle()

                }

            }

            val localUploadCandidates = selectVideoUploadCandidatesByPersons(candidates)
            val rescueCandidates = buildVideoRescueCandidates(
                video,
                retriever,
                rescueObservations,
                localUploadCandidates,
                (VIDEO_MAX_CLOUD_UPLOADS - localUploadCandidates.size).coerceAtLeast(0)
            )
            val uploadCandidates = mergeVideoLocalAndRescueCandidates(
                localUploadCandidates,
                rescueCandidates
            )
                .take(VIDEO_MAX_CLOUD_UPLOADS)

            recordDiagnostic(
                "视频云端上传计划: total=${uploadCandidates.size}, localPersons=${localUploadCandidates.size}, " +
                    "rescuePersons=${rescueCandidates.size}, candidates=${uploadCandidates.joinToString { candidate ->
                        "${candidate.frameTimeMs}ms/${if (candidate.isRescueFrame) "rescue" else "local"}/" +
                            "q=${candidate.qualityScore}/hash=${java.lang.Long.toHexString(candidate.faceHash)}"
                    }}"
            )

            recordDiagnostic(

                "视频本地候选完成: quickHits=${faceHitTimes.size}, fineSamples=${fineSampleTimes.size}, " +

                    "localCandidates=${candidates.size}, localPersons=${localUploadCandidates.size}, " +
                    "rescueObservations=${rescueObservations.size}, " +
                    "rescueCandidates=${rescueCandidates.size}, uploadCandidates=${uploadCandidates.size}, " +

                    "costMs=${System.currentTimeMillis() - startedAt}"

            )

            // 延迟编码：从 retriever 重新取帧编码为原始 JPEG，避免精扫阶段大量全帧 Bitmap 驻留内存
            uploadCandidates.forEach { candidate ->
                if (candidate.originalBytes == null) {
                    try {
                        val reFrame = extractVideoFrame(retriever, candidate.frameTimeMs)
                        if (reFrame != null) {
                            try {
                                candidate.originalBytes = bitmapToJpegBytes(reFrame, VIDEO_FRAME_JPEG_QUALITY)
                                recordDiagnostic(
                                    "视频原始帧延迟编码完成: timeMs=${candidate.frameTimeMs}, " +
                                        "candidateFrame=${candidate.originalWidth}x${candidate.originalHeight}, " +
                                        "savedFrame=${reFrame.width}x${reFrame.height}, bytes=${candidate.originalBytes?.size ?: 0}"
                                )
                            } finally {
                                reFrame.recycle()
                            }
                        } else {
                            recordDiagnostic("延迟取帧失败(retriever返回null): timeMs=${candidate.frameTimeMs}")
                        }
                    } catch (e: Exception) {
                        recordDiagnostic("延迟编码视频原始帧异常: timeMs=${candidate.frameTimeMs}", e)
                    }
                }
            }

            if (uploadCandidates.isEmpty()) {
                finishVideoRecognition(batchId, "视频中未检测到可识别人脸", 0)
                return
            }

            // 并行云端上传识别，云端返回多少条结果就保留多少条。
            val cloudMatches = java.util.Collections.synchronizedList(mutableListOf<VideoCloudMatch>())
            val completedCount = java.util.concurrent.atomic.AtomicInteger(0)
            val totalUploads = uploadCandidates.size
            val parallelism = 3.coerceAtMost(totalUploads)
            val latch = java.util.concurrent.CountDownLatch(totalUploads)
            val uploadPool = java.util.concurrent.Executors.newFixedThreadPool(parallelism)

            updateVideoProgress(batchId, "正在云端识别 0/$totalUploads", 0, totalUploads, finished = false)

            uploadCandidates.forEachIndexed { index, candidate ->
                uploadPool.submit {
                    try {
                        val base64Data = Base64.encodeToString(candidate.uploadBytes, Base64.NO_WRAP)

                        val requestMaxFaceNum = if (candidate.isRescueFrame) {
                            VIDEO_RESCUE_CLOUD_MAX_FACE_NUM
                        } else {
                            1
                        }
                        val result = searchFaceOnCloudSync(
                            "data:image/jpeg;base64,$base64Data",
                            requestMaxFaceNum,
                            "视频帧 ${index + 1}/$totalUploads ${candidate.frameTimeMs}ms rescue=${candidate.isRescueFrame}"
                        )

                        if (result.experts.isNotEmpty()) {
                            val expertsToSave = result.experts
                            expertsToSave.forEach { expert ->
                                cloudMatches.add(VideoCloudMatch(candidate, expert))
                            }
                            recordDiagnostic(
                                "视频候选云端命中: timeMs=${candidate.frameTimeMs}, rescue=${candidate.isRescueFrame}, " +
                                    "experts=${result.experts.size}, accepted=${expertsToSave.size}, " +
                                    "pendingMatches=${cloudMatches.size}"
                            )
                        } else {
                            recordDiagnostic(
                                "视频候选云端未命中: timeMs=${candidate.frameTimeMs}, " +
                                    "message=${result.message}"
                            )
                            val retryCandidate = buildVideoFullFrameRetryCandidate(candidate)
                            if (retryCandidate != null) {
                                recordDiagnostic(
                                    "视频候选云端未命中，尝试整帧救援: timeMs=${candidate.frameTimeMs}, " +
                                        "cropUpload=${candidate.uploadWidth}x${candidate.uploadHeight}, " +
                                        "fullUpload=${retryCandidate.uploadWidth}x${retryCandidate.uploadHeight}, " +
                                        "bytes=${retryCandidate.uploadBytes.size}"
                                )
                                val retryBase64 = Base64.encodeToString(retryCandidate.uploadBytes, Base64.NO_WRAP)
                                val retryResult = searchFaceOnCloudSync(
                                    "data:image/jpeg;base64,$retryBase64",
                                    VIDEO_RESCUE_CLOUD_MAX_FACE_NUM,
                                    "视频帧 ${index + 1}/$totalUploads ${candidate.frameTimeMs}ms fullFrameRetry=true"
                                )
                                if (retryResult.experts.isNotEmpty()) {
                                    retryResult.experts.forEach { expert ->
                                        cloudMatches.add(VideoCloudMatch(retryCandidate, expert))
                                    }
                                    recordDiagnostic(
                                        "视频整帧救援云端命中: timeMs=${candidate.frameTimeMs}, " +
                                            "experts=${retryResult.experts.size}, pendingMatches=${cloudMatches.size}"
                                    )
                                } else {
                                    recordDiagnostic(
                                        "视频整帧救援云端未命中: timeMs=${candidate.frameTimeMs}, " +
                                            "message=${retryResult.message}"
                                    )
                                }
                            } else {
                                recordDiagnostic(
                                    "视频候选整帧救援跳过: timeMs=${candidate.frameTimeMs}, " +
                                        "reason=缺少原始帧或已是救援帧"
                                )
                            }
                        }
                    } catch (e: Exception) {
                        recordDiagnostic("视频云端并行上传异常: timeMs=${candidate.frameTimeMs}", e)
                    } finally {
                        val done = completedCount.incrementAndGet()
                        updateVideoProgress(batchId, "正在云端识别 $done/$totalUploads", done, totalUploads, finished = false)
                        latch.countDown()
                    }
                }
            }

            try {
                latch.await(120, java.util.concurrent.TimeUnit.SECONDS)
            } catch (e: InterruptedException) {
                recordDiagnostic("视频云端并行上传等待超时")
            }
            uploadPool.shutdown()

            var savedCount = 0
            cloudMatches.sortedBy { it.candidate.frameTimeMs }.forEach { match ->
                savedCount += saveVideoExpertRecords(
                    video,
                    match.candidate,
                    listOf(match.expert)
                )
            }
            recordDiagnostic(
                "视频云端结果汇总: raw=${cloudMatches.size}, saved=$savedCount, dedup=false"
            )
            val message = if (savedCount > 0) {
                "视频识别完成，发现 $savedCount 名专家"
            } else {
                "视频识别完成，未发现匹配专家"
            }

            finishVideoRecognition(batchId, message, savedCount)

        } catch (e: Exception) {

            recordDiagnostic("视频识别异常: name=${video.displayName}", e)

            finishVideoRecognition(batchId, "视频识别异常，已记录日志", 0)

        } finally {

            try {

                retriever.release()

            } catch (e: Exception) {

                // ignore

            }

        }

    }

    private fun readVideoDurationMs(retriever: MediaMetadataRetriever, fallbackMs: Long): Long {

        val metaDuration = retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_DURATION)

            ?.toLongOrNull()

        return (metaDuration ?: fallbackMs).coerceAtLeast(0L)

    }

    private fun scanVideoFramesSequential(
        uri: Uri,
        targetTimesMs: List<Long>,
        maxSide: Int,
        onFrame: (index: Int, targetTimeMs: Long, actualTimeMs: Long, bitmap: Bitmap) -> Unit
    ): Set<Long> {
        if (targetTimesMs.isEmpty()) {
            return emptySet()
        }
        val processedTimes = linkedSetOf<Long>()
        val extractor = MediaExtractor()
        var codec: MediaCodec? = null
        try {
            extractor.setDataSource(this, uri, null)
            var videoTrack = -1
            var format: MediaFormat? = null
            for (trackIndex in 0 until extractor.trackCount) {
                val candidate = extractor.getTrackFormat(trackIndex)
                val mime = candidate.getString(MediaFormat.KEY_MIME).orEmpty()
                if (mime.startsWith("video/")) {
                    videoTrack = trackIndex
                    format = candidate
                    break
                }
            }
            if (videoTrack < 0 || format == null) {
                recordDiagnostic("视频顺序解码不可用: 未找到视频轨道")
                return emptySet()
            }

            val mime = format.getString(MediaFormat.KEY_MIME).orEmpty()
            val rotationDegrees = if (format.containsKey(MediaFormat.KEY_ROTATION)) {
                format.getInteger(MediaFormat.KEY_ROTATION)
            } else {
                0
            }
            format.setInteger(
                MediaFormat.KEY_COLOR_FORMAT,
                android.media.MediaCodecInfo.CodecCapabilities.COLOR_FormatYUV420Flexible
            )
            extractor.selectTrack(videoTrack)
            codec = MediaCodec.createDecoderByType(mime)
            codec.configure(format, null, null, 0)
            codec.start()

            val bufferInfo = MediaCodec.BufferInfo()
            var inputDone = false
            var outputDone = false
            var targetIndex = 0
            var idleLoops = 0
            val startedAt = System.currentTimeMillis()

            while (!outputDone && targetIndex < targetTimesMs.size && idleLoops < VIDEO_CODEC_MAX_IDLE_LOOPS) {
                var madeProgress = false
                if (!inputDone) {
                    val inputIndex = codec.dequeueInputBuffer(VIDEO_CODEC_DEQUEUE_TIMEOUT_US)
                    if (inputIndex >= 0) {
                        val inputBuffer = codec.getInputBuffer(inputIndex)
                        val sampleSize = if (inputBuffer != null) {
                            extractor.readSampleData(inputBuffer, 0)
                        } else {
                            -1
                        }
                        if (sampleSize < 0) {
                            codec.queueInputBuffer(
                                inputIndex,
                                0,
                                0,
                                0L,
                                MediaCodec.BUFFER_FLAG_END_OF_STREAM
                            )
                            inputDone = true
                        } else {
                            codec.queueInputBuffer(
                                inputIndex,
                                0,
                                sampleSize,
                                extractor.sampleTime.coerceAtLeast(0L),
                                0
                            )
                            extractor.advance()
                        }
                        madeProgress = true
                    }
                }

                when (val outputIndex = codec.dequeueOutputBuffer(bufferInfo, VIDEO_CODEC_DEQUEUE_TIMEOUT_US)) {
                    MediaCodec.INFO_TRY_AGAIN_LATER -> Unit
                    MediaCodec.INFO_OUTPUT_FORMAT_CHANGED -> {
                        recordDiagnostic("视频顺序解码输出格式: ${codec.outputFormat}")
                        madeProgress = true
                    }
                    else -> if (outputIndex >= 0) {
                        madeProgress = true
                        val actualTimeMs = bufferInfo.presentationTimeUs.coerceAtLeast(0L) / 1000L
                        if (bufferInfo.size > 0 && actualTimeMs >= targetTimesMs[targetIndex]) {
                            var selectedTargetIndex = targetIndex
                            while (selectedTargetIndex + 1 < targetTimesMs.size &&
                                targetTimesMs[selectedTargetIndex + 1] <= actualTimeMs
                            ) {
                                selectedTargetIndex += 1
                            }
                            val targetTimeMs = targetTimesMs[selectedTargetIndex]
                            val image = codec.getOutputImage(outputIndex)
                            if (image != null) {
                                image.use {
                                    var bitmap = yuvImageToScaledBitmap(it, maxSide)
                                    bitmap = applyVideoRotation(bitmap, rotationDegrees)
                                    onFrame(selectedTargetIndex, targetTimeMs, actualTimeMs, bitmap)
                                    processedTimes.add(targetTimeMs)
                                }
                            }
                            targetIndex = selectedTargetIndex + 1
                        }
                        outputDone = bufferInfo.flags and MediaCodec.BUFFER_FLAG_END_OF_STREAM != 0
                        codec.releaseOutputBuffer(outputIndex, false)
                    }
                }

                idleLoops = if (madeProgress) 0 else idleLoops + 1
            }

            recordDiagnostic(
                "视频顺序解码完成: processed=${processedTimes.size}/${targetTimesMs.size}, " +
                    "rotation=$rotationDegrees, costMs=${System.currentTimeMillis() - startedAt}, " +
                    "inputDone=$inputDone, outputDone=$outputDone, idleLoops=$idleLoops"
            )
        } catch (e: Exception) {
            recordDiagnostic(
                "视频顺序解码失败，回退精确取帧: processed=${processedTimes.size}/${targetTimesMs.size}",
                e
            )
        } finally {
            try {
                codec?.stop()
            } catch (_: Exception) {
            }
            try {
                codec?.release()
            } catch (_: Exception) {
            }
            try {
                extractor.release()
            } catch (_: Exception) {
            }
        }
        return processedTimes
    }

    private fun yuvImageToScaledBitmap(image: Image, maxSide: Int): Bitmap {
        require(image.planes.size >= 3) { "Unsupported decoded image planes=${image.planes.size}" }
        val crop = image.cropRect
        val sourceWidth = crop.width().coerceAtLeast(1)
        val sourceHeight = crop.height().coerceAtLeast(1)
        val scale = if (maxSide > 0) {
            minOf(1f, maxSide.toFloat() / maxOf(sourceWidth, sourceHeight).toFloat())
        } else {
            1f
        }
        val targetWidth = (sourceWidth * scale).roundToInt().coerceAtLeast(1)
        val targetHeight = (sourceHeight * scale).roundToInt().coerceAtLeast(1)
        val yPlane = image.planes[0]
        val uPlane = image.planes[1]
        val vPlane = image.planes[2]
        val yBuffer = yPlane.buffer
        val uBuffer = uPlane.buffer
        val vBuffer = vPlane.buffer
        val pixels = IntArray(targetWidth * targetHeight)

        for (targetY in 0 until targetHeight) {
            val sourceY = crop.top + (targetY * sourceHeight / targetHeight)
            for (targetX in 0 until targetWidth) {
                val sourceX = crop.left + (targetX * sourceWidth / targetWidth)
                val yValue = readImagePlaneValue(yBuffer, yPlane, sourceX, sourceY)
                val chromaX = sourceX / 2
                val chromaY = sourceY / 2
                val uValue = readImagePlaneValue(uBuffer, uPlane, chromaX, chromaY) - 128
                val vValue = readImagePlaneValue(vBuffer, vPlane, chromaX, chromaY) - 128
                val luminance = (yValue - 16).coerceAtLeast(0)
                val red = ((298 * luminance + 409 * vValue + 128) shr 8).coerceIn(0, 255)
                val green = ((298 * luminance - 100 * uValue - 208 * vValue + 128) shr 8).coerceIn(0, 255)
                val blue = ((298 * luminance + 516 * uValue + 128) shr 8).coerceIn(0, 255)
                pixels[targetY * targetWidth + targetX] = Color.rgb(red, green, blue)
            }
        }
        return Bitmap.createBitmap(pixels, targetWidth, targetHeight, Bitmap.Config.ARGB_8888)
    }

    private fun readImagePlaneValue(
        buffer: java.nio.ByteBuffer,
        plane: Image.Plane,
        x: Int,
        y: Int
    ): Int {
        val index = buffer.position() + y * plane.rowStride + x * plane.pixelStride
        if (index < buffer.position() || index >= buffer.limit()) {
            return 128
        }
        return buffer.get(index).toInt() and 0xFF
    }

    private fun applyVideoRotation(bitmap: Bitmap, rotationDegrees: Int): Bitmap {
        val normalized = ((rotationDegrees % 360) + 360) % 360
        if (normalized == 0) {
            return bitmap
        }
        return try {
            val matrix = Matrix().apply { postRotate(normalized.toFloat()) }
            val rotated = Bitmap.createBitmap(bitmap, 0, 0, bitmap.width, bitmap.height, matrix, true)
            if (rotated !== bitmap) {
                bitmap.recycle()
            }
            rotated
        } catch (e: Exception) {
            recordDiagnostic("视频顺序解码方向修正失败: rotation=$rotationDegrees", e)
            bitmap
        }
    }

    private fun buildVideoQuickSampleTimes(durationMs: Long): List<Long> {

        if (durationMs <= 0L) {

            return listOf(0L)

        }

        val intervalMs = if (durationMs <= VIDEO_QUICK_SHORT_DURATION_MS) {

            VIDEO_QUICK_SHORT_INTERVAL_MS

        } else if (durationMs <= VIDEO_QUICK_DENSE_DURATION_MS) {

            VIDEO_QUICK_SAMPLE_INTERVAL_MS

        } else {
            VIDEO_QUICK_SAMPLE_INTERVAL_MS
        }

        val naturalSampleCount = (durationMs / intervalMs + 1L).coerceAtLeast(1L)
        if (naturalSampleCount <= VIDEO_MAX_QUICK_SAMPLE_FRAMES) {
            val times = mutableListOf<Long>()
            var timeMs = 0L
            while (timeMs <= durationMs) {
                times.add(timeMs)
                timeMs += intervalMs
            }
            if (times.lastOrNull() != durationMs) {
                times.add(durationMs)
            }
            return times.distinct()
        }

        return (0 until VIDEO_MAX_QUICK_SAMPLE_FRAMES).map { index ->
            if (VIDEO_MAX_QUICK_SAMPLE_FRAMES == 1) {
                0L
            } else {
                (index * durationMs.toDouble() / (VIDEO_MAX_QUICK_SAMPLE_FRAMES - 1).toDouble())
                    .toLong()
                    .coerceIn(0L, durationMs)
            }
        }.distinct()

    }

    private fun buildVideoFocusedSampleTimes(hitTimes: List<Long>, durationMs: Long): List<Long> {

        if (hitTimes.isEmpty()) {

            return emptyList()

        }

        val times = TreeSet<Long>()

        hitTimes.forEach { hitTime ->

            val start = (hitTime - VIDEO_FINE_WINDOW_BEFORE_MS).coerceAtLeast(0L)

            val end = (hitTime + VIDEO_FINE_WINDOW_AFTER_MS).coerceAtMost(durationMs.coerceAtLeast(0L))

            var timeMs = start

            while (timeMs <= end) {

                times.add(timeMs)

                timeMs += VIDEO_FINE_SAMPLE_INTERVAL_MS

            }

            times.add(hitTime.coerceIn(0L, durationMs.coerceAtLeast(0L)))

        }

        if (times.size <= VIDEO_MAX_FINE_SAMPLE_FRAMES) {

            return times.toList()

        }

        val sorted = times.toList()

        val sampled = mutableListOf<Long>()

        for (i in 0 until VIDEO_MAX_FINE_SAMPLE_FRAMES) {

            val sourceIndex = if (VIDEO_MAX_FINE_SAMPLE_FRAMES == 1) {

                0

            } else {

                (i * (sorted.size - 1).toFloat() / (VIDEO_MAX_FINE_SAMPLE_FRAMES - 1).toFloat()).roundToInt()

            }

            sampled.add(sorted[sourceIndex.coerceIn(0, sorted.lastIndex)])

        }

        return sampled.distinct()

    }

    private fun selectVideoUploadCandidatesByPersons(
        candidates: List<VideoFaceCandidate>
    ): List<VideoFaceCandidate> {
        val trackingCandidates = candidates
            .sortedBy { it.frameTimeMs }
        if (trackingCandidates.isEmpty()) {
            return emptyList()
        }

        data class PersonCluster(
            val candidates: MutableList<VideoFaceCandidate>,
            val trackingIds: MutableSet<Int>
        )

        val personClusters = mutableListOf<PersonCluster>()
        trackingCandidates.groupBy { it.frameTimeMs }
            .toSortedMap()
            .forEach { (_, frameCandidates) ->
                data class Match(
                    val clusterIndex: Int,
                    val candidateIndex: Int,
                    val score: Int
                )

                val matches = mutableListOf<Match>()
                personClusters.forEachIndexed { clusterIndex, cluster ->
                    frameCandidates.forEachIndexed { candidateIndex, candidate ->
                        val score = videoPersonTrackMatchScore(cluster.candidates, candidate)
                        if (score >= VIDEO_PERSON_MATCH_MIN_SCORE) {
                            matches.add(Match(clusterIndex, candidateIndex, score))
                        }
                    }
                }

                val assignedClusters = mutableSetOf<Int>()
                val assignedCandidates = mutableSetOf<Int>()
                matches.sortedByDescending { it.score }.forEach { match ->
                    if (match.clusterIndex !in assignedClusters &&
                        match.candidateIndex !in assignedCandidates
                    ) {
                        val candidate = frameCandidates[match.candidateIndex]
                        val cluster = personClusters[match.clusterIndex]
                        cluster.candidates.add(candidate)
                        candidate.trackingId?.let { cluster.trackingIds.add(it) }
                        assignedClusters.add(match.clusterIndex)
                        assignedCandidates.add(match.candidateIndex)
                    }
                }

                frameCandidates.forEachIndexed { candidateIndex, candidate ->
                    if (candidateIndex !in assignedCandidates) {
                        personClusters.add(
                            PersonCluster(
                                candidates = mutableListOf(candidate),
                                trackingIds = candidate.trackingId?.let { mutableSetOf(it) }
                                    ?: mutableSetOf()
                            )
                        )
                    }
                }
            }

        val stitchedClusters = stitchVideoPersonTracklets(personClusters.map { it.candidates })
        val selected = stitchedClusters.mapNotNull { cluster ->
            val best = cluster.maxByOrNull { it.qualityScore } ?: return@mapNotNull null
            val isUsableSideProfile = abs(best.yaw) >= VIDEO_SIDE_PROFILE_MIN_YAW &&
                best.qualityScore >= VIDEO_SIDE_PROFILE_MIN_UPLOAD_QUALITY_SCORE
            if (best.qualityScore < VIDEO_MIN_UPLOAD_QUALITY_SCORE && !isUsableSideProfile) {
                return@mapNotNull null
            }
            best.personTrackSignatures = cluster.map { it.toVideoPersonSignature() }
            best
        }.sortedByDescending { it.qualityScore }

        recordDiagnostic(
            "视频人物候选聚合: localCandidates=${candidates.size}, trackingCandidates=${trackingCandidates.size}, " +
                "initialPersons=${personClusters.size}, persons=${stitchedClusters.size}, selected=${selected.size}, " +
                "clusters=${stitchedClusters.joinToString(limit = 10, truncated = "...") { cluster ->
                    val best = cluster.maxByOrNull { it.qualityScore }
                    "count=${cluster.size}/ids=${cluster.mapNotNull { it.trackingId }.toSet()}/" +
                        "best=${best?.frameTimeMs ?: -1}ms/q=${best?.qualityScore ?: 0}/" +
                        "yaw=${best?.yaw?.roundToInt() ?: 0}/" +
                        "center=${best?.faceCenterX?.let { "%.2f".format(Locale.ROOT, it) }}," +
                        "${best?.faceCenterY?.let { "%.2f".format(Locale.ROOT, it) }}/" +
                        "range=${cluster.minOfOrNull { it.frameTimeMs } ?: -1}-" +
                        "${cluster.maxOfOrNull { it.frameTimeMs } ?: -1}ms"
                }}"
        )
        return selected
            .take(VIDEO_MAX_CLOUD_UPLOADS)
    }

    private fun VideoFaceCandidate.toVideoPersonSignature(): VideoPersonSignature {
        return VideoPersonSignature(
            frameTimeMs = frameTimeMs,
            qualityScore = qualityScore,
            differenceHash = differenceHash,
            mirroredDifferenceHash = mirroredDifferenceHash,
            appearanceHistogram = appearanceHistogram,
            faceAreaRatio = faceAreaRatio,
            faceCenterX = faceCenterX,
            faceCenterY = faceCenterY,
            yaw = yaw
        )
    }

    private fun stitchVideoPersonTracklets(
        sourceClusters: List<List<VideoFaceCandidate>>
    ): List<MutableList<VideoFaceCandidate>> {
        val clusters = sourceClusters
            .filter { it.isNotEmpty() }
            .map { it.sortedBy { candidate -> candidate.frameTimeMs }.toMutableList() }
            .toMutableList()
        var mergeCount = 0
        while (true) {
            var bestLeft = -1
            var bestRight = -1
            var bestScore = Int.MIN_VALUE
            for (leftIndex in 0 until clusters.lastIndex) {
                for (rightIndex in leftIndex + 1 until clusters.size) {
                    val score = videoTrackletStitchScore(
                        clusters[leftIndex],
                        clusters[rightIndex]
                    )
                    if (score > bestScore) {
                        bestScore = score
                        bestLeft = leftIndex
                        bestRight = rightIndex
                    }
                }
            }
            if (bestLeft < 0 || bestScore < VIDEO_TRACKLET_STITCH_MIN_SCORE) {
                break
            }
            val left = clusters[bestLeft]
            val right = clusters[bestRight]
            recordDiagnostic(
                "视频人物轨迹二次拼接: score=$bestScore, " +
                    "left=${left.minOf { it.frameTimeMs }}-${left.maxOf { it.frameTimeMs }}ms, " +
                    "right=${right.minOf { it.frameTimeMs }}-${right.maxOf { it.frameTimeMs }}ms"
            )
            left.addAll(right)
            left.sortBy { it.frameTimeMs }
            clusters.removeAt(bestRight)
            mergeCount += 1
        }
        recordDiagnostic(
            "视频人物轨迹二次拼接完成: source=${sourceClusters.size}, " +
                "merged=$mergeCount, result=${clusters.size}"
        )
        return clusters
    }

    private fun videoTrackletStitchScore(
        first: List<VideoFaceCandidate>,
        second: List<VideoFaceCandidate>
    ): Int {
        val left: List<VideoFaceCandidate>
        val right: List<VideoFaceCandidate>
        if (first.minOf { it.frameTimeMs } <= second.minOf { it.frameTimeMs }) {
            left = first
            right = second
        } else {
            left = second
            right = first
        }
        val leftEnd = left.maxOf { it.frameTimeMs }
        val rightStart = right.minOf { it.frameTimeMs }
        val gapMs = rightStart - leftEnd
        if (gapMs < VIDEO_TRACKLET_MIN_NON_OVERLAP_MS ||
            gapMs > VIDEO_TRACKLET_MAX_STITCH_GAP_MS
        ) {
            return Int.MIN_VALUE
        }

        val leftRepresentatives = left.sortedByDescending { it.qualityScore }
            .take(VIDEO_TRACKLET_REPRESENTATIVE_COUNT)
        val rightRepresentatives = right.sortedByDescending { it.qualityScore }
            .take(VIDEO_TRACKLET_REPRESENTATIVE_COUNT)
        var bestAppearanceScore = Int.MIN_VALUE
        leftRepresentatives.forEach { leftCandidate ->
            rightRepresentatives.forEach { rightCandidate ->
                val dHashDistance = minOf(
                    hammingDistance(leftCandidate.differenceHash, rightCandidate.differenceHash),
                    hammingDistance(leftCandidate.differenceHash, rightCandidate.mirroredDifferenceHash),
                    hammingDistance(leftCandidate.mirroredDifferenceHash, rightCandidate.differenceHash)
                )
                val averageHashDistance = hammingDistance(
                    leftCandidate.faceHash,
                    rightCandidate.faceHash
                )
                val histogramSimilarity = histogramCosineSimilarity(
                    leftCandidate.appearanceHistogram,
                    rightCandidate.appearanceHistogram
                )
                val appearanceScore = 100 -
                    dHashDistance * VIDEO_TRACKLET_DHASH_PENALTY -
                    averageHashDistance * VIDEO_TRACKLET_AHASH_PENALTY +
                    (histogramSimilarity * VIDEO_TRACKLET_HISTOGRAM_BONUS).roundToInt()
                bestAppearanceScore = maxOf(bestAppearanceScore, appearanceScore)
            }
        }
        if (bestAppearanceScore < VIDEO_TRACKLET_MIN_APPEARANCE_SCORE) {
            return Int.MIN_VALUE
        }
        return bestAppearanceScore -
            (gapMs / VIDEO_TRACKLET_GAP_PENALTY_DIVISOR_MS).toInt()
    }

    private fun histogramCosineSimilarity(left: IntArray, right: IntArray): Float {
        if (left.isEmpty() || right.isEmpty() || left.size != right.size) {
            return 0f
        }
        var dot = 0.0
        var leftNorm = 0.0
        var rightNorm = 0.0
        left.indices.forEach { index ->
            val leftValue = left[index].toDouble()
            val rightValue = right[index].toDouble()
            dot += leftValue * rightValue
            leftNorm += leftValue * leftValue
            rightNorm += rightValue * rightValue
        }
        if (leftNorm <= 0.0 || rightNorm <= 0.0) {
            return 0f
        }
        return (dot / kotlin.math.sqrt(leftNorm * rightNorm)).toFloat()
    }

    private fun videoPersonTrackMatchScore(
        trackCandidates: List<VideoFaceCandidate>,
        candidate: VideoFaceCandidate
    ): Int {
        val last = trackCandidates.maxByOrNull { it.frameTimeMs } ?: return Int.MIN_VALUE
        val timeGapMs = candidate.frameTimeMs - last.frameTimeMs
        if (timeGapMs <= 0L || timeGapMs > VIDEO_PERSON_TRACK_MAX_GAP_MS) {
            return Int.MIN_VALUE
        }

        val previous = trackCandidates
            .asSequence()
            .filter { it.frameTimeMs < last.frameTimeMs }
            .maxByOrNull { it.frameTimeMs }
        val predictedCenterX: Float
        val predictedCenterY: Float
        if (previous != null) {
            val previousGapMs = (last.frameTimeMs - previous.frameTimeMs).coerceAtLeast(1L)
            val predictionRatio = (
                timeGapMs.toFloat() / previousGapMs.toFloat()
                ).coerceIn(0f, VIDEO_PERSON_MAX_PREDICTION_RATIO)
            predictedCenterX = last.faceCenterX +
                (last.faceCenterX - previous.faceCenterX) * predictionRatio
            predictedCenterY = last.faceCenterY +
                (last.faceCenterY - previous.faceCenterY) * predictionRatio
        } else {
            predictedCenterX = last.faceCenterX
            predictedCenterY = last.faceCenterY
        }

        val dx = candidate.faceCenterX - predictedCenterX
        val dy = candidate.faceCenterY - predictedCenterY
        val centerDistance = kotlin.math.sqrt(dx * dx + dy * dy)
        val allowedCenterDistance = (
            VIDEO_PERSON_BASE_CENTER_DISTANCE +
                timeGapMs.toFloat() / VIDEO_PERSON_TRACK_MAX_GAP_MS.toFloat() *
                VIDEO_PERSON_CENTER_DISTANCE_GROWTH
            ).coerceAtMost(VIDEO_PERSON_MAX_CENTER_DISTANCE)
        val sizeRatio = videoCandidateSizeRatio(last.faceAreaRatio, candidate.faceAreaRatio)
        val hashDistance = hammingDistance(last.faceHash, candidate.faceHash)
        val sameTrackingId = last.trackingId != null &&
            last.trackingId == candidate.trackingId
        val strongAppearanceMatch = hashDistance <= VIDEO_PERSON_STRONG_HASH_DISTANCE

        if (!sameTrackingId && !strongAppearanceMatch &&
            (centerDistance > allowedCenterDistance ||
                sizeRatio > VIDEO_PERSON_MAX_SIZE_RATIO)
        ) {
            return Int.MIN_VALUE
        }

        var score = VIDEO_PERSON_BASE_MATCH_SCORE
        score -= (centerDistance * VIDEO_PERSON_CENTER_PENALTY).roundToInt()
        score -= (timeGapMs / VIDEO_PERSON_TIME_PENALTY_DIVISOR_MS).toInt()
        score -= (kotlin.math.ln(sizeRatio.toDouble()) *
            VIDEO_PERSON_SIZE_RATIO_PENALTY).roundToInt()
        if (sameTrackingId) {
            score += VIDEO_PERSON_TRACKING_ID_BONUS
        }
        if (hashDistance <= VIDEO_PERSON_RELAXED_HASH_DISTANCE) {
            score += (VIDEO_PERSON_RELAXED_HASH_DISTANCE - hashDistance) *
                VIDEO_PERSON_HASH_BONUS_PER_BIT
        }
        return score
    }

    private fun videoCandidateSizeRatio(leftArea: Float, rightArea: Float): Float {
        val smaller = minOf(leftArea, rightArea).coerceAtLeast(0.000001f)
        val larger = maxOf(leftArea, rightArea).coerceAtLeast(smaller)
        return larger / smaller
    }

    private fun buildVideoRescueObservation(
        bitmap: Bitmap,
        detectionBitmap: Bitmap,
        faces: List<Face>,
        frameTimeMs: Long
    ): VideoRescueObservation {
        data class DetectedFaceRegion(
            val rect: FaceRect,
            val reliable: Boolean
        )

        val detectedRegions = faces.mapNotNull { face ->
            clippedRect(face.boundingBox, detectionBitmap.width, detectionBitmap.height)?.let { rect ->
                val faceAreaRatio = rect.width().toFloat() * rect.height().toFloat() /
                    (detectionBitmap.width.toFloat() * detectionBitmap.height.toFloat())
                        .coerceAtLeast(1f)
                val shouldMaskAsReliableLocalFace =
                    rect.width() >= VIDEO_RESCUE_MASK_MIN_FACE_SIDE &&
                        rect.height() >= VIDEO_RESCUE_MASK_MIN_FACE_SIDE &&
                        faceAreaRatio >= VIDEO_MIN_FACE_AREA_RATIO &&
                        abs(face.headEulerAngleY) <= VIDEO_RESCUE_MASK_MAX_YAW &&
                        abs(face.headEulerAngleX) <= VIDEO_RESCUE_MASK_MAX_PITCH
                DetectedFaceRegion(
                    rect = FaceRect(
                        x = rect.left.toFloat() / detectionBitmap.width.toFloat(),
                        y = rect.top.toFloat() / detectionBitmap.height.toFloat(),
                        width = rect.width().toFloat() / detectionBitmap.width.toFloat(),
                        height = rect.height().toFloat() / detectionBitmap.height.toFloat()
                    ),
                    reliable = shouldMaskAsReliableLocalFace
                )
            }
        }
        val knownFaceRects = detectedRegions.filter { it.reliable }.map { it.rect }
        val unmaskedDetectedFace = detectedRegions
            .filterNot { it.reliable }
            .maxByOrNull { it.rect.width * it.rect.height }
            ?.rect
        val analysis = if (unmaskedDetectedFace != null) {
            analyzeVideoRescueDetectedFace(bitmap, unmaskedDetectedFace)
        } else {
            analyzeVideoRescueRegion(bitmap, knownFaceRects)
        }
        val sharpnessRect = analysis.regionRect?.toPixelRect(bitmap.width, bitmap.height)
        val sharpness = sharpnessRect?.let { estimateFaceSharpness(bitmap, it) } ?: 0
        val score = sharpness +
            (analysis.skinRatio * VIDEO_RESCUE_SKIN_SCORE_WEIGHT).roundToInt()
        return VideoRescueObservation(
            frameTimeMs = frameTimeMs,
            qualityScore = score,
            regionHash = analysis.regionHash,
            skinRatio = analysis.skinRatio,
            localFaceCount = faces.size,
            knownFaceRects = knownFaceRects,
            detectedFaceRects = detectedRegions.map { it.rect },
            unmaskedDetectedFaceCount = detectedRegions.count { !it.reliable },
            regionRect = analysis.regionRect,
            regionCenterX = analysis.regionCenterX,
            regionCenterY = analysis.regionCenterY,
            regionAreaRatio = analysis.regionAreaRatio
        )
    }

    private fun analyzeVideoRescueDetectedFace(
        bitmap: Bitmap,
        normalizedRect: FaceRect
    ): VideoRescueRegionAnalysis {
        val pixelRect = normalizedRect.toPixelRect(bitmap.width, bitmap.height)
            ?: return VideoRescueRegionAnalysis()
        val crop = Bitmap.createBitmap(
            bitmap,
            pixelRect.left,
            pixelRect.top,
            pixelRect.width(),
            pixelRect.height()
        )
        val sample = resizeBitmapToMaxSide(crop, VIDEO_RESCUE_SKIN_SAMPLE_SIDE)
        val pixels = IntArray(sample.width * sample.height)
        sample.getPixels(pixels, 0, sample.width, 0, 0, sample.width, sample.height)
        val skinRatio = pixels.count { isLikelySkinColor(it) }.toFloat() /
            pixels.size.coerceAtLeast(1).toFloat()
        if (sample !== crop) {
            sample.recycle()
        }
        crop.recycle()
        return VideoRescueRegionAnalysis(
            skinRatio = skinRatio,
            regionHash = averageFaceHash(bitmap, pixelRect),
            regionRect = normalizedRect,
            regionCenterX = normalizedRect.x + normalizedRect.width / 2f,
            regionCenterY = normalizedRect.y + normalizedRect.height / 2f,
            regionAreaRatio = normalizedRect.width * normalizedRect.height
        )
    }

    private fun buildVideoRescueCandidates(
        video: GalleryVideo,
        retriever: MediaMetadataRetriever,
        observations: List<VideoRescueObservation>,
        localCandidates: List<VideoFaceCandidate>,
        maxCandidates: Int
    ): List<VideoFaceCandidate> {
        if (observations.isEmpty() || maxCandidates <= 0) {
            return emptyList()
        }

        data class RescuePersonCluster(
            val observations: MutableList<VideoRescueObservation>
        )

        val eligible = observations
            .filter { observation ->
                observation.regionRect != null &&
                    observation.skinRatio >= VIDEO_RESCUE_MIN_SKIN_RATIO
            }
            .sortedBy { it.frameTimeMs }

        val clusters = mutableListOf<RescuePersonCluster>()
        eligible.forEach { observation ->
            val matchedCluster = clusters
                .mapNotNull { cluster ->
                    val score = cluster.observations
                        .map { existing -> videoRescuePersonMatchScore(existing, observation) }
                        .maxOrNull()
                        ?: Int.MIN_VALUE
                    if (score >= VIDEO_RESCUE_PERSON_MATCH_MIN_SCORE) {
                        cluster to score
                    } else {
                        null
                    }
                }
                .maxByOrNull { it.second }
                ?.first
            if (matchedCluster == null) {
                clusters.add(RescuePersonCluster(mutableListOf(observation)))
            } else {
                matchedCluster.observations.add(observation)
            }
        }

        val selectedObservations = clusters
            .mapNotNull { cluster ->
                cluster.observations.maxWithOrNull(
                    compareBy<VideoRescueObservation> { videoRescueObservationPriority(it) }
                        .thenBy { it.qualityScore }
                )
            }
            .sortedWith(
                compareByDescending<VideoRescueObservation> {
                    videoRescueObservationPriority(it)
                }.thenByDescending { it.qualityScore }
            )
            .take(minOf(VIDEO_MAX_RESCUE_UPLOADS, maxCandidates))

        val rescueCandidates = selectedObservations.mapNotNull { observation ->
            val frame = extractVideoFrame(
                retriever,
                observation.frameTimeMs,
                precise = true,
                maxSide = VIDEO_MAX_UPLOAD_IMAGE_SIDE
            ) ?: return@mapNotNull null
            try {
                val maskedFrame = maskKnownFacesForVideoRescue(frame, observation.knownFaceRects)
                try {
                    val uploadBytes = bitmapToJpegBytes(maskedFrame, VIDEO_FRAME_JPEG_QUALITY)
                    val localFaceRect = observation.regionRect?.let { rect ->
                        FaceRect(
                            x = rect.x * maskedFrame.width,
                            y = rect.y * maskedFrame.height,
                            width = rect.width * maskedFrame.width,
                            height = rect.height * maskedFrame.height
                        )
                    } ?: FaceRect(
                        0f,
                        0f,
                        maskedFrame.width.toFloat(),
                        maskedFrame.height.toFloat()
                    )
                    val descriptorRect = localFaceRect.toPixelRect(
                        maskedFrame.width,
                        maskedFrame.height
                    ) ?: Rect(0, 0, maskedFrame.width, maskedFrame.height)
                    VideoFaceCandidate(
                        frameTimeMs = observation.frameTimeMs,
                        qualityScore = observation.qualityScore,
                        faceHash = observation.regionHash,
                        differenceHash = differenceFaceHash(
                            maskedFrame,
                            descriptorRect,
                            mirror = false
                        ),
                        mirroredDifferenceHash = differenceFaceHash(
                            maskedFrame,
                            descriptorRect,
                            mirror = true
                        ),
                        appearanceHistogram = faceAppearanceHistogram(
                            maskedFrame,
                            descriptorRect
                        ),
                        originalBytes = null,
                        originalBitmap = null,
                        originalWidth = frame.width,
                        originalHeight = frame.height,
                        uploadBytes = uploadBytes,
                        uploadWidth = maskedFrame.width,
                        uploadHeight = maskedFrame.height,
                        localFaceRect = localFaceRect,
                        sourceCropRect = FaceRect(
                            0f,
                            0f,
                            maskedFrame.width.toFloat(),
                            maskedFrame.height.toFloat()
                        ),
                        faceAreaRatio = observation.regionAreaRatio,
                        faceCenterX = observation.regionCenterX,
                        faceCenterY = observation.regionCenterY,
                        yaw = 0f,
                        roll = 0f,
                        trackingId = null,
                        isRescueFrame = true,
                        rescueSourceDetectedFaceRects = observation.detectedFaceRects,
                        rescueRegionRect = observation.regionRect
                    )
                } finally {
                    if (maskedFrame !== frame) {
                        maskedFrame.recycle()
                    }
                }
            } finally {
                frame.recycle()
            }
        }

        recordDiagnostic(
            "视频云端救援人物筛选: observations=${observations.size}, eligible=${eligible.size}, " +
                "coveredByLocal=${observations.count { isRescueObservationCoveredByLocalPerson(it, localCandidates) }}, " +
                "persons=${clusters.size}, selected=${rescueCandidates.size}, " +
                "times=${selectedObservations.joinToString { observation ->
                    "${observation.frameTimeMs}ms/skin=${"%.3f".format(Locale.ROOT, observation.skinRatio)}/" +
                        "faces=${observation.localFaceCount}/masked=${observation.knownFaceRects.size}/" +
                        "unmasked=${observation.unmaskedDetectedFaceCount}/" +
                        "priority=${videoRescueObservationPriority(observation)}/" +
                        "region=${observation.regionRect?.let {
                            "%.2f,%.2f,%.2f,%.2f".format(
                                Locale.ROOT,
                                it.x,
                                it.y,
                                it.width,
                                it.height
                            )
                        }}"
                }}"
        )
        return rescueCandidates
    }

    private fun videoRescueObservationPriority(
        observation: VideoRescueObservation
    ): Int {
        return when {
            observation.unmaskedDetectedFaceCount > 0 -> 3
            observation.localFaceCount > 0 -> 2
            else -> 1
        }
    }

    private fun analyzeVideoRescueRegion(
        bitmap: Bitmap,
        knownFaceRects: List<FaceRect>
    ): VideoRescueRegionAnalysis {
        val sample = resizeBitmapToMaxSide(bitmap, VIDEO_RESCUE_SKIN_SAMPLE_SIDE)
        val width = sample.width
        val height = sample.height
        if (width <= 0 || height <= 0) {
            return VideoRescueRegionAnalysis()
        }
        val pixels = IntArray(width * height)
        sample.getPixels(pixels, 0, width, 0, 0, width, height)
        val excludedFaceRects = knownFaceRects.map {
            expandedNormalizedFaceRect(it, VIDEO_RESCUE_FACE_MASK_PADDING)
        }
        val skinMask = BooleanArray(pixels.size)
        for (y in 0 until height) {
            for (x in 0 until width) {
                val normalizedX = x.toFloat() / width.toFloat()
                val normalizedY = y.toFloat() / height.toFloat()
                val excluded = excludedFaceRects.any { rect ->
                    normalizedX >= rect.x &&
                        normalizedX <= rect.x + rect.width &&
                        normalizedY >= rect.y &&
                        normalizedY <= rect.y + rect.height
                }
                if (!excluded && isLikelySkinColor(pixels[y * width + x])) {
                    skinMask[y * width + x] = true
                }
            }
        }

        val visited = BooleanArray(skinMask.size)
        val queue = IntArray(skinMask.size)
        var bestCount = 0
        var bestMinX = width
        var bestMinY = height
        var bestMaxX = -1
        var bestMaxY = -1
        for (startIndex in skinMask.indices) {
            if (!skinMask[startIndex] || visited[startIndex]) {
                continue
            }
            var head = 0
            var tail = 0
            queue[tail++] = startIndex
            visited[startIndex] = true
            var componentCount = 0
            var minX = width
            var minY = height
            var maxX = -1
            var maxY = -1
            while (head < tail) {
                val index = queue[head++]
                val x = index % width
                val y = index / width
                componentCount += 1
                minX = minOf(minX, x)
                minY = minOf(minY, y)
                maxX = maxOf(maxX, x)
                maxY = maxOf(maxY, y)
                val left = index - 1
                val right = index + 1
                val top = index - width
                val bottom = index + width
                if (x > 0 && skinMask[left] && !visited[left]) {
                    visited[left] = true
                    queue[tail++] = left
                }
                if (x + 1 < width && skinMask[right] && !visited[right]) {
                    visited[right] = true
                    queue[tail++] = right
                }
                if (y > 0 && skinMask[top] && !visited[top]) {
                    visited[top] = true
                    queue[tail++] = top
                }
                if (y + 1 < height && skinMask[bottom] && !visited[bottom]) {
                    visited[bottom] = true
                    queue[tail++] = bottom
                }
            }
            if (componentCount > bestCount) {
                bestCount = componentCount
                bestMinX = minX
                bestMinY = minY
                bestMaxX = maxX
                bestMaxY = maxY
            }
        }

        val skinRatio = bestCount.toFloat() / pixels.size.coerceAtLeast(1).toFloat()
        val regionRect = if (bestCount > 0 && bestMaxX >= bestMinX && bestMaxY >= bestMinY) {
            FaceRect(
                x = bestMinX.toFloat() / width.toFloat(),
                y = bestMinY.toFloat() / height.toFloat(),
                width = (bestMaxX - bestMinX + 1).toFloat() / width.toFloat(),
                height = (bestMaxY - bestMinY + 1).toFloat() / height.toFloat()
            )
        } else {
            null
        }
        val regionHash = regionRect
            ?.toPixelRect(width, height)
            ?.let { averageFaceHash(sample, it) }
            ?: 0L
        if (sample !== bitmap) {
            sample.recycle()
        }
        return VideoRescueRegionAnalysis(
            skinRatio = skinRatio,
            regionHash = regionHash,
            regionRect = regionRect,
            regionCenterX = regionRect?.let { it.x + it.width / 2f } ?: 0.5f,
            regionCenterY = regionRect?.let { it.y + it.height / 2f } ?: 0.5f,
            regionAreaRatio = regionRect?.let { it.width * it.height } ?: 0f
        )
    }

    private fun isLikelySkinColor(color: Int): Boolean {
        val red = Color.red(color)
        val green = Color.green(color)
        val blue = Color.blue(color)
        val maxChannel = maxOf(red, green, blue)
        val minChannel = minOf(red, green, blue)
        return red > 95 && green > 40 && blue > 20 &&
            maxChannel - minChannel > 15 &&
            abs(red - green) > 15 &&
            red > green &&
            red > blue
    }

    private fun expandedNormalizedFaceRect(rect: FaceRect, paddingRatio: Float): FaceRect {
        val padX = rect.width * paddingRatio
        val padY = rect.height * paddingRatio
        val left = (rect.x - padX).coerceIn(0f, 1f)
        val top = (rect.y - padY).coerceIn(0f, 1f)
        val right = (rect.x + rect.width + padX).coerceIn(0f, 1f)
        val bottom = (rect.y + rect.height + padY).coerceIn(0f, 1f)
        return FaceRect(left, top, right - left, bottom - top)
    }

    private fun maskKnownFacesForVideoRescue(
        bitmap: Bitmap,
        knownFaceRects: List<FaceRect>
    ): Bitmap {
        if (knownFaceRects.isEmpty()) {
            return bitmap
        }
        val mutableBitmap = bitmap.copy(Bitmap.Config.ARGB_8888, true)
        val canvas = Canvas(mutableBitmap)
        val paint = Paint().apply {
            color = Color.BLACK
            style = Paint.Style.FILL
        }
        knownFaceRects.forEach { rect ->
            expandedNormalizedFaceRect(rect, VIDEO_RESCUE_FACE_MASK_PADDING)
                .toPixelRect(mutableBitmap.width, mutableBitmap.height)
                ?.let { canvas.drawRect(it, paint) }
        }
        return mutableBitmap
    }

    private fun mergeVideoLocalAndRescueCandidates(
        localCandidates: List<VideoFaceCandidate>,
        rescueCandidates: List<VideoFaceCandidate>
    ): List<VideoFaceCandidate> {
        val merged = localCandidates.toMutableList()
        var replaced = 0
        var skipped = 0
        rescueCandidates.sortedByDescending { it.qualityScore }.forEach { rescue ->
            val localIndex = merged.indexOfFirst { local ->
                !local.isRescueFrame && sameVideoLocalAndRescuePerson(local, rescue)
            }
            if (localIndex < 0) {
                merged.add(rescue)
                return@forEach
            }
            val local = merged[localIndex]
            val shouldUseRescue = abs(local.yaw) >= VIDEO_RESCUE_REPLACE_MIN_YAW &&
                local.qualityScore < VIDEO_RESCUE_REPLACE_MAX_LOCAL_QUALITY
            if (shouldUseRescue) {
                merged[localIndex] = rescue
                replaced += 1
                recordDiagnostic(
                    "视频救援候选替换本地侧脸: local=${local.frameTimeMs}ms/" +
                        "q=${local.qualityScore}/yaw=${local.yaw.roundToInt()}, " +
                        "rescue=${rescue.frameTimeMs}ms/q=${rescue.qualityScore}"
                )
            } else {
                skipped += 1
                recordDiagnostic(
                    "视频救援候选与本地人物重复，保留本地: local=${local.frameTimeMs}ms/" +
                        "q=${local.qualityScore}, rescue=${rescue.frameTimeMs}ms/q=${rescue.qualityScore}"
                )
            }
        }
        recordDiagnostic(
            "视频本地与救援候选合并: local=${localCandidates.size}, rescue=${rescueCandidates.size}, " +
                "replaced=$replaced, skipped=$skipped, result=${merged.size}"
        )
        return merged.sortedByDescending { it.qualityScore }
    }

    private fun sameVideoLocalAndRescuePerson(
        local: VideoFaceCandidate,
        rescue: VideoFaceCandidate
    ): Boolean {
        if (sameVideoTrackAndRescueSourceFace(local, rescue)) {
            return true
        }
        if (local.personTrackSignatures.any { signature ->
                sameVideoSignatureAndCandidate(signature, rescue)
            }
        ) {
            return true
        }
        val timeGapMs = abs(local.frameTimeMs - rescue.frameTimeMs)
        if (timeGapMs > VIDEO_RESCUE_LOCAL_COVERAGE_GAP_MS) {
            return false
        }
        val dx = local.faceCenterX - rescue.faceCenterX
        val dy = local.faceCenterY - rescue.faceCenterY
        val centerDistance = kotlin.math.sqrt(dx * dx + dy * dy)
        val sizeRatio = videoCandidateSizeRatio(local.faceAreaRatio, rescue.faceAreaRatio)
        val dHashDistance = minOf(
            hammingDistance(local.differenceHash, rescue.differenceHash),
            hammingDistance(local.differenceHash, rescue.mirroredDifferenceHash),
            hammingDistance(local.mirroredDifferenceHash, rescue.differenceHash)
        )
        return (
            centerDistance <= VIDEO_RESCUE_LOCAL_MAX_CENTER_DISTANCE &&
                sizeRatio <= VIDEO_RESCUE_LOCAL_MAX_SIZE_RATIO
            ) || (
            timeGapMs <= VIDEO_RESCUE_SIDE_REPLACEMENT_GAP_MS &&
                abs(local.yaw) >= VIDEO_RESCUE_REPLACE_MIN_YAW &&
                dHashDistance <= VIDEO_RESCUE_LOCAL_MAX_DHASH_DISTANCE
            )
    }

    private fun sameVideoTrackAndRescueSourceFace(
        local: VideoFaceCandidate,
        rescue: VideoFaceCandidate
    ): Boolean {
        val rescueRegion = rescue.rescueRegionRect ?: return false
        if (rescue.rescueSourceDetectedFaceRects.isEmpty()) {
            return false
        }
        return local.personTrackSignatures.any { signature ->
            val timeGapMs = abs(signature.frameTimeMs - rescue.frameTimeMs)
            if (timeGapMs > VIDEO_RESCUE_SOURCE_TRACK_GAP_MS) {
                return@any false
            }
            rescue.rescueSourceDetectedFaceRects.any { sourceFaceRect ->
                val sourceCenterX = sourceFaceRect.x + sourceFaceRect.width / 2f
                val sourceCenterY = sourceFaceRect.y + sourceFaceRect.height / 2f
                val trackDx = signature.faceCenterX - sourceCenterX
                val trackDy = signature.faceCenterY - sourceCenterY
                val trackCenterDistance = kotlin.math.sqrt(
                    trackDx * trackDx + trackDy * trackDy
                )
                val trackSizeRatio = videoCandidateSizeRatio(
                    signature.faceAreaRatio,
                    sourceFaceRect.width * sourceFaceRect.height
                )
                val rescueNearSourceFace = normalizedRectGap(
                    rescueRegion,
                    expandedNormalizedFaceRect(
                        sourceFaceRect,
                        VIDEO_RESCUE_SOURCE_PROXIMITY_PADDING
                    )
                ) <= VIDEO_RESCUE_SOURCE_MAX_REGION_GAP
                trackCenterDistance <= VIDEO_RESCUE_SOURCE_MAX_TRACK_DISTANCE &&
                    trackSizeRatio <= VIDEO_RESCUE_SOURCE_MAX_SIZE_RATIO &&
                    rescueNearSourceFace
            }
        }
    }

    private fun normalizedRectGap(left: FaceRect, right: FaceRect): Float {
        val leftRight = left.x + left.width
        val leftBottom = left.y + left.height
        val rightRight = right.x + right.width
        val rightBottom = right.y + right.height
        val horizontalGap = when {
            leftRight < right.x -> right.x - leftRight
            rightRight < left.x -> left.x - rightRight
            else -> 0f
        }
        val verticalGap = when {
            leftBottom < right.y -> right.y - leftBottom
            rightBottom < left.y -> left.y - rightBottom
            else -> 0f
        }
        return kotlin.math.sqrt(
            horizontalGap * horizontalGap + verticalGap * verticalGap
        )
    }

    private fun sameVideoSignatureAndCandidate(
        signature: VideoPersonSignature,
        candidate: VideoFaceCandidate
    ): Boolean {
        val timeGapMs = abs(signature.frameTimeMs - candidate.frameTimeMs)
        if (timeGapMs > VIDEO_RESCUE_TRACK_SIGNATURE_GAP_MS) {
            return false
        }
        val dx = signature.faceCenterX - candidate.faceCenterX
        val dy = signature.faceCenterY - candidate.faceCenterY
        val centerDistance = kotlin.math.sqrt(dx * dx + dy * dy)
        val sizeRatio = videoCandidateSizeRatio(
            signature.faceAreaRatio,
            candidate.faceAreaRatio
        )
        val dHashDistance = minOf(
            hammingDistance(signature.differenceHash, candidate.differenceHash),
            hammingDistance(
                signature.differenceHash,
                candidate.mirroredDifferenceHash
            ),
            hammingDistance(
                signature.mirroredDifferenceHash,
                candidate.differenceHash
            )
        )
        val histogramSimilarity = histogramCosineSimilarity(
            signature.appearanceHistogram,
            candidate.appearanceHistogram
        )
        return centerDistance <= VIDEO_RESCUE_TRACK_MAX_CENTER_DISTANCE &&
            sizeRatio <= VIDEO_RESCUE_TRACK_MAX_SIZE_RATIO &&
            (
                dHashDistance <= VIDEO_RESCUE_TRACK_MAX_DHASH_DISTANCE ||
                    histogramSimilarity >= VIDEO_RESCUE_TRACK_MIN_HISTOGRAM_SIMILARITY
                )
    }

    private fun isRescueObservationCoveredByLocalPerson(
        observation: VideoRescueObservation,
        localCandidates: List<VideoFaceCandidate>
    ): Boolean {
        return localCandidates.any { local ->
            val timeGapMs = abs(local.frameTimeMs - observation.frameTimeMs)
            if (timeGapMs > VIDEO_RESCUE_LOCAL_COVERAGE_GAP_MS) {
                return@any false
            }
            val dx = local.faceCenterX - observation.regionCenterX
            val dy = local.faceCenterY - observation.regionCenterY
            val centerDistance = kotlin.math.sqrt(dx * dx + dy * dy)
            centerDistance <= VIDEO_RESCUE_LOCAL_MAX_CENTER_DISTANCE &&
                videoCandidateSizeRatio(local.faceAreaRatio, observation.regionAreaRatio) <=
                VIDEO_RESCUE_LOCAL_MAX_SIZE_RATIO
        }
    }

    private fun videoRescuePersonMatchScore(
        left: VideoRescueObservation,
        right: VideoRescueObservation
    ): Int {
        val hashDistance = hammingDistance(left.regionHash, right.regionHash)
        val timeGapMs = abs(left.frameTimeMs - right.frameTimeMs)
        if (timeGapMs > VIDEO_RESCUE_CLUSTER_MAX_GAP_MS) {
            return Int.MIN_VALUE
        }
        if (hashDistance <= VIDEO_RESCUE_STRONG_HASH_DISTANCE) {
            return 90 - hashDistance
        }
        val dx = left.regionCenterX - right.regionCenterX
        val dy = left.regionCenterY - right.regionCenterY
        val centerDistance = kotlin.math.sqrt(dx * dx + dy * dy)
        val sizeRatio = videoCandidateSizeRatio(left.regionAreaRatio, right.regionAreaRatio)
        if (timeGapMs <= VIDEO_RESCUE_CONTINUITY_GAP_MS &&
            centerDistance <= VIDEO_RESCUE_MAX_CENTER_DISTANCE &&
            sizeRatio <= VIDEO_RESCUE_MAX_SIZE_RATIO
        ) {
            return 60 +
                (VIDEO_RESCUE_RELAXED_HASH_DISTANCE - hashDistance).coerceAtLeast(0)
        }
        if (timeGapMs <= VIDEO_RESCUE_CONTINUITY_GAP_MS &&
            hashDistance <= VIDEO_RESCUE_RELAXED_HASH_DISTANCE &&
            centerDistance <= VIDEO_RESCUE_RELAXED_CENTER_DISTANCE &&
            sizeRatio <= VIDEO_RESCUE_MAX_SIZE_RATIO
        ) {
            return 48 + (VIDEO_RESCUE_RELAXED_HASH_DISTANCE - hashDistance)
        }
        return Int.MIN_VALUE
    }

    private fun extractVideoFrame(
        retriever: MediaMetadataRetriever,
        timeMs: Long,
        precise: Boolean = true,
        maxSide: Int = -1
    ): Bitmap? {

        val option = if (precise) {
            MediaMetadataRetriever.OPTION_CLOSEST
        } else {
            MediaMetadataRetriever.OPTION_CLOSEST_SYNC
        }

        return try {
            if (maxSide > 0) {
                val widthStr = retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_VIDEO_WIDTH)
                val heightStr = retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_VIDEO_HEIGHT)
                val w = widthStr?.toIntOrNull() ?: -1
                val h = heightStr?.toIntOrNull() ?: -1
                if (w > 0 && h > 0) {
                    val currentMax = maxOf(w, h)
                    val scale = maxSide.toFloat() / currentMax.toFloat()
                    if (scale < 1.0f) {
                        val dstW = Math.max(1, (w * scale).toInt())
                        val dstH = Math.max(1, (h * scale).toInt())
                        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O_MR1) {
                            return retriever.getScaledFrameAtTime(timeMs * 1000L, option, dstW, dstH)
                        }
                    }
                }
            }
            retriever.getFrameAtTime(timeMs * 1000L, option)
        } catch (e: Exception) {
            recordDiagnostic("视频取帧异常: timeMs=$timeMs, precise=$precise, maxSide=$maxSide", e)
            null
        }
    }

    private fun buildVideoFaceCandidate(

        video: GalleryVideo,

        frame: Bitmap,

        detectionBitmap: Bitmap,

        face: Face,

        frameTimeMs: Long

    ): VideoFaceCandidate? {

        val faceRectOnDetection = clippedRect(face.boundingBox, detectionBitmap.width, detectionBitmap.height)

        if (faceRectOnDetection == null) {

            recordDiagnostic("视频候选被拒: clippedRect为null, trackingId=${face.trackingId}")

            return null

        }

            

        // 过滤在检测分辨率（最大边 960）下宽度或高度小于 100 像素的人脸，防止超小模糊脸干扰打分并上传云端

        if (faceRectOnDetection.width() < 35 || faceRectOnDetection.height() < 35) {

            recordDiagnostic("视频候选被拒: 尺寸过小 (${faceRectOnDetection.width()}x${faceRectOnDetection.height()}), trackingId=${face.trackingId}")

            return null

        }

        // 仅过滤接近背脸或严重俯仰的候选；清晰侧脸保留给云端继续判断。

        if (abs(face.headEulerAngleY) > VIDEO_MAX_CANDIDATE_YAW ||
            abs(face.headEulerAngleX) > VIDEO_MAX_CANDIDATE_PITCH
        ) {

            recordDiagnostic("视频候选被拒: 姿态角过大 (yaw=${face.headEulerAngleY}, pitch=${face.headEulerAngleX}), trackingId=${face.trackingId}")

            return null

        }

        val faceAreaRatio = faceRectOnDetection.width().toFloat() * faceRectOnDetection.height().toFloat() /

            (detectionBitmap.width.toFloat() * detectionBitmap.height.toFloat()).coerceAtLeast(1f)
        val faceCenterX = faceRectOnDetection.centerX().toFloat() / detectionBitmap.width.toFloat()
        val faceCenterY = faceRectOnDetection.centerY().toFloat() / detectionBitmap.height.toFloat()

        if (faceAreaRatio < VIDEO_MIN_FACE_AREA_RATIO) {

            recordDiagnostic("视频候选被拒: 面积比例过小 (ratio=$faceAreaRatio < $VIDEO_MIN_FACE_AREA_RATIO), trackingId=${face.trackingId}")

            return null

        }

        val scaleX = frame.width.toFloat() / detectionBitmap.width.toFloat()

        val scaleY = frame.height.toFloat() / detectionBitmap.height.toFloat()

        val faceRectOnFrame = Rect(

            (faceRectOnDetection.left * scaleX).roundToInt().coerceIn(0, frame.width),

            (faceRectOnDetection.top * scaleY).roundToInt().coerceIn(0, frame.height),

            (faceRectOnDetection.right * scaleX).roundToInt().coerceIn(0, frame.width),

            (faceRectOnDetection.bottom * scaleY).roundToInt().coerceIn(0, frame.height)

        )

        if (faceRectOnFrame.width() <= 0 || faceRectOnFrame.height() <= 0) {

            recordDiagnostic("视频候选被拒: 映射到原图后的宽度或高度为0, trackingId=${face.trackingId}")

            return null

        }

        val uploadImage = buildSingleFaceUploadImageFromRect(frame, faceRectOnFrame, VIDEO_MAX_UPLOAD_IMAGE_SIDE)

        val uploadBytes = bitmapToJpegBytes(uploadImage.bitmap, FACE_UPLOAD_JPEG_QUALITY)

        val uploadWidth = uploadImage.bitmap.width

        val uploadHeight = uploadImage.bitmap.height

        val quality = scoreVideoFaceCandidate(frame, face, faceRectOnFrame)

        val hash = averageFaceHash(frame, faceRectOnFrame)
        val differenceHash = differenceFaceHash(frame, faceRectOnFrame, mirror = false)
        val mirroredDifferenceHash = differenceFaceHash(frame, faceRectOnFrame, mirror = true)
        val appearanceHistogram = faceAppearanceHistogram(frame, faceRectOnFrame)

        val localRect = uploadImage.localFaceRects.firstOrNull() ?: FaceRect(

            0f,

            0f,

            uploadWidth.toFloat(),

            uploadHeight.toFloat()

        )

        recordDiagnostic(

            "视频候选人脸: video=${video.displayName}, timeMs=$frameTimeMs, trackingId=${face.trackingId}, quality=$quality, " +

                "areaRatio=$faceAreaRatio, yaw=${face.headEulerAngleY}, roll=${face.headEulerAngleZ}, " +

                "upload=${uploadWidth}x${uploadHeight}, bytes=${uploadBytes.size}"

        )

        // 显式回收本地生成的上传用临时小图，避免内存累积

        try {

            uploadImage.bitmap.recycle()

        } catch (e: Exception) {}

        return VideoFaceCandidate(

            frameTimeMs = frameTimeMs,

            qualityScore = quality,

            faceHash = hash,

            differenceHash = differenceHash,

            mirroredDifferenceHash = mirroredDifferenceHash,

            appearanceHistogram = appearanceHistogram,

            originalBytes = null,

            originalBitmap = null, // 延迟到去重筛选后再从 retriever 取帧编码，避免同时驻留大量全帧 Bitmap

            originalWidth = frame.width,
            originalHeight = frame.height,

            uploadBytes = uploadBytes,

            uploadWidth = uploadWidth,

            uploadHeight = uploadHeight,

            localFaceRect = localRect,

            sourceCropRect = faceRectFromPixelRect(uploadImage.sourceCropRect),

            faceAreaRatio = faceAreaRatio,

            faceCenterX = faceCenterX,

            faceCenterY = faceCenterY,

            yaw = face.headEulerAngleY,

            roll = face.headEulerAngleZ,

            trackingId = face.trackingId

        )

    }

    private fun buildSingleFaceUploadImageFromRect(

        sourceBitmap: Bitmap,

        faceRect: Rect,

        maxUploadSide: Int

    ): FaceUploadImage {

        val padX = (faceRect.width() * FACE_CROP_HORIZONTAL_PADDING).toInt()

        val padTop = (faceRect.height() * FACE_CROP_TOP_PADDING).toInt()

        val padBottom = (faceRect.height() * FACE_CROP_BOTTOM_PADDING).toInt()

        val cropRect = expandRectToMinimumSide(

            Rect(

                (faceRect.left - padX).coerceAtLeast(0),

                (faceRect.top - padTop).coerceAtLeast(0),

                (faceRect.right + padX).coerceAtMost(sourceBitmap.width),

                (faceRect.bottom + padBottom).coerceAtMost(sourceBitmap.height)

            ),

            sourceBitmap.width,

            sourceBitmap.height,

            0

        )

        val cropped = Bitmap.createBitmap(sourceBitmap, cropRect.left, cropRect.top, cropRect.width(), cropRect.height())

        val uploadBitmap = resizeBitmapForUpload(cropped, maxUploadSide)

        val scaleX = uploadBitmap.width.toFloat() / cropRect.width().toFloat()

        val scaleY = uploadBitmap.height.toFloat() / cropRect.height().toFloat()

        val localRect = mapLocalFaceToUploadRect(faceRect, cropRect, scaleX, scaleY, uploadBitmap.width, uploadBitmap.height)

        return FaceUploadImage(uploadBitmap, cropRect, listOfNotNull(localRect))

    }

    private fun buildRealtimeFaceUploadImageFromRect(
        sourceBitmap: Bitmap,
        faceRect: Rect,
        maxUploadSide: Int,
        wideRetry: Boolean = false
    ): FaceUploadImage {
        val horizontalPadding = if (wideRetry) {
            REALTIME_RETRY_FACE_CROP_HORIZONTAL_PADDING
        } else {
            REALTIME_FACE_CROP_HORIZONTAL_PADDING
        }
        val topPadding = if (wideRetry) {
            REALTIME_RETRY_FACE_CROP_TOP_PADDING
        } else {
            REALTIME_FACE_CROP_TOP_PADDING
        }
        val bottomPadding = if (wideRetry) {
            REALTIME_RETRY_FACE_CROP_BOTTOM_PADDING
        } else {
            REALTIME_FACE_CROP_BOTTOM_PADDING
        }
        val minSide = if (wideRetry) {
            REALTIME_RETRY_UPLOAD_MIN_SIDE
        } else {
            REALTIME_UPLOAD_MIN_SIDE
        }
        val padX = (faceRect.width() * horizontalPadding).roundToInt()
        val padTop = (faceRect.height() * topPadding).roundToInt()
        val padBottom = (faceRect.height() * bottomPadding).roundToInt()
        val cropRect = expandRectToMinimumSide(
            Rect(
                (faceRect.left - padX).coerceAtLeast(0),
                (faceRect.top - padTop).coerceAtLeast(0),
                (faceRect.right + padX).coerceAtMost(sourceBitmap.width),
                (faceRect.bottom + padBottom).coerceAtMost(sourceBitmap.height)
            ),
            sourceBitmap.width,
            sourceBitmap.height,
            minSide
        )
        val cropped = Bitmap.createBitmap(sourceBitmap, cropRect.left, cropRect.top, cropRect.width(), cropRect.height())
        val uploadBitmap = resizeBitmapForUpload(cropped, maxUploadSide)
        if (uploadBitmap !== cropped) {
            try {
                cropped.recycle()
            } catch (_: Exception) {
            }
        }
        val scaleX = uploadBitmap.width.toFloat() / cropRect.width().toFloat()
        val scaleY = uploadBitmap.height.toFloat() / cropRect.height().toFloat()
        val localRect = mapLocalFaceToUploadRect(faceRect, cropRect, scaleX, scaleY, uploadBitmap.width, uploadBitmap.height)
        return FaceUploadImage(uploadBitmap, cropRect, listOfNotNull(localRect))
    }

    private fun scoreRealtimeFaceCandidate(bitmap: Bitmap, face: Face, faceRect: Rect): RealtimeFaceScore {
        val sharpness = estimateFaceSharpness(bitmap, faceRect).coerceIn(0, 8000)
        val faceArea = faceRect.width().toLong() * faceRect.height().toLong()
        val frameArea = (bitmap.width.toLong() * bitmap.height.toLong()).coerceAtLeast(1L)
        val faceAreaRatio = faceArea.toFloat() / frameArea.toFloat()
        val areaBonus = ((faceAreaRatio / REALTIME_FACE_AREA_BONUS_FULL_RATIO) *
            REALTIME_FACE_AREA_BONUS_MAX
        ).roundToInt().coerceIn(0, REALTIME_FACE_AREA_BONUS_MAX)

        val yawPenalty = if (abs(face.headEulerAngleY) > VIDEO_YAW_FREE_ANGLE) {
            ((abs(face.headEulerAngleY) - VIDEO_YAW_FREE_ANGLE) * VIDEO_YAW_PENALTY_PER_DEGREE).roundToInt()
        } else 0
        val rollPenalty = if (abs(face.headEulerAngleZ) > 12f) {
            ((abs(face.headEulerAngleZ) - 12f) * 20f).roundToInt()
        } else 0
        val pitchPenalty = if (abs(face.headEulerAngleX) > 12f) {
            ((abs(face.headEulerAngleX) - 12f) * 30f).roundToInt()
        } else 0
        val centerX = faceRect.centerX().toFloat() / bitmap.width.toFloat()
        val centerY = faceRect.centerY().toFloat() / bitmap.height.toFloat()
        val centerPenalty = ((abs(centerX - 0.5f) + abs(centerY - 0.48f)) * 400f).roundToInt()
        val qualityScore = (sharpness - yawPenalty - rollPenalty - pitchPenalty - centerPenalty).coerceAtLeast(0)
        val dispatchScore = (qualityScore + areaBonus).coerceAtLeast(0)
        return RealtimeFaceScore(
            qualityScore = qualityScore,
            dispatchScore = dispatchScore,
            sharpnessScore = sharpness,
            areaBonus = areaBonus
        )
    }

    private fun scoreVideoFaceCandidate(bitmap: Bitmap, face: Face, faceRect: Rect): Int {

        // 1. 基础分为归一化后的五官核心区清晰度（范围 0 ~ 8000）

        val sharpness = estimateFaceSharpness(bitmap, faceRect).coerceIn(0, 8000)

        

        // 2. 面积奖励分：鼓励人脸在画面中足够大（离镜头越近识别度越高），最高加 3000 分

        val faceArea = faceRect.width().toLong() * faceRect.height().toLong()

        val areaBonus = (faceArea * 3000L / (bitmap.width.toLong() * bitmap.height.toLong()).coerceAtLeast(1L)).toInt().coerceIn(0, 3000)

        

        // 3. 姿态角（Yaw, Roll, Pitch）非线性惩罚扣分：

        // 只要偏角在合理范围内不扣分（Yaw在15度内，Roll在12度内，Pitch在12度内），超过该范围则线性惩罚扣分，防止因为正脸让模糊晃动脸胜出

        val yawPenalty = if (abs(face.headEulerAngleY) > VIDEO_YAW_FREE_ANGLE) {

            ((abs(face.headEulerAngleY) - VIDEO_YAW_FREE_ANGLE) * VIDEO_YAW_PENALTY_PER_DEGREE).roundToInt()

        } else 0

        

        val rollPenalty = if (abs(face.headEulerAngleZ) > 12f) {

            ((abs(face.headEulerAngleZ) - 12f) * 20f).roundToInt()

        } else 0

        val pitchPenalty = if (abs(face.headEulerAngleX) > 12f) {

            ((abs(face.headEulerAngleX) - 12f) * 30f).roundToInt()

        } else 0

        

        // 4. 中心位置惩罚扣分：越靠近画面正中心（或微偏上）惩罚越小

        val centerX = faceRect.centerX().toFloat() / bitmap.width.toFloat()

        val centerY = faceRect.centerY().toFloat() / bitmap.height.toFloat()

        val centerPenalty = ((abs(centerX - 0.5f) + abs(centerY - 0.48f)) * 400f).roundToInt()

        

        // 最终质量分 = 清晰度分 + 面积奖励 - 姿态角惩罚 - 中心位置惩罚

        val score = sharpness + areaBonus - yawPenalty - rollPenalty - pitchPenalty - centerPenalty

        return score.coerceAtLeast(0)

    }

    

    private fun estimateFaceSharpness(bitmap: Bitmap, rect: Rect): Int {

        val width = rect.width()

        val height = rect.height()

        if (width < 10 || height < 10) return 0

        

        // 1. 裁剪人脸核心五官区域（中心 60% 宽度和 60% 高度），避开额头头发、耳朵以及外部衣领/背景的高对比度纹理噪点

        val coreLeft = rect.left + (width * 0.2f).toInt()

        val coreTop = rect.top + (height * 0.2f).toInt()

        val coreRight = rect.right - (width * 0.2f).toInt()

        val coreBottom = rect.bottom - (height * 0.2f).toInt()

        val coreRect = clippedRect(Rect(coreLeft, coreTop, coreRight, coreBottom), bitmap.width, bitmap.height) ?: return 0

        // 2. 限制五官核心区大图的最大边为 120 像素，避免过大分辨率或小分辨率带来的特征梯度失真，实现公平打分

        val coreWidth = coreRect.width()

        val coreHeight = coreRect.height()

        val scale = minOf(1f, REALTIME_SHARPNESS_SAMPLE_MAX_SIDE.toFloat() / maxOf(coreWidth, coreHeight).toFloat())

        val sWidth = (coreWidth * scale).roundToInt().coerceAtLeast(1)

        val sHeight = (coreHeight * scale).roundToInt().coerceAtLeast(1)

        if (sWidth < 3 || sHeight < 3) {

            return 0

        }

        

        val pixels = IntArray(sWidth * sHeight)

        for (sampleY in 0 until sHeight) {

            val sourceY = (coreRect.top + ((sampleY + 0.5f) * coreHeight / sHeight).toInt())
                .coerceIn(coreRect.top, coreRect.bottom - 1)

            for (sampleX in 0 until sWidth) {

                val sourceX = (coreRect.left + ((sampleX + 0.5f) * coreWidth / sWidth).toInt())
                    .coerceIn(coreRect.left, coreRect.right - 1)

                pixels[sampleY * sWidth + sampleX] = bitmap.getPixel(sourceX, sourceY)

            }

        }

        var gradientSum = 0L

        var count = 0

        for (y in 1 until sHeight) {

            for (x in 1 until sWidth) {

                val current = luminance(pixels[y * sWidth + x])

                val left = luminance(pixels[y * sWidth + x - 1])

                val top = luminance(pixels[(y - 1) * sWidth + x])

                gradientSum += abs(current - left) + abs(current - top)

                count += 2

            }

        }

        // 归一化平均差值，乘以 120 放大映射到 0~8000 区间，更保真地反映出五官对焦清晰度与防晃动程度

        val avgGradient = if (count == 0) 0f else (gradientSum.toFloat() / count.toFloat())

        return (avgGradient * 120f).roundToInt()

    }

    private fun averageFaceHash(bitmap: Bitmap, rect: Rect): Long {

        val cropRect = expandRectToMinimumSide(

            rect,

            bitmap.width,

            bitmap.height,

            maxOf(rect.width(), rect.height()).coerceAtLeast(1)

        )

        val crop = Bitmap.createBitmap(bitmap, cropRect.left, cropRect.top, cropRect.width(), cropRect.height())

        val small = Bitmap.createScaledBitmap(crop, VIDEO_HASH_SIZE, VIDEO_HASH_SIZE, true)

        val pixels = IntArray(VIDEO_HASH_SIZE * VIDEO_HASH_SIZE)

        small.getPixels(pixels, 0, VIDEO_HASH_SIZE, 0, 0, VIDEO_HASH_SIZE, VIDEO_HASH_SIZE)

        val values = pixels.map { luminance(it) }

        val average = values.sum() / values.size.coerceAtLeast(1)

        var hash = 0L

        values.forEachIndexed { index, value ->

            if (value >= average) {

                hash = hash or (1L shl index)

            }

        }

        if (small !== crop) {
            small.recycle()
        }
        if (crop !== bitmap) {
            crop.recycle()
        }

        return hash

    }

    private fun differenceFaceHash(
        bitmap: Bitmap,
        rect: Rect,
        mirror: Boolean
    ): Long {
        val cropRect = expandRectToMinimumSide(
            rect,
            bitmap.width,
            bitmap.height,
            maxOf(rect.width(), rect.height()).coerceAtLeast(1)
        )
        val crop = Bitmap.createBitmap(
            bitmap,
            cropRect.left,
            cropRect.top,
            cropRect.width(),
            cropRect.height()
        )
        val normalized = if (mirror) {
            val matrix = Matrix().apply { preScale(-1f, 1f) }
            Bitmap.createBitmap(crop, 0, 0, crop.width, crop.height, matrix, true)
        } else {
            crop
        }
        val small = Bitmap.createScaledBitmap(
            normalized,
            VIDEO_DHASH_WIDTH + 1,
            VIDEO_DHASH_HEIGHT,
            true
        )
        val pixels = IntArray((VIDEO_DHASH_WIDTH + 1) * VIDEO_DHASH_HEIGHT)
        small.getPixels(
            pixels,
            0,
            VIDEO_DHASH_WIDTH + 1,
            0,
            0,
            VIDEO_DHASH_WIDTH + 1,
            VIDEO_DHASH_HEIGHT
        )
        var hash = 0L
        var bitIndex = 0
        for (y in 0 until VIDEO_DHASH_HEIGHT) {
            for (x in 0 until VIDEO_DHASH_WIDTH) {
                val rowStart = y * (VIDEO_DHASH_WIDTH + 1)
                if (luminance(pixels[rowStart + x]) >=
                    luminance(pixels[rowStart + x + 1])
                ) {
                    hash = hash or (1L shl bitIndex)
                }
                bitIndex += 1
            }
        }
        if (small !== normalized) {
            small.recycle()
        }
        if (normalized !== crop) {
            normalized.recycle()
        }
        crop.recycle()
        return hash
    }

    private fun faceAppearanceHistogram(bitmap: Bitmap, rect: Rect): IntArray {
        val cropRect = expandRectToMinimumSide(
            rect,
            bitmap.width,
            bitmap.height,
            maxOf(rect.width(), rect.height()).coerceAtLeast(1)
        )
        val crop = Bitmap.createBitmap(
            bitmap,
            cropRect.left,
            cropRect.top,
            cropRect.width(),
            cropRect.height()
        )
        val sample = resizeBitmapToMaxSide(crop, VIDEO_APPEARANCE_SAMPLE_SIDE)
        val pixels = IntArray(sample.width * sample.height)
        sample.getPixels(pixels, 0, sample.width, 0, 0, sample.width, sample.height)
        val histogram = IntArray(VIDEO_APPEARANCE_HUE_BINS * VIDEO_APPEARANCE_VALUE_BINS)
        val hsv = FloatArray(3)
        pixels.forEach { color ->
            Color.RGBToHSV(Color.red(color), Color.green(color), Color.blue(color), hsv)
            val hueBin = (hsv[0] / 360f * VIDEO_APPEARANCE_HUE_BINS)
                .toInt()
                .coerceIn(0, VIDEO_APPEARANCE_HUE_BINS - 1)
            val valueBin = (hsv[2] * VIDEO_APPEARANCE_VALUE_BINS)
                .toInt()
                .coerceIn(0, VIDEO_APPEARANCE_VALUE_BINS - 1)
            histogram[hueBin * VIDEO_APPEARANCE_VALUE_BINS + valueBin] += 1
        }
        if (sample !== crop) {
            sample.recycle()
        }
        crop.recycle()
        return histogram
    }

    private fun luminance(color: Int): Int {
        val r = (color shr 16) and 0xFF
        val g = (color shr 8) and 0xFF
        val b = color and 0xFF
        return (r * 299 + g * 587 + b * 114) / 1000
    }

    private fun addOrReplaceVideoCandidate(

        candidates: MutableList<VideoFaceCandidate>,

        candidate: VideoFaceCandidate

    ) {

        val duplicateIndex = candidates.indexOfFirst {

            hammingDistance(it.faceHash, candidate.faceHash) <= VIDEO_FACE_HASH_DUP_DISTANCE

        }

        if (duplicateIndex >= 0) {

            if (candidate.qualityScore > candidates[duplicateIndex].qualityScore) {

                recordDiagnostic(

                    "视频候选相似脸替换: oldQuality=${candidates[duplicateIndex].qualityScore}, " +

                        "newQuality=${candidate.qualityScore}, distance=${hammingDistance(candidates[duplicateIndex].faceHash, candidate.faceHash)}"

                )

                candidates[duplicateIndex] = candidate

            }

        } else {

            candidates.add(candidate)

        }

        candidates.sortByDescending { it.qualityScore }

        while (candidates.size > VIDEO_MAX_LOCAL_CANDIDATES) {

            candidates.removeAt(candidates.lastIndex)

        }

    }

    private fun hammingDistance(left: Long, right: Long): Int {

        return java.lang.Long.bitCount(left xor right)

    }

    private fun searchFaceOnCloudSync(

        base64Image: String,

        maxFaceNum: Int,

        sourceLabel: String

    ): CloudFaceSearchResult {

        return try {

            val requestUrl = "$serverBaseUrl/dlsgzs/api/face/search"

            val requestMaxFaceNum = cloudMaxFaceNumFor(maxFaceNum)

            val jsonPayload = JsonObject().apply {

                addProperty("image", base64Image)

                addProperty("max_face_num", requestMaxFaceNum)

                addProperty("search_mode", "speed")

            }

            val requestBodyString = jsonPayload.toString()

            val requestBody = requestBodyString

                .toRequestBody("application/json; charset=utf-8".toMediaTypeOrNull())

            val request = Request.Builder()

                .url(requestUrl)

                .post(requestBody)

                .build()

            recordDiagnostic(

                "视频云端识别请求: source=$sourceLabel, url=$requestUrl, " +

                    "imageChars=${base64Image.length}, maxFaceNum=$requestMaxFaceNum"

            )

            okHttpClient.newCall(request).execute().use { response ->

                val bodyString = response.body?.string() ?: ""

                recordDiagnostic(

                    "视频云端识别响应: source=$sourceLabel, code=${response.code}, " +

                        "success=${response.isSuccessful}, bodyChars=${bodyString.length}"

                )

                if (!response.isSuccessful || bodyString.isEmpty()) {

                    return CloudFaceSearchResult(

                        experts = emptyList(),

                        message = cloudErrorMessage(response.code, bodyString)

                    )

                }

                val resultObj = Gson().fromJson(bodyString, JsonObject::class.java)

                val success = resultObj.get("success")?.asBoolean ?: false

                if (!success) {

                    return CloudFaceSearchResult(

                        experts = emptyList(),

                        message = resultObj.get("error")?.asString ?: "未匹配到登记的专家档案"

                    )

                }

                val resultsArray = resultObj.getAsJsonArray("results")

                if (resultsArray == null || resultsArray.size() == 0) {

                    return CloudFaceSearchResult(emptyList(), "云端未返回匹配结果")

                }

                val experts = mutableListOf<ExpertInfo>()

                for (i in 0 until resultsArray.size()) {

                    val matchItem = resultsArray.get(i).asJsonObject

                    val expertObj = matchItem.get("expert")

                        ?.takeIf { it.isJsonObject }

                        ?.asJsonObject

                        ?: continue

                    val score = matchItem.get("score")?.asFloat ?: 0f

                    val name = expertObj.get("name")?.asString ?: "-"

                    val company = expertObj.get("company")?.asString ?: "无工作单位"

                    val major = expertObj.get("major")?.asString ?: "未填写"

                    val phone = expertObj.get("phone")?.asString ?: "-"

                    val idCard = expertObj.get("id_card")?.asString ?: "-"

                    val photoPath = expertObj.get("photo_path")?.asString ?: ""

                    val faceRect = parseFaceRect(matchItem)

                    experts.add(ExpertInfo(name, company, major, phone, idCard, score, photoPath, faceRect))

                }

                CloudFaceSearchResult(experts, if (experts.isEmpty()) "云端未返回专家数据" else "ok")

            }

        } catch (e: Exception) {

            recordDiagnostic("视频云端识别异常: source=$sourceLabel", e)

            CloudFaceSearchResult(emptyList(), e.message ?: "视频云端识别异常")

        }

    }

    private fun buildVideoFullFrameRetryCandidate(candidate: VideoFaceCandidate): VideoFaceCandidate? {

        if (candidate.isRescueFrame) {

            return null

        }

        val originalBytes = candidate.originalBytes ?: return null

        val originalSize = imageSizeFromBytes(originalBytes) ?: return null

        var decodedBitmap: Bitmap? = null

        var uploadBitmap: Bitmap? = null

        return try {

            decodedBitmap = BitmapFactory.decodeByteArray(originalBytes, 0, originalBytes.size)

            val fullFrameBitmap = decodedBitmap ?: return null

            uploadBitmap = resizeBitmapForUpload(fullFrameBitmap, VIDEO_MAX_UPLOAD_IMAGE_SIDE)

            val finalUploadBytes = if (uploadBitmap === fullFrameBitmap) {

                originalBytes

            } else {

                bitmapToJpegBytes(uploadBitmap, VIDEO_FRAME_JPEG_QUALITY)

            }

            candidate.copy(

                originalWidth = originalSize.first,

                originalHeight = originalSize.second,

                uploadBytes = finalUploadBytes,

                uploadWidth = uploadBitmap.width,

                uploadHeight = uploadBitmap.height,

                localFaceRect = FaceRect(

                    0f,

                    0f,

                    uploadBitmap.width.toFloat(),

                    uploadBitmap.height.toFloat()

                ),

                sourceCropRect = FaceRect(

                    0f,

                    0f,

                    originalSize.first.toFloat(),

                    originalSize.second.toFloat()

                ),

                isRescueFrame = true

            )

        } catch (e: Exception) {

            recordDiagnostic("视频整帧救援候选构建异常: timeMs=${candidate.frameTimeMs}", e)

            null

        } finally {

            if (uploadBitmap != null && uploadBitmap !== decodedBitmap) {

                try {

                    uploadBitmap.recycle()

                } catch (_: Exception) {

                }

            }

            try {

                decodedBitmap?.recycle()

            } catch (_: Exception) {

            }

        }

    }

    private fun saveVideoExpertRecords(

        video: GalleryVideo,

        candidate: VideoFaceCandidate,

        experts: List<ExpertInfo>

    ): Int {

        var added = 0

        experts.forEachIndexed { index, expert ->

            val recordId = "${System.currentTimeMillis()}_${Random().nextInt(100000)}"

            val expertWithRect = if (expert.faceRect != null) {

                expert

            } else {

                recordDiagnostic(

                    "视频云端未返回人脸框，使用本地上传图人脸框: name=${expert.name}, " +

                        "rect=${candidate.localFaceRect.x},${candidate.localFaceRect.y}," +

                        "${candidate.localFaceRect.width},${candidate.localFaceRect.height}"

                )

                expert.copy(faceRect = candidate.localFaceRect)

            }

            val record = RecognitionRecord(

                id = recordId,

                createdAt = System.currentTimeMillis() - index * 10L,

                updatedAt = System.currentTimeMillis(),

                status = STATUS_SUCCESS,

                statusText = "视频识别成功"

            )

            candidate.originalBytes?.let {

                record.originalImagePath = saveHistoryImage(recordId, "original", it)

            }

            val savedOriginalSize = candidate.originalBytes?.let { imageSizeFromBytes(it) }
            val recordOriginalWidth = savedOriginalSize?.first ?: candidate.originalWidth
            val recordOriginalHeight = savedOriginalSize?.second ?: candidate.originalHeight
            val sourceCropForRecord = scaleFaceRect(
                candidate.sourceCropRect,
                candidate.originalWidth,
                candidate.originalHeight,
                recordOriginalWidth,
                recordOriginalHeight
            )

            record.uploadImagePath = saveHistoryImage(recordId, "upload", candidate.uploadBytes)

            record.originalWidth = recordOriginalWidth

            record.originalHeight = recordOriginalHeight

            record.uploadWidth = candidate.uploadWidth

            record.uploadHeight = candidate.uploadHeight

            record.faceRectImageWidth = candidate.uploadWidth

            record.faceRectImageHeight = candidate.uploadHeight

            record.uploadSourceRect = sourceCropForRecord

            record.localFaceRects.add(candidate.localFaceRect)

            record.experts.add(expertWithRect)

            val cropRect = expertWithRect.faceRect

            if (cropRect != null) {

                val crop = cropAndSaveBestFaceImage(

                    candidate.uploadBytes,

                    candidate.originalBytes,

                    cropRect,

                    recordId

                )

                if (crop != null) {

                    record.uploadImagePath = crop.path

                    record.uploadWidth = crop.width

                    record.uploadHeight = crop.height

                }

            }

            synchronized(recognitionRecords) {

                recognitionRecords.add(0, record)

            }

            publishRecognitionRecordIfNeeded(record, "视频识别")

            added += 1

            recordDiagnostic(

                "视频识别结果已保存: video=${video.displayName}, recordId=$recordId, " +

                    "name=${expert.name}, score=${expert.score}, timeMs=${candidate.frameTimeMs}, " +
                    "candidateFrame=${candidate.originalWidth}x${candidate.originalHeight}, " +
                    "recordOriginal=${recordOriginalWidth}x$recordOriginalHeight, " +
                    "sourceCrop=${sourceCropForRecord.x},${sourceCropForRecord.y}," +
                    "${sourceCropForRecord.width},${sourceCropForRecord.height}"

            )

        }

        if (added > 0) {

            saveRecognitionRecords()

            runOnUiThread {

                renderHistoryListIfVisible()

            }

        }

        return added

    }

    private fun clippedRect(rect: Rect, imageWidth: Int, imageHeight: Int): Rect? {

        val left = rect.left.coerceIn(0, imageWidth)

        val top = rect.top.coerceIn(0, imageHeight)

        val right = rect.right.coerceIn(0, imageWidth)

        val bottom = rect.bottom.coerceIn(0, imageHeight)

        return if (right > left && bottom > top) {

            Rect(left, top, right, bottom)

        } else {

            null

        }

    }

    private fun resizeBitmapToMaxSide(bitmap: Bitmap, maxSide: Int): Bitmap {

        if (maxSide <= 0) return bitmap

        val currentMaxSide = maxOf(bitmap.width, bitmap.height)

        if (currentMaxSide <= maxSide) {

            return bitmap

        }

        val scale = maxSide.toFloat() / currentMaxSide.toFloat()

        val targetWidth = (bitmap.width * scale).roundToInt().coerceAtLeast(1)

        val targetHeight = (bitmap.height * scale).roundToInt().coerceAtLeast(1)

        return Bitmap.createScaledBitmap(bitmap, targetWidth, targetHeight, true)

    }

    private fun formatDurationMs(durationMs: Long): String {

        val totalSeconds = (durationMs / 1000L).coerceAtLeast(0L)

        val minutes = totalSeconds / 60L

        val seconds = totalSeconds % 60L

        return String.format(Locale.CHINA, "%d:%02d", minutes, seconds)

    }

    private fun triggerCaptureFromExternalEvent(source: String) {

        val now = System.currentTimeMillis()

        if (now - lastExternalCaptureTriggerAt < EXTERNAL_CAPTURE_DEBOUNCE_MS) {

            recordDiagnostic("$source 触发被忽略: debounceMs=$EXTERNAL_CAPTURE_DEBOUNCE_MS")

            return

        }

        lastExternalCaptureTriggerAt = now

        recordDiagnostic("$source 触发现场抓拍比对")

        runOnUiThread {

            if (binding.settingsPage.visibility == View.VISIBLE ||

                binding.historyPage.visibility == View.VISIBLE ||

                binding.galleryPage.visibility == View.VISIBLE ||

                binding.videoPage.visibility == View.VISIBLE

            ) {

                showMainPage()

            }

            takePhotoAndMatch()

        }

    }

    private fun createRecognitionRecord(

        status: String = STATUS_CAPTURING,

        statusText: String = "正在请求眼镜拍照"

    ): RecognitionRecord {

        val now = System.currentTimeMillis()

        val record = RecognitionRecord(

            id = "${now}_${Random().nextInt(100000)}",

            createdAt = now,

            updatedAt = now,

            status = status,

            statusText = statusText

        )

        synchronized(recognitionRecords) {

            recognitionRecords.add(0, record)

        }

        saveRecognitionRecords()

        runOnUiThread {

            renderHistoryListIfVisible()

        }

        return record

    }

    private fun findRecognitionRecord(recordId: String?): RecognitionRecord? {

        if (recordId == null) return null

        return synchronized(recognitionRecords) {

            recognitionRecords.firstOrNull { it.id == recordId }

        }

    }

    private fun updateRecognitionRecord(recordId: String?, block: (RecognitionRecord) -> Unit) {

        val record = findRecognitionRecord(recordId) ?: return

        block(record)

        record.updatedAt = System.currentTimeMillis()

        val updatedStatus = record.status

        val updatedRecordId = record.id

        saveRecognitionRecords()

        updateGalleryBatchProgressForRecord(updatedRecordId, updatedStatus)

        runOnUiThread {

            renderHistoryListIfVisible()

        }

    }

    private fun loadRecognitionRecords() {

        val json = getSharedPreferences(HISTORY_PREFS_NAME, Context.MODE_PRIVATE)

            .getString(HISTORY_PREFS_KEY, "[]")

        val type = object : TypeToken<MutableList<RecognitionRecord>>() {}.type

        val loaded = try {

            Gson().fromJson<MutableList<RecognitionRecord>>(json, type) ?: mutableListOf()

        } catch (e: Exception) {

            recordDiagnostic("读取识别记录失败，将重置历史", e)

            mutableListOf()

        }

        synchronized(recognitionRecords) {

            recognitionRecords.clear()

            recognitionRecords.addAll(loaded.sortedByDescending { it.createdAt })

        }

    }

    private fun saveRecognitionRecords() {

        val snapshot = synchronized(recognitionRecords) {

            recognitionRecords.sortedByDescending { it.createdAt }

        }

        executeWorker("保存识别记录") {

            try {

                val json = Gson().toJson(snapshot)

                getSharedPreferences(HISTORY_PREFS_NAME, Context.MODE_PRIVATE)

                    .edit()

                    .putString(HISTORY_PREFS_KEY, json)

                    .apply()

            } catch (e: Exception) {

                recordDiagnostic("后台保存识别记录异常", e)

            }

        }

    }

    private fun loadSharedRecognitionRecords() {

        val json = getSharedPreferences(SHARE_PREFS_NAME, Context.MODE_PRIVATE)

            .getString(SHARE_PREF_RECORDS, "[]")

        val type = object : TypeToken<MutableList<SharedRecognitionRecord>>() {}.type

        val loaded = try {

            Gson().fromJson<MutableList<SharedRecognitionRecord>>(json, type) ?: mutableListOf()

        } catch (e: Exception) {

            recordDiagnostic("读取共享识别记录失败，将重置共享缓存", e)

            mutableListOf()

        }

        val now = System.currentTimeMillis()

        if (pruneDeletedSharedRecordIds(now)) {

            saveDeletedSharedRecordIds()

        }

        val hiddenIds = synchronized(deletedSharedRecordIds) { deletedSharedRecordIds.toSet() }

        synchronized(sharedRecognitionRecords) {

            sharedRecognitionRecords.clear()

            sharedRecognitionRecords.addAll(

                loaded

                    .filter { it.expiresAt > now && it.shareId !in hiddenIds }

                    .sortedByDescending { it.createdAt }

            )

        }

    }

    private fun saveSharedRecognitionRecords() {

        val snapshot = synchronized(sharedRecognitionRecords) {

            sharedRecognitionRecords

                .filter { it.expiresAt > System.currentTimeMillis() }

                .sortedByDescending { it.createdAt }

        }

        executeWorker("保存共享识别记录") {

            try {

                val json = Gson().toJson(snapshot)

                getSharedPreferences(SHARE_PREFS_NAME, Context.MODE_PRIVATE)

                    .edit()

                    .putString(SHARE_PREF_RECORDS, json)

                    .apply()

            } catch (e: Exception) {

                recordDiagnostic("后台保存共享识别记录异常", e)

            }

        }

    }

    private fun cleanupExpiredSharedRecognitionRecords() {

        val now = System.currentTimeMillis()

        var changed = false

        val expiredShareIds = mutableListOf<String>()

        synchronized(sharedRecognitionRecords) {

            val iterator = sharedRecognitionRecords.iterator()

            while (iterator.hasNext()) {

                val record = iterator.next()

                if (record.expiresAt <= now) {

                    iterator.remove()

                    expiredShareIds.add(record.shareId)

                    changed = true

                }

            }

        }

        if (changed) {

            saveSharedRecognitionRecords()

            expiredShareIds.forEach { deleteSharedOriginalCacheFile(it) }

            cleanupSharedOriginalCache()

            recordDiagnostic("已清理过期共享记录")

        }

    }

    private fun startSharedRecordSync() {

        if (!recordShareEnabled || !isActivityResumed) {

            return

        }

        sharedRecordSyncRunning = true

        sharedRecordSyncCursor = 0L

        mainHandler.removeCallbacks(sharedRecordSyncRunnable)

        fetchSharedRecognitionRecords(initialFetch = true)

        mainHandler.postDelayed(sharedRecordSyncRunnable, SHARED_RECORD_POLL_MS)

    }

    private fun stopSharedRecordSync() {

        sharedRecordSyncRunning = false

        mainHandler.removeCallbacks(sharedRecordSyncRunnable)

    }

    private fun fetchSharedRecognitionRecords(initialFetch: Boolean) {

        if (!recordShareEnabled || sharedRecordSyncInFlight) {

            return

        }

        val since = if (initialFetch) 0L else sharedRecordSyncCursor

        val requestUrl = serverBaseUrl.trimEnd('/') +

            "/dlsgzs/api/shared-records/recent?since=$since&device_id=${urlEncode(shareDeviceId)}"

        val request = try {

            Request.Builder().url(requestUrl).get().build()

        } catch (e: Exception) {

            recordDiagnostic("共享记录同步请求构建失败: url=$requestUrl", e)

            return

        }

        sharedRecordSyncInFlight = true

        okHttpClient.newCall(request).enqueue(object : Callback {

            override fun onFailure(call: Call, e: IOException) {

                sharedRecordSyncInFlight = false

                recordDiagnostic("共享记录同步网络失败: url=$requestUrl", e)

            }

            override fun onResponse(call: Call, response: Response) {

                response.use {

                    try {

                        val bodyString = it.body?.string().orEmpty()

                        if (!it.isSuccessful || bodyString.isBlank()) {

                            recordDiagnostic(

                                "共享记录同步 HTTP 失败: code=${it.code}, bodyPreview=${bodyString.take(160)}"

                            )

                            return

                        }

                        val obj = Gson().fromJson(bodyString, JsonObject::class.java)

                        if (obj.get("success")?.asBoolean != true) {

                            recordDiagnostic("共享记录同步业务失败: bodyPreview=${bodyString.take(160)}")

                            return

                        }

                        val items = obj.getAsJsonArray("items")

                        val parsedRecords = mutableListOf<SharedRecognitionRecord>()

                        if (items != null) {

                            for (i in 0 until items.size()) {

                                val itemObj = items.get(i).takeIf { item -> item.isJsonObject }?.asJsonObject ?: continue

                                parseSharedRecognitionRecord(itemObj)?.let { record ->

                                    parsedRecords.add(record)

                                }

                            }

                        }

                        val nextCursor = obj.get("next_cursor")?.takeIf { cursor -> !cursor.isJsonNull }?.asLong

                            ?: System.currentTimeMillis()

                        if (!recordShareEnabled || !sharedRecordSyncRunning) {

                            recordDiagnostic("共享记录同步响应已忽略: sharingEnabled=$recordShareEnabled, running=$sharedRecordSyncRunning")

                            return

                        }

                        sharedRecordSyncCursor = maxOf(sharedRecordSyncCursor, nextCursor)

                        if (parsedRecords.isNotEmpty()) {

                            mergeSharedRecognitionRecords(parsedRecords)

                            recordDiagnostic(

                                "共享记录同步完成: received=${parsedRecords.size}, cursor=$sharedRecordSyncCursor"

                            )

                        } else if (initialFetch) {

                            cleanupExpiredSharedRecognitionRecords()

                        }

                    } catch (e: Exception) {

                        recordDiagnostic("共享记录同步响应解析异常", e)

                    } finally {

                        sharedRecordSyncInFlight = false

                    }

                }

            }

        })

    }

    private fun mergeSharedRecognitionRecords(newRecords: List<SharedRecognitionRecord>) {

        if (pruneDeletedSharedRecordIds()) {

            saveDeletedSharedRecordIds()

        }

        val hiddenIds = synchronized(deletedSharedRecordIds) { deletedSharedRecordIds.toSet() }

        var changed = false

        synchronized(sharedRecognitionRecords) {

            newRecords

                .filter { it.expiresAt > System.currentTimeMillis() && it.shareId !in hiddenIds }

                .forEach { incoming ->

                    val existingIndex = sharedRecognitionRecords.indexOfFirst { it.shareId == incoming.shareId }

                    if (existingIndex >= 0) {

                        sharedRecognitionRecords[existingIndex] = incoming

                    } else {

                        sharedRecognitionRecords.add(incoming)

                    }

                    changed = true

                }

            if (changed) {

                sharedRecognitionRecords.sortByDescending { it.createdAt }

            }

        }

        if (changed) {

            saveSharedRecognitionRecords()

            prefetchRecentSharedOriginalImages()

            runOnUiThread {

                renderHistoryListIfVisible()

            }

        }

    }

    private fun parseSharedRecognitionRecord(itemObj: JsonObject): SharedRecognitionRecord? {

        val shareId = jsonString(itemObj, "share_id").ifBlank { return null }

        val metadata = firstJsonObject(itemObj, "metadata") ?: return null

        val recordObj = firstJsonObject(metadata, "record") ?: return null

        val expertObj = firstJsonObject(recordObj, "expert") ?: return null

        val expert = ExpertInfo(

            name = jsonString(expertObj, "name", "-"),

            company = jsonString(expertObj, "company", "无工作单位"),

            major = jsonString(expertObj, "major", "未填写"),

            phone = jsonString(expertObj, "phone", "-"),

            idCard = jsonString(expertObj, "id_card", "-"),

            score = jsonFloat(recordObj, "score") ?: jsonFloat(expertObj, "score") ?: 0f,

            photoPath = jsonString(expertObj, "photo_path", ""),

            faceRect = parseFaceRect(recordObj)

        )

        return SharedRecognitionRecord(

            shareId = shareId,

            clientRecordId = jsonString(itemObj, "client_record_id"),

            deviceId = jsonString(itemObj, "device_id"),

            nickname = jsonString(itemObj, "nickname", DEFAULT_SHARE_NICKNAME).ifBlank { DEFAULT_SHARE_NICKNAME },

            source = jsonString(itemObj, "source"),

            capturedAt = jsonLong(itemObj, "captured_at") ?: jsonLong(metadata, "captured_at") ?: 0L,

            createdAt = jsonLong(itemObj, "created_at") ?: System.currentTimeMillis(),

            expiresAt = jsonLong(itemObj, "expires_at") ?: (System.currentTimeMillis() + SHARED_RECORD_RETENTION_MS),

            originalUrl = jsonString(itemObj, "original_url"),

            faceUrl = jsonString(itemObj, "face_url"),

            originalWidth = jsonInt(recordObj, "original_width") ?: 0,

            originalHeight = jsonInt(recordObj, "original_height") ?: 0,

            uploadWidth = jsonInt(recordObj, "upload_width") ?: 0,

            uploadHeight = jsonInt(recordObj, "upload_height") ?: 0,

            faceRectImageWidth = jsonInt(recordObj, "face_rect_image_width") ?: 0,

            faceRectImageHeight = jsonInt(recordObj, "face_rect_image_height") ?: 0,

            uploadSourceRect = parseNamedFaceRect(recordObj, "upload_source_rect", "uploadSourceRect"),

            expert = expert

        )

    }

    private fun urlEncode(value: String): String {

        return try {

            URLEncoder.encode(value, "UTF-8")

        } catch (_: Exception) {

            value

        }

    }

    private fun publishRecognitionRecordIfNeeded(recordId: String?, sourceLabel: String) {

        val record = findRecognitionRecord(recordId) ?: return

        publishRecognitionRecordIfNeeded(record, sourceLabel)

    }

    private fun publishRecognitionRecordIfNeeded(record: RecognitionRecord, sourceLabel: String) {

        if (!recordShareEnabled) {

            return

        }

        val snapshot = synchronized(recognitionRecords) {

            val current = recognitionRecords.firstOrNull { it.id == record.id } ?: return

            if (current.status != STATUS_SUCCESS || current.experts.isEmpty()) {

                return

            }

            if (current.sharePending || current.sharedAt > 0L || !current.sharedShareId.isNullOrBlank()) {

                return

            }

            current.sharePending = true

            current.copy(

                localFaceRects = current.localFaceRects.toMutableList(),

                experts = current.experts.toMutableList()

            )

        }

        saveRecognitionRecords()

        executeWorker("发布共享识别记录") {

            postSharedRecognitionRecord(snapshot, sourceLabel)

        }

    }

    private fun postSharedRecognitionRecord(record: RecognitionRecord, sourceLabel: String) {

        val expert = record.experts.firstOrNull()

        if (expert == null) {

            markSharedRecordPublishFinished(record.id, null, false)

            return

        }

        val originalBytes = loadHistoryBytes(record.originalImagePath)

        if (originalBytes == null || originalBytes.isEmpty()) {

            recordDiagnostic("共享记录发布延后: 原图未保存, id=${record.id}, source=$sourceLabel")

            scheduleSharedRecordPublishRetry(record.id, sourceLabel, "original_not_saved")

            return

        }

        val faceBytes = loadHistoryBytes(record.uploadImagePath)

        val metadata = buildSharedRecordMetadata(record, expert, sourceLabel)

        val multipart = MultipartBody.Builder()

            .setType(MultipartBody.FORM)

            .addFormDataPart("metadata", metadata.toString())

            .addFormDataPart(

                "original_image",

                "${record.id}_original.jpg",

                originalBytes.toRequestBody("image/jpeg".toMediaTypeOrNull())

            )

        if (faceBytes != null && faceBytes.isNotEmpty()) {

            multipart.addFormDataPart(

                "face_image",

                "${record.id}_face.jpg",

                faceBytes.toRequestBody("image/jpeg".toMediaTypeOrNull())

            )

        }

        val requestUrl = "${serverBaseUrl.trimEnd('/')}/dlsgzs/api/shared-records"

        val request = try {

            Request.Builder()

                .url(requestUrl)

                .post(multipart.build())

                .build()

        } catch (e: Exception) {

            recordDiagnostic("共享记录发布请求构建失败: id=${record.id}, url=$requestUrl", e)

            scheduleSharedRecordPublishRetry(record.id, sourceLabel, "request_build_failed")

            return

        }

        try {

            okHttpClient.newCall(request).execute().use { response ->

                val bodyString = response.body?.string().orEmpty()

                if (!response.isSuccessful || bodyString.isBlank()) {

                    recordDiagnostic(

                        "共享记录发布 HTTP 失败: id=${record.id}, code=${response.code}, bodyPreview=${bodyString.take(160)}"

                    )

                    if (bodyString.isBlank() || shouldRetrySharedRecordPublish(response.code)) {

                        scheduleSharedRecordPublishRetry(record.id, sourceLabel, "http_${response.code}")

                    } else {

                        markSharedRecordPublishFinished(record.id, null, false)

                    }

                    return

                }

                val bodyObj = Gson().fromJson(bodyString, JsonObject::class.java)

                val success = bodyObj.get("success")?.asBoolean ?: false

                if (!success) {

                    recordDiagnostic("共享记录发布业务失败: id=${record.id}, bodyPreview=${bodyString.take(160)}")

                    markSharedRecordPublishFinished(record.id, null, false)

                    return

                }

                val shareId = bodyObj.get("share_id")?.takeIf { !it.isJsonNull }?.asString

                markSharedRecordPublishFinished(record.id, shareId, true)

                recordDiagnostic(

                    "共享记录发布成功: id=${record.id}, shareId=${shareId ?: "-"}, source=${sharedSourceType(sourceLabel)}, " +

                        "originalBytes=${originalBytes.size}, faceBytes=${faceBytes?.size ?: 0}, nickname=${shareDisplayNickname()}"

                )

            }

        } catch (e: Exception) {

            recordDiagnostic("共享记录发布网络异常: id=${record.id}, url=$requestUrl", e)

            scheduleSharedRecordPublishRetry(record.id, sourceLabel, "network_exception")

        }

    }

    private fun shouldRetrySharedRecordPublish(httpCode: Int): Boolean {

        return httpCode == 0 || httpCode == 408 || httpCode == 429 || httpCode >= 500

    }

    private fun buildSharedRecordMetadata(record: RecognitionRecord, expert: ExpertInfo, sourceLabel: String): JsonObject {

        val expertObj = JsonObject().apply {

            addProperty("name", expert.name)

            addProperty("company", expert.company)

            addProperty("major", expert.major)

            addProperty("phone", expert.phone)

            addProperty("id_card", expert.idCard ?: "-")

            addProperty("photo_path", expert.photoPath)

            addProperty("score", expert.score)

        }

        val recordObj = JsonObject().apply {

            addProperty("status", record.status)

            addProperty("status_text", record.statusText)

            addProperty("score", expert.score)

            add("expert", expertObj)

            expert.faceRect?.let { add("face_rect", faceRectToJson(it)) }

            record.uploadSourceRect?.let { add("upload_source_rect", faceRectToJson(it)) }

            addProperty("original_width", record.originalWidth)

            addProperty("original_height", record.originalHeight)

            addProperty("upload_width", record.uploadWidth)

            addProperty("upload_height", record.uploadHeight)

            addProperty("face_rect_image_width", record.faceRectImageWidth)

            addProperty("face_rect_image_height", record.faceRectImageHeight)

        }

        return JsonObject().apply {

            addProperty("client_record_id", record.id)

            addProperty("device_id", shareDeviceId)

            addProperty("nickname", shareDisplayNickname())

            addProperty("source", sharedSourceType(sourceLabel))

            addProperty("captured_at", record.createdAt)

            add("record", recordObj)

        }

    }

    private fun faceRectToJson(rect: FaceRect): JsonObject {

        return JsonObject().apply {

            addProperty("x", rect.x)

            addProperty("y", rect.y)

            addProperty("width", rect.width)

            addProperty("height", rect.height)

        }

    }

    private fun sharedSourceType(sourceLabel: String): String {

        return when {

            sourceLabel.contains("图库") -> "gallery"

            sourceLabel.contains("视频") -> "video"

            sourceLabel.contains("实时") -> "realtime"

            else -> "glasses"

        }

    }

    private fun markSharedRecordPublishFinished(recordId: String, shareId: String?, success: Boolean) {

        synchronized(recognitionRecords) {

            val record = recognitionRecords.firstOrNull { it.id == recordId } ?: return@synchronized

            record.sharePending = false

            if (success) {

                record.sharedAt = System.currentTimeMillis()

                record.sharedShareId = shareId

                record.shareRetryCount = 0

            }

        }

        saveRecognitionRecords()

    }

    private fun scheduleSharedRecordPublishRetry(recordId: String, sourceLabel: String, reason: String) {

        var retryIndex = -1

        synchronized(recognitionRecords) {

            val record = recognitionRecords.firstOrNull { it.id == recordId } ?: return@synchronized

            record.sharePending = false

            if (record.shareRetryCount < SHARE_PUBLISH_MAX_RETRIES) {

                record.shareRetryCount += 1

                retryIndex = record.shareRetryCount

            }

        }

        saveRecognitionRecords()

        if (retryIndex > 0) {

            val delayMs = SHARE_PUBLISH_RETRY_DELAY_MS * retryIndex

            mainHandler.postDelayed(

                {

                    publishRecognitionRecordIfNeeded(recordId, sourceLabel)

                },

                delayMs

            )

            recordDiagnostic(

                "共享记录发布计划重试: id=$recordId, retry=$retryIndex, delayMs=$delayMs, reason=$reason"

            )

        } else {

            recordDiagnostic("共享记录发布放弃: id=$recordId, reason=$reason")

        }

    }

    private fun executeThumbnailWorker(taskName: String, block: () -> Unit) {

        if (!::thumbnailExecutor.isInitialized || thumbnailExecutor.isShutdown || thumbnailExecutor.isTerminated) {

            Log.w(TAG, "Skip thumbnail task after shutdown: $taskName")

            return

        }

        try {

            thumbnailExecutor.execute {

                try {

                    block()

                } catch (e: Exception) {

                    Log.e(TAG, "Thumbnail task failed: $taskName", e)

                }

            }

        } catch (e: RejectedExecutionException) {

            Log.w(TAG, "Thumbnail task rejected after shutdown: $taskName")

        }

    }

    private fun executeWorker(taskName: String, block: () -> Unit) {

        if (!::workExecutor.isInitialized || workExecutor.isShutdown || workExecutor.isTerminated) {

            Log.w(TAG, "Skip worker task after shutdown: $taskName")

            return

        }

        try {

            workExecutor.execute {

                try {

                    block()

                } catch (e: Exception) {

                    recordDiagnostic("$taskName 执行异常", e)

                }

            }

        } catch (e: RejectedExecutionException) {

            Log.w(TAG, "Worker task rejected after shutdown: $taskName", e)

        }

    }

    private fun executeRealtimeCloudWorker(taskName: String, block: () -> Unit) {

        if (!::realtimeCloudExecutor.isInitialized ||
            realtimeCloudExecutor.isShutdown ||
            realtimeCloudExecutor.isTerminated
        ) {

            Log.w(TAG, "Skip realtime cloud task after shutdown: $taskName")

            return

        }

        try {

            realtimeCloudExecutor.execute {

                try {

                    block()

                } catch (e: Exception) {

                    recordDiagnostic("$taskName 执行异常", e)

                }

            }

        } catch (e: RejectedExecutionException) {

            Log.w(TAG, "Realtime cloud task rejected after shutdown: $taskName", e)

        }

    }

    private fun markInterruptedRecordsForRetry() {

        var changed = false

        synchronized(recognitionRecords) {

            recognitionRecords.forEach { record ->

                if (record.status in setOf(STATUS_CAPTURING, STATUS_LOCAL_PROCESSING, STATUS_UPLOADING)) {

                    record.status = STATUS_INTERRUPTED

                    record.statusText = "上次关闭时未完成，可手动重试"

                    record.updatedAt = System.currentTimeMillis()

                    changed = true

                }

            }

        }

        if (changed) {

            saveRecognitionRecords()

        }

    }

    private fun cleanupExpiredRecognitionRecords() {

        val cutoff = System.currentTimeMillis() - HISTORY_RETENTION_MS

        val expired = mutableListOf<RecognitionRecord>()

        synchronized(recognitionRecords) {

            val iterator = recognitionRecords.iterator()

            while (iterator.hasNext()) {

                val record = iterator.next()

                if (record.createdAt < cutoff) {

                    expired.add(record)

                    iterator.remove()

                }

            }

        }

        expired.forEach { deleteRecognitionRecordFiles(it) }

        if (expired.isNotEmpty()) {

            saveRecognitionRecords()

            recordDiagnostic("已自动清理过期识别记录: count=${expired.size}")

        }

    }

    private fun historyDir(): File {

        return File(filesDir, "recognition_history").apply {

            if (!exists()) mkdirs()

        }

    }

    private fun saveHistoryImage(recordId: String, suffix: String, bytes: ByteArray): String {

        val file = File(historyDir(), "${recordId}_${suffix}.jpg")

        file.writeBytes(bytes)

        return file.absolutePath

    }

    private fun loadHistoryBytes(path: String?): ByteArray? {

        if (path.isNullOrEmpty()) return null

        val file = File(path)

        return if (file.exists()) file.readBytes() else null

    }

    private fun decodeHistoryThumbnail(path: String?, maxSide: Int): Bitmap? {

        if (path.isNullOrBlank()) return null

        val file = File(path)

        if (!file.exists()) return null

        return try {

            val bounds = BitmapFactory.Options().apply { inJustDecodeBounds = true }

            BitmapFactory.decodeFile(path, bounds)

            if (bounds.outWidth <= 0 || bounds.outHeight <= 0) {

                return null

            }

            val options = BitmapFactory.Options().apply {

                inSampleSize = calculateInSampleSize(bounds.outWidth, bounds.outHeight, maxSide)

            }

            BitmapFactory.decodeFile(path, options)

        } catch (e: Exception) {

            recordDiagnostic("识别记录缩略图解码失败: path=$path", e)

            null

        } catch (e: OutOfMemoryError) {

            recordDiagnostic("识别记录缩略图解码内存不足: path=$path", e)

            null

        }

    }

    private fun deleteRecognitionRecord(recordId: String) {

        val removed = synchronized(recognitionRecords) {

            val record = recognitionRecords.firstOrNull { it.id == recordId }

            if (record != null) {

                recognitionRecords.remove(record)

            }

            record

        }

        if (removed != null) {

            deleteRecognitionRecordFiles(removed)

            saveRecognitionRecords()

            renderHistoryList()

            recordDiagnostic("手动删除识别记录: id=$recordId")

        }

    }

    private fun deleteRecognitionRecordFiles(record: RecognitionRecord) {

        listOf(record.originalImagePath, record.uploadImagePath).forEach { path ->

            if (!path.isNullOrEmpty()) {

                try {

                     File(path).delete()

                } catch (e: Exception) {

                    recordDiagnostic("删除识别记录图片失败: $path", e)

                }

            }

        }

    }

    private fun clearFailedHistoryRecords() {

        val toRemove = synchronized(recognitionRecords) {

            val activeStates = setOf(STATUS_CAPTURING, STATUS_LOCAL_PROCESSING, STATUS_UPLOADING)

            val filtered = recognitionRecords.filter { it.status != STATUS_SUCCESS && it.status !in activeStates }

            recognitionRecords.removeAll(filtered)

            filtered

        }

        

        if (toRemove.isEmpty()) {

            Toast.makeText(this, "暂无可清理的无识别记录", Toast.LENGTH_SHORT).show()

            return

        }

        

        executeWorker("清理无识别记录") {

            toRemove.forEach { deleteRecognitionRecordFiles(it) }

            saveRecognitionRecords()

            runOnUiThread {

                renderHistoryList()

                Toast.makeText(this@MainActivity, "已清理 ${toRemove.size} 条无识别记录", Toast.LENGTH_SHORT).show()

            }

        }

        recordDiagnostic("一键清除无识别记录: 清除数量=${toRemove.size}")

    }

    private fun retryRecognitionRecord(recordId: String) {

        val record = findRecognitionRecord(recordId)

        if (record == null) {

            Toast.makeText(this, "记录不存在", Toast.LENGTH_SHORT).show()

            return

        }

        val uploadBytes = loadHistoryBytes(record.uploadImagePath)

        val originalBytes = loadHistoryBytes(record.originalImagePath)

        when {

            uploadBytes != null -> {

                updateRecognitionRecord(recordId) {

                    resetSharedPublishState(it)

                    it.status = STATUS_UPLOADING

                    it.statusText = "正在重新上传识别"

                    it.errorMessage = null

                    it.experts.clear()

                }

                val base64Data = Base64.encodeToString(uploadBytes, Base64.NO_WRAP)

                postFaceSearchRequest(recordId, "data:image/jpeg;base64,$base64Data", DEFAULT_CLOUD_MAX_FACE_NUM)

            }

            originalBytes != null -> {

                updateRecognitionRecord(recordId) {

                    resetSharedPublishState(it)

                    it.status = STATUS_LOCAL_PROCESSING

                    it.statusText = "正在重新检测人脸"

                    it.errorMessage = null

                    it.experts.clear()

                }

                processCapturedFrameForMatch(recordId, originalBytes)

            }

            else -> {

                updateRecognitionRecord(recordId) {

                    it.status = STATUS_FAILED

                    it.statusText = "原始照片不存在，无法重试"

                    it.errorMessage = it.statusText

                }

                Toast.makeText(this, "原始照片不存在，无法重试", Toast.LENGTH_SHORT).show()

            }

        }

    }

    private fun resetSharedPublishState(record: RecognitionRecord) {

        record.sharePending = false

        record.shareRetryCount = 0

        record.sharedAt = 0L

        record.sharedShareId = null

    }

    private fun deleteSharedRecognitionRecord(shareId: String) {

        val removed = synchronized(sharedRecognitionRecords) {

            val record = sharedRecognitionRecords.firstOrNull { it.shareId == shareId }

            if (record != null) {

                sharedRecognitionRecords.remove(record)

            }

            record

        }

        if (removed != null) {

            synchronized(deletedSharedRecordIds) {

                deletedSharedRecordIds.add(shareId)

            }

            synchronized(deletedSharedRecordTimestamps) {

                deletedSharedRecordTimestamps[shareId] = System.currentTimeMillis()

            }

            saveDeletedSharedRecordIds()

            deleteSharedOriginalCacheFile(shareId)

            saveSharedRecognitionRecords()

            renderHistoryList()

            recordDiagnostic("本机删除共享识别记录: shareId=$shareId, from=${removed.nickname}")

        }

    }

    private fun loadSharedThumbnail(record: SharedRecognitionRecord, imageView: ImageView) {

        val imageUrl = (record.faceUrl.ifBlank { record.originalUrl }).ifBlank { return }

        val requestUrl = expertPhotoUrl(imageUrl)

        val request = try {

            Request.Builder().url(requestUrl).get().build()

        } catch (e: Exception) {

            recordDiagnostic("共享缩略图请求构建失败: shareId=${record.shareId}, url=$requestUrl", e)

            return

        }

        okHttpClient.newCall(request).enqueue(object : Callback {

            override fun onFailure(call: Call, e: IOException) {

                recordDiagnostic("共享缩略图加载失败: shareId=${record.shareId}, url=$requestUrl", e)

            }

            override fun onResponse(call: Call, response: Response) {

                response.use {

                    if (!it.isSuccessful) {

                        recordDiagnostic("共享缩略图 HTTP 失败: shareId=${record.shareId}, code=${it.code}")

                        return

                    }

                    val bytes = it.body?.bytes()

                    if (bytes == null || bytes.isEmpty()) {

                        return

                    }

                    val bitmap = BitmapFactory.decodeByteArray(bytes, 0, bytes.size) ?: return

                    runOnUiThread {

                        if (imageView.tag == record.shareId) {

                            imageView.setImageBitmap(bitmap)

                        }

                    }

                }

            }

        })

    }

    private fun renderHistoryList() {

        if (!::binding.isInitialized) return

        cleanupExpiredSharedRecognitionRecords()

        val records = synchronized(recognitionRecords) {

            recognitionRecords.sortedByDescending { it.createdAt }

        }

        val sharedRecords = synchronized(sharedRecognitionRecords) {

            sharedRecognitionRecords

                .filter { it.expiresAt > System.currentTimeMillis() }

                .sortedByDescending { it.createdAt }

        }

        val items = mutableListOf<HistoryRecordItem>()

        records.forEach { record ->

            items.add(HistoryRecordItem(createdAt = record.createdAt, localRecord = record))

        }

        sharedRecords.forEach { record ->

            items.add(HistoryRecordItem(createdAt = record.createdAt, sharedRecord = record))

        }

        items.sortByDescending { it.createdAt }

        binding.historyList.removeAllViews()

        binding.tvHistoryEmpty.visibility = if (items.isEmpty()) View.VISIBLE else View.GONE

        items.forEach { item ->

            try {

                val localRecord = item.localRecord

                val sharedRecord = item.sharedRecord

                when {

                    localRecord != null -> binding.historyList.addView(createHistoryRecordView(localRecord))

                    sharedRecord != null -> binding.historyList.addView(createSharedHistoryRecordView(sharedRecord))

                }

            } catch (e: Exception) {

                recordDiagnostic(

                    "渲染识别记录异常: local=${item.localRecord?.id}, shared=${item.sharedRecord?.shareId}",

                    e

                )

            }

        }

    }

    private fun renderHistoryListIfVisible() {

        if (::binding.isInitialized && binding.historyPage.visibility == View.VISIBLE) {

            renderHistoryList()

        }

    }

    private fun createHistoryRecordView(record: RecognitionRecord): View {

        val card = LinearLayout(this).apply {

            orientation = LinearLayout.VERTICAL

            setPadding(dp(14), dp(14), dp(14), dp(14))

            background = ContextCompat.getDrawable(this@MainActivity, R.drawable.bg_page_panel)

        }

        val layoutParams = LinearLayout.LayoutParams(

            LinearLayout.LayoutParams.MATCH_PARENT,

            LinearLayout.LayoutParams.WRAP_CONTENT

        ).apply {

            bottomMargin = dp(12)

        }

        card.layoutParams = layoutParams

        val topRow = LinearLayout(this).apply {

            orientation = LinearLayout.HORIZONTAL

            gravity = android.view.Gravity.CENTER_VERTICAL

        }

        val thumb = ImageView(this).apply {

            setLayoutParams(

                LinearLayout.LayoutParams(dp(68), dp(88)).apply {

                    setMargins(0, 0, dp(12), 0)

                }

            )

            scaleType = ImageView.ScaleType.CENTER_CROP

            background = ContextCompat.getDrawable(this@MainActivity, R.drawable.bg_preview_panel)

            val bitmap = decodeHistoryThumbnail(record.uploadImagePath ?: record.originalImagePath, dp(120))

            if (bitmap != null) setImageBitmap(bitmap)

        }

        val textBox = LinearLayout(this).apply {

            orientation = LinearLayout.VERTICAL

            setLayoutParams(LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f))

        }

        if (record.experts.isNotEmpty()) {

            val expert = record.experts[0] // 拆分后每条卡片有且仅有 1 个专家

            

            // 1. 时间与相似度分值药丸行

            val headerRow = LinearLayout(this).apply {

                orientation = LinearLayout.HORIZONTAL

                gravity = android.view.Gravity.CENTER_VERTICAL

            }

            headerRow.addView(TextView(this).apply {

                text = historyTimeFormat.format(Date(record.createdAt))

                setTextColor(ContextCompat.getColor(this@MainActivity, R.color.text_secondary))

                textSize = 12f

            })

            headerRow.addView(TextView(this).apply {

                text = String.format(Locale.getDefault(), "  相似度 %.1f%%", expert.score)

                if (expert.score >= 85.0) {
                    setTextColor(ContextCompat.getColor(this@MainActivity, R.color.accent_error_red))
                } else {
                    setTextColor(ContextCompat.getColor(this@MainActivity, R.color.accent_aurora_green))
                }

                textSize = 12f

                setTypeface(typeface, android.graphics.Typeface.BOLD)

            })

            textBox.addView(headerRow)

            

            // 2. 专家姓名大字行

            textBox.addView(TextView(this).apply {

                text = expert.name

                setTextColor(ContextCompat.getColor(this@MainActivity, R.color.text_primary))

                textSize = 17f

                setTypeface(typeface, android.graphics.Typeface.BOLD)

                setPadding(0, dp(2), 0, dp(4))

            })

            

            // 3. 结构化档案详情行

            val detailLines = listOf(

                "身份证：" to (expert.idCard?.takeIf { it.isNotBlank() } ?: "-"),

                "手机号：" to expert.phone,

                "单　位：" to expert.company,

                "专　业：" to expert.major

            )

            detailLines.forEach { (label, value) ->

                val lineLayout = LinearLayout(this).apply {

                    orientation = LinearLayout.HORIZONTAL

                    setPadding(0, dp(1), 0, dp(1))

                }

                lineLayout.addView(TextView(this).apply {

                    text = label

                    setTextColor(ContextCompat.getColor(this@MainActivity, R.color.text_secondary))

                    textSize = 12f

                })

                lineLayout.addView(TextView(this).apply {

                    text = value

                    if (label == "手机号：" && value != "-" && value.isNotBlank()) {

                        setTextColor(ContextCompat.getColor(this@MainActivity, R.color.accent_aurora_green))

                        paintFlags = paintFlags or android.graphics.Paint.UNDERLINE_TEXT_FLAG

                        setOnClickListener {

                            try {

                                val clipboard = getSystemService(android.content.Context.CLIPBOARD_SERVICE) as android.content.ClipboardManager

                                val clip = android.content.ClipData.newPlainText("phone", value)

                                clipboard.setPrimaryClip(clip)

                                Toast.makeText(this@MainActivity, "已复制手机号：$value", Toast.LENGTH_SHORT).show()

                            } catch (e: Exception) {

                                Toast.makeText(this@MainActivity, "复制失败", Toast.LENGTH_SHORT).show()

                            }

                        }

                    } else {

                        setTextColor(ContextCompat.getColor(this@MainActivity, R.color.text_primary))

                    }

                    textSize = 12f

                })

                textBox.addView(lineLayout)

            }

        } else {

            // 没有专家匹配成功（如失败/未检测人脸）的卡片排版

            textBox.addView(TextView(this).apply {

                text = "${historyTimeFormat.format(Date(record.createdAt))}  ${statusLabel(record.status)}"

                setTextColor(statusColor(record.status))

                textSize = 14f

                setTypeface(typeface, android.graphics.Typeface.BOLD)

            })

            textBox.addView(TextView(this).apply {

                text = record.statusText

                setTextColor(ContextCompat.getColor(this@MainActivity, R.color.text_secondary))

                textSize = 12f

                setPadding(0, dp(2), 0, 0)

            })

            textBox.addView(TextView(this).apply {

                text = historyExpertSummary(record)

                setTextColor(ContextCompat.getColor(this@MainActivity, R.color.text_primary))

                textSize = 12f

                setPadding(0, dp(2), 0, 0)

            })

        }

        topRow.addView(thumb)

        topRow.addView(textBox)

        card.addView(topRow)

        val actionBox = LinearLayout(this).apply {

            orientation = LinearLayout.VERTICAL

            setPadding(0, dp(10), 0, 0)

        }

        val actionButtons = mutableListOf(

            createHistoryActionButton("原图", R.color.accent_aurora_green) {

                showOriginalImage(record)

            }

        )

        val expertPhotoPath = record.experts.firstOrNull()?.photoPath.orEmpty()

        if (record.status == STATUS_SUCCESS && expertPhotoPath.isNotBlank()) {

            actionButtons.add(

                createHistoryActionButton("专家照", R.color.button_gradient_start) {

                    showExpertOriginalImage(record)

                }

            )

        }

        actionButtons.add(

            createHistoryActionButton("重试", R.color.button_gradient_end) {

                retryRecognitionRecord(record.id)

            }

        )

        actionButtons.add(

            createHistoryActionButton("删除", R.color.accent_warning_orange) {

                deleteRecognitionRecord(record.id)

            }

        )

        addHistoryActionRows(actionBox, actionButtons)

        card.addView(actionBox)

        return card

    }

    private fun createSharedHistoryRecordView(record: SharedRecognitionRecord): View {

        val card = LinearLayout(this).apply {

            orientation = LinearLayout.VERTICAL

            setPadding(dp(14), dp(14), dp(14), dp(14))

            background = ContextCompat.getDrawable(this@MainActivity, R.drawable.bg_page_panel)

        }

        card.layoutParams = LinearLayout.LayoutParams(

            LinearLayout.LayoutParams.MATCH_PARENT,

            LinearLayout.LayoutParams.WRAP_CONTENT

        ).apply {

            bottomMargin = dp(12)

        }

        val topRow = LinearLayout(this).apply {

            orientation = LinearLayout.HORIZONTAL

            gravity = android.view.Gravity.CENTER_VERTICAL

        }

        val thumb = ImageView(this).apply {

            setLayoutParams(

                LinearLayout.LayoutParams(dp(68), dp(88)).apply {

                    setMargins(0, 0, dp(12), 0)

                }

            )

            scaleType = ImageView.ScaleType.CENTER_CROP

            background = ContextCompat.getDrawable(this@MainActivity, R.drawable.bg_preview_panel)

            tag = record.shareId

        }

        loadSharedThumbnail(record, thumb)

        val textBox = LinearLayout(this).apply {

            orientation = LinearLayout.VERTICAL

            setLayoutParams(LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f))

        }

        val expert = record.expert

        val headerRow = LinearLayout(this).apply {

            orientation = LinearLayout.HORIZONTAL

            gravity = android.view.Gravity.CENTER_VERTICAL

        }

        headerRow.addView(TextView(this).apply {

            text = historyTimeFormat.format(Date(record.createdAt))

            setTextColor(ContextCompat.getColor(this@MainActivity, R.color.text_secondary))

            textSize = 12f

        })

        headerRow.addView(TextView(this).apply {

            text = String.format(Locale.getDefault(), "  相似度 %.1f%%", expert.score)

            if (expert.score >= 85.0) {

                setTextColor(ContextCompat.getColor(this@MainActivity, R.color.accent_error_red))

            } else {

                setTextColor(ContextCompat.getColor(this@MainActivity, R.color.accent_aurora_green))

            }

            textSize = 12f

            setTypeface(typeface, android.graphics.Typeface.BOLD)

        })

        textBox.addView(headerRow)

        textBox.addView(TextView(this).apply {

            text = "由「${record.nickname.ifBlank { DEFAULT_SHARE_NICKNAME }}」共享"

            setTextColor(ContextCompat.getColor(this@MainActivity, R.color.accent_aurora_green))

            textSize = 12f

            setPadding(0, dp(2), 0, dp(2))

        })

        textBox.addView(TextView(this).apply {

            text = expert.name

            setTextColor(ContextCompat.getColor(this@MainActivity, R.color.text_primary))

            textSize = 17f

            setTypeface(typeface, android.graphics.Typeface.BOLD)

            setPadding(0, dp(2), 0, dp(4))

        })

        val detailLines = listOf(

            "身份证：" to (expert.idCard?.takeIf { it.isNotBlank() } ?: "-"),

            "手机号：" to expert.phone,

            "单　位：" to expert.company,

            "专　业：" to expert.major

        )

        detailLines.forEach { (label, value) ->

            val lineLayout = LinearLayout(this).apply {

                orientation = LinearLayout.HORIZONTAL

                setPadding(0, dp(1), 0, dp(1))

            }

            lineLayout.addView(TextView(this).apply {

                text = label

                setTextColor(ContextCompat.getColor(this@MainActivity, R.color.text_secondary))

                textSize = 12f

            })

            lineLayout.addView(TextView(this).apply {

                text = value

                if (label == "手机号：" && value != "-" && value.isNotBlank()) {

                    setTextColor(ContextCompat.getColor(this@MainActivity, R.color.accent_aurora_green))

                    paintFlags = paintFlags or android.graphics.Paint.UNDERLINE_TEXT_FLAG

                    setOnClickListener {

                        try {

                            val clipboard = getSystemService(android.content.Context.CLIPBOARD_SERVICE) as android.content.ClipboardManager

                            val clip = android.content.ClipData.newPlainText("phone", value)

                            clipboard.setPrimaryClip(clip)

                            Toast.makeText(this@MainActivity, "已复制手机号：$value", Toast.LENGTH_SHORT).show()

                        } catch (e: Exception) {

                            Toast.makeText(this@MainActivity, "复制失败", Toast.LENGTH_SHORT).show()

                        }

                    }

                } else {

                    setTextColor(ContextCompat.getColor(this@MainActivity, R.color.text_primary))

                }

                textSize = 12f

            })

            textBox.addView(lineLayout)

        }

        topRow.addView(thumb)

        topRow.addView(textBox)

        card.addView(topRow)

        val actionBox = LinearLayout(this).apply {

            orientation = LinearLayout.VERTICAL

            setPadding(0, dp(10), 0, 0)

        }

        val actionButtons = mutableListOf(

            createHistoryActionButton("原图", R.color.accent_aurora_green) {

                showSharedOriginalImage(record)

            }

        )

        if (record.expert.photoPath.isNotBlank()) {

            actionButtons.add(

                createHistoryActionButton("专家照", R.color.button_gradient_start) {

                    showExpertOriginalImage(

                        RecognitionRecord(

                            id = record.shareId,

                            createdAt = record.createdAt,

                            status = STATUS_SUCCESS,

                            statusText = "共享识别成功",

                            experts = mutableListOf(record.expert)

                        )

                    )

                }

            )

        }

        actionButtons.add(

            createHistoryActionButton("删除", R.color.accent_warning_orange) {

                deleteSharedRecognitionRecord(record.shareId)

            }

        )

        addHistoryActionRows(actionBox, actionButtons)

        card.addView(actionBox)

        return card

    }

    private fun createHistoryActionButton(textValue: String, colorRes: Int, onClick: () -> Unit): Button {

        return Button(this).apply {

            text = textValue

            textSize = 12f

            minWidth = 0

            minimumWidth = 0

            setTextColor(Color.WHITE)

            backgroundTintList = android.content.res.ColorStateList.valueOf(

                ContextCompat.getColor(this@MainActivity, colorRes)

            )

            setOnClickListener { onClick() }

        }

    }

    private fun addHistoryActionRows(container: LinearLayout, buttons: List<Button>) {

        buttons.chunked(2).forEachIndexed { rowIndex, rowButtons ->

            val row = LinearLayout(this).apply {

                orientation = LinearLayout.HORIZONTAL

                if (rowIndex > 0) {

                    setPadding(0, dp(6), 0, 0)

                }

            }

            rowButtons.forEachIndexed { index, button ->

                val params = LinearLayout.LayoutParams(0, dp(40), 1f).apply {

                    if (index > 0) {

                        marginStart = dp(8)

                    }

                }

                row.addView(button, params)

            }

            if (rowButtons.size == 1) {

                row.addView(View(this), LinearLayout.LayoutParams(0, dp(40), 1f).apply {

                    marginStart = dp(8)

                })

            }

            container.addView(row)

        }

    }

    private fun showOriginalImage(record: RecognitionRecord) {

        val originalPath = record.originalImagePath

        if (originalPath.isNullOrBlank()) {

            Toast.makeText(this, "这条记录没有保存原图", Toast.LENGTH_SHORT).show()

            recordDiagnostic("查看原图失败: originalPath为空, id=${record.id}")

            return

        }

        val originalFile = File(originalPath)

        if (!originalFile.exists()) {

            Toast.makeText(this, "原图文件不存在", Toast.LENGTH_SHORT).show()

            recordDiagnostic("查看原图失败: 文件不存在, id=${record.id}, path=$originalPath")

            return

        }

        val rawBitmap = BitmapFactory.decodeFile(
            originalPath,
            BitmapFactory.Options().apply {
                inMutable = true
                inPreferredConfig = Bitmap.Config.ARGB_8888
            }
        )

        if (rawBitmap == null) {

            Toast.makeText(this, "原图无法打开", Toast.LENGTH_SHORT).show()

            recordDiagnostic("查看原图失败: decode失败, id=${record.id}, path=$originalPath")

            return

        }

        val orientation = readExifOrientation(originalPath)

        val orientedBitmap = applyExifOrientation(rawBitmap, orientation)

        if (orientedBitmap !== rawBitmap) {

            try {

                rawBitmap.recycle()

            } catch (_: Exception) {

            }

        }

        val bitmap = if (orientedBitmap.isMutable) {

            orientedBitmap

        } else {

            orientedBitmap.copy(Bitmap.Config.ARGB_8888, true) ?: orientedBitmap

        }

        val originalFaceBoxes = originalFaceBoxesForRecord(record, bitmap.width, bitmap.height)

        if (originalFaceBoxes.isNotEmpty()) {

            drawOriginalFaceBoxes(bitmap, originalFaceBoxes)

        }

        val content = LinearLayout(this).apply {

            this.orientation = LinearLayout.VERTICAL

            setPadding(dp(12), dp(8), dp(12), 0)

        }

        content.addView(TextView(this).apply {

            text = String.format(

                Locale.getDefault(),

                "眼镜回传原图  %dx%d  %.1f KB%s",

                bitmap.width,

                bitmap.height,

                originalFile.length() / 1024f,

                if (originalFaceBoxes.isNotEmpty()) "  已用绿框标出对应人脸" else ""

            )

            setTextColor(ContextCompat.getColor(this@MainActivity, R.color.text_secondary))

            textSize = 12f

            setPadding(0, 0, 0, dp(8))

        })

        content.addView(ImageView(this).apply {

            setImageBitmap(bitmap)

            adjustViewBounds = true

            scaleType = ImageView.ScaleType.FIT_CENTER

            setBackgroundColor(ContextCompat.getColor(this@MainActivity, R.color.bg_dark))

            layoutParams = LinearLayout.LayoutParams(

                LinearLayout.LayoutParams.MATCH_PARENT,

                LinearLayout.LayoutParams.WRAP_CONTENT

            )

        })

        val scrollView = ScrollView(this).apply {

            addView(content)

        }

        val dialog = AlertDialog.Builder(this)

            .setTitle("查看原图")

            .setView(scrollView)

            .setPositiveButton("关闭", null)

            .create()

        dialog.setOnShowListener {

            dialog.window?.setLayout(

                (resources.displayMetrics.widthPixels * 0.94f).toInt(),

                LinearLayout.LayoutParams.WRAP_CONTENT

            )

        }

        dialog.show()

        recordDiagnostic(
            "查看原图: id=${record.id}, size=${bitmap.width}x${bitmap.height}, " +
                "bytes=${originalFile.length()}, faceBoxes=${originalFaceBoxes.size}, " +
                "faceRectImage=${record.faceRectImageWidth}x${record.faceRectImageHeight}, " +
                "uploadSource=${record.uploadSourceRect?.let { "${it.x},${it.y},${it.width},${it.height}" } ?: "null"}"
        )

    }

    private fun showSharedOriginalImage(record: SharedRecognitionRecord) {

        if (record.originalUrl.isBlank()) {

            Toast.makeText(this, "这条共享记录没有原图", Toast.LENGTH_SHORT).show()

            recordDiagnostic("查看共享原图失败: originalUrl为空, shareId=${record.shareId}")

            return

        }

        val url = expertPhotoUrl(record.originalUrl)

        Toast.makeText(this, "正在打开共享原图...", Toast.LENGTH_SHORT).show()

        recordDiagnostic("开始查看共享原图: shareId=${record.shareId}, from=${record.nickname}, url=$url")

        executeWorker("打开共享原图") {

            val cachedBytes = loadSharedOriginalCacheBytes(record)

            if (cachedBytes != null) {

                renderSharedOriginalImage(record, cachedBytes, fromCache = true)

                return@executeWorker

            }

            val downloadedBytes = downloadSharedOriginalImageBytes(record, url, reportUserErrors = true)

                ?: return@executeWorker

            saveSharedOriginalCacheBytes(record, downloadedBytes)

            renderSharedOriginalImage(record, downloadedBytes, fromCache = false)

        }

    }

    private fun renderSharedOriginalImage(record: SharedRecognitionRecord, bytes: ByteArray, fromCache: Boolean) {

        val decodedBitmap = BitmapFactory.decodeByteArray(
            bytes,
            0,
            bytes.size,
            BitmapFactory.Options().apply {
                inMutable = true
                inPreferredConfig = Bitmap.Config.ARGB_8888
            }
        )

        if (decodedBitmap == null) {

            runOnUiThread {

                Toast.makeText(this@MainActivity, "共享原图无法打开", Toast.LENGTH_SHORT).show()

            }

            recordDiagnostic("共享原图解码失败: shareId=${record.shareId}, bytes=${bytes.size}, fromCache=$fromCache")

            return

        }

        val bitmap = if (decodedBitmap.isMutable) {

            decodedBitmap

        } else {

            decodedBitmap.copy(Bitmap.Config.ARGB_8888, true) ?: decodedBitmap

        }

        val originalFaceBoxes = originalFaceBoxesForRecord(

            sharedRecordToRecognitionRecordForFaceBoxes(record),

            bitmap.width,

            bitmap.height

        )

        if (originalFaceBoxes.isNotEmpty()) {

            drawOriginalFaceBoxes(bitmap, originalFaceBoxes)

        }

        runOnUiThread {

            showBitmapDialog(

                title = "查看共享原图",

                summary = "由「${record.nickname.ifBlank { DEFAULT_SHARE_NICKNAME }}」共享  ${bitmap.width}x${bitmap.height}  %.1f KB%s%s".format(

                    Locale.getDefault(),

                    bytes.size / 1024f,

                    if (originalFaceBoxes.isNotEmpty()) "  已用绿框标出对应人脸" else "",

                    if (fromCache) "  本机缓存" else ""

                ),

                bitmap = bitmap

            )

        }

        recordDiagnostic(

            "查看共享原图: shareId=${record.shareId}, from=${record.nickname}, " +

                "size=${bitmap.width}x${bitmap.height}, bytes=${bytes.size}, fromCache=$fromCache, " +

                "faceBoxes=${originalFaceBoxes.size}, " +

                "faceRectImage=${record.faceRectImageWidth}x${record.faceRectImageHeight}, " +

                "uploadSource=${record.uploadSourceRect?.let { "${it.x},${it.y},${it.width},${it.height}" } ?: "null"}"

        )

    }

    private fun downloadSharedOriginalImageBytes(
        record: SharedRecognitionRecord,
        url: String,
        reportUserErrors: Boolean
    ): ByteArray? {

        val request = try {

            Request.Builder().url(url).get().build()

        } catch (e: Exception) {

            if (reportUserErrors) {

                runOnUiThread {

                    Toast.makeText(this@MainActivity, "共享原图地址无效", Toast.LENGTH_SHORT).show()

                }

            }

            recordDiagnostic("共享原图请求构建失败: shareId=${record.shareId}, url=$url", e)

            return null

        }

        return try {

            okHttpClient.newCall(request).execute().use { response ->

                if (!response.isSuccessful) {

                    if (reportUserErrors) {

                        runOnUiThread {

                            Toast.makeText(this@MainActivity, "共享原图加载失败: HTTP ${response.code}", Toast.LENGTH_SHORT).show()

                        }

                    }

                    recordDiagnostic("共享原图 HTTP 失败: shareId=${record.shareId}, code=${response.code}, url=$url")

                    return null

                }

                val bytes = response.body?.bytes()

                if (bytes == null || bytes.isEmpty()) {

                    if (reportUserErrors) {

                        runOnUiThread {

                            Toast.makeText(this@MainActivity, "共享原图为空", Toast.LENGTH_SHORT).show()

                        }

                    }

                    recordDiagnostic("共享原图为空: shareId=${record.shareId}, url=$url")

                    return null

                }

                bytes

            }

        } catch (e: Exception) {

            if (reportUserErrors) {

                runOnUiThread {

                    Toast.makeText(this@MainActivity, "共享原图加载失败", Toast.LENGTH_SHORT).show()

                }

            }

            recordDiagnostic("共享原图网络失败: shareId=${record.shareId}, url=$url", e)

            null

        }

    }

    private fun prefetchRecentSharedOriginalImages() {

        if (!recordShareEnabled) {

            return

        }

        val now = System.currentTimeMillis()

        val candidates = synchronized(sharedRecognitionRecords) {

            sharedRecognitionRecords

                .filter { it.originalUrl.isNotBlank() && it.expiresAt > now }

                .sortedByDescending { it.createdAt }

                .take(SHARED_ORIGINAL_PREFETCH_LIMIT)

        }

        if (candidates.isEmpty()) {

            cleanupSharedOriginalCache()

            return

        }

        executeWorker("预取共享原图缓存") {

            cleanupSharedOriginalCache()

            candidates.forEach { record ->

                if (loadSharedOriginalCacheBytes(record) != null) {

                    return@forEach

                }

                if (!sharedOriginalCacheInFlight.add(record.shareId)) {

                    return@forEach

                }

                try {

                    val url = expertPhotoUrl(record.originalUrl)

                    val bytes = downloadSharedOriginalImageBytes(record, url, reportUserErrors = false)

                    if (bytes != null) {

                        saveSharedOriginalCacheBytes(record, bytes)

                        recordDiagnostic(

                            "共享原图已预取缓存: shareId=${record.shareId}, bytes=${bytes.size}, from=${record.nickname}"

                        )

                    }

                } finally {

                    sharedOriginalCacheInFlight.remove(record.shareId)

                }

            }

        }

    }

    private fun loadSharedOriginalCacheBytes(record: SharedRecognitionRecord): ByteArray? {

        if (record.expiresAt <= System.currentTimeMillis()) {

            deleteSharedOriginalCacheFile(record.shareId)

            return null

        }

        val cacheFile = sharedOriginalCacheFile(record.shareId)

        if (!cacheFile.exists() || cacheFile.length() <= 0L) {

            return null

        }

        return try {

            cacheFile.readBytes()

        } catch (e: Exception) {

            recordDiagnostic("读取共享原图缓存失败: shareId=${record.shareId}, path=${cacheFile.absolutePath}", e)

            try {

                cacheFile.delete()

            } catch (_: Exception) {

            }

            null

        }

    }

    private fun saveSharedOriginalCacheBytes(record: SharedRecognitionRecord, bytes: ByteArray) {

        if (bytes.isEmpty() || record.expiresAt <= System.currentTimeMillis()) {

            return

        }

        val cacheFile = sharedOriginalCacheFile(record.shareId)

        try {

            cacheFile.parentFile?.mkdirs()

            cacheFile.writeBytes(bytes)

        } catch (e: Exception) {

            recordDiagnostic("写入共享原图缓存失败: shareId=${record.shareId}, path=${cacheFile.absolutePath}", e)

        }

    }

    private fun cleanupSharedOriginalCache(activeRecords: List<SharedRecognitionRecord>? = null) {

        val dir = sharedOriginalCacheDir()

        val files = dir.listFiles() ?: return

        val now = System.currentTimeMillis()

        val activeShareIds = activeRecords

            ?.filter { it.expiresAt > now }

            ?.map { it.shareId }

            ?.toSet()

            ?: synchronized(sharedRecognitionRecords) {

                sharedRecognitionRecords

                    .filter { it.expiresAt > now }

                    .map { it.shareId }

                    .toSet()

            }

        files.forEach { file ->

            val shareId = file.name.removeSuffix(SHARED_ORIGINAL_CACHE_SUFFIX)

            val staleByAge = now - file.lastModified() > SHARED_DELETED_ID_RETENTION_MS

            if (shareId !in activeShareIds || staleByAge) {

                try {

                    file.delete()

                } catch (e: Exception) {

                    recordDiagnostic("清理共享原图缓存失败: path=${file.absolutePath}", e)

                }

            }

        }

    }

    private fun deleteSharedOriginalCacheFile(shareId: String) {

        try {

            sharedOriginalCacheFile(shareId).delete()

        } catch (e: Exception) {

            recordDiagnostic("删除共享原图缓存失败: shareId=$shareId", e)

        }

    }

    private fun sharedOriginalCacheFile(shareId: String): File {

        val safeName = shareId

            .ifBlank { "unknown" }

            .map { ch -> if (ch.isLetterOrDigit() || ch == '-' || ch == '_') ch else '_' }

            .joinToString(separator = "")

        return File(sharedOriginalCacheDir(), safeName + SHARED_ORIGINAL_CACHE_SUFFIX)

    }

    private fun sharedOriginalCacheDir(): File {

        return File(cacheDir, SHARED_ORIGINAL_CACHE_DIR).apply {

            if (!exists()) {

                mkdirs()

            }

        }

    }

    private fun sharedRecordToRecognitionRecordForFaceBoxes(record: SharedRecognitionRecord): RecognitionRecord {

        return RecognitionRecord(

            id = record.shareId,

            createdAt = record.createdAt,

            originalWidth = record.originalWidth,

            originalHeight = record.originalHeight,

            uploadWidth = record.uploadWidth,

            uploadHeight = record.uploadHeight,

            faceRectImageWidth = record.faceRectImageWidth,

            faceRectImageHeight = record.faceRectImageHeight,

            uploadSourceRect = record.uploadSourceRect,

            experts = mutableListOf(record.expert)

        )

    }

    private fun originalFaceBoxesForRecord(
        record: RecognitionRecord,
        actualOriginalWidth: Int,
        actualOriginalHeight: Int
    ): List<Rect> {
        if (actualOriginalWidth <= 0 || actualOriginalHeight <= 0) {
            return emptyList()
        }
        val expertRect = record.experts.firstOrNull()?.faceRect
            ?: record.localFaceRects.firstOrNull()
            ?: return emptyList()
        val faceRectImageWidth = record.faceRectImageWidth
            .takeIf { it > 0 }
            ?: record.uploadWidth.takeIf { it > 0 }
            ?: return emptyList()
        val faceRectImageHeight = record.faceRectImageHeight
            .takeIf { it > 0 }
            ?: record.uploadHeight.takeIf { it > 0 }
            ?: return emptyList()
        val faceOnUpload = expertRect.toPixelRect(faceRectImageWidth, faceRectImageHeight)
            ?: return emptyList()
        val logicalOriginalWidth = record.originalWidth.takeIf { it > 0 } ?: actualOriginalWidth
        val logicalOriginalHeight = record.originalHeight.takeIf { it > 0 } ?: actualOriginalHeight
        val uploadSourceRect = record.uploadSourceRect
        val useActualOriginalAsSourceReference = uploadSourceRect?.let {
            shouldUseActualOriginalSizeForUploadSourceRect(
                rect = it,
                logicalOriginalWidth = logicalOriginalWidth,
                logicalOriginalHeight = logicalOriginalHeight,
                actualOriginalWidth = actualOriginalWidth,
                actualOriginalHeight = actualOriginalHeight
            )
        } ?: false
        val sourceReferenceWidth = if (useActualOriginalAsSourceReference) {
            actualOriginalWidth
        } else {
            logicalOriginalWidth
        }
        val sourceReferenceHeight = if (useActualOriginalAsSourceReference) {
            actualOriginalHeight
        } else {
            logicalOriginalHeight
        }
        val sourceOnOriginal = uploadSourceRect?.toPixelRect(sourceReferenceWidth, sourceReferenceHeight)
            ?: inferFullImageUploadSourceRect(
                faceRectImageWidth = faceRectImageWidth,
                faceRectImageHeight = faceRectImageHeight,
                logicalOriginalWidth = sourceReferenceWidth,
                logicalOriginalHeight = sourceReferenceHeight
            )
            ?: run {
                recordDiagnostic(
                    "查看原图绿框跳过: 缺少上传图原图裁剪区域, id=${record.id}, " +
                        "faceRectImage=${faceRectImageWidth}x$faceRectImageHeight, " +
                        "original=${logicalOriginalWidth}x$logicalOriginalHeight"
                )
                return emptyList()
            }
        if (sourceOnOriginal.width() <= 0 || sourceOnOriginal.height() <= 0) {
            return emptyList()
        }
        val logicalLeft = sourceOnOriginal.left +
            faceOnUpload.left.toFloat() / faceRectImageWidth.toFloat() * sourceOnOriginal.width().toFloat()
        val logicalTop = sourceOnOriginal.top +
            faceOnUpload.top.toFloat() / faceRectImageHeight.toFloat() * sourceOnOriginal.height().toFloat()
        val logicalRight = sourceOnOriginal.left +
            faceOnUpload.right.toFloat() / faceRectImageWidth.toFloat() * sourceOnOriginal.width().toFloat()
        val logicalBottom = sourceOnOriginal.top +
            faceOnUpload.bottom.toFloat() / faceRectImageHeight.toFloat() * sourceOnOriginal.height().toFloat()
        val scaleX = actualOriginalWidth.toFloat() / sourceReferenceWidth.toFloat().coerceAtLeast(1f)
        val scaleY = actualOriginalHeight.toFloat() / sourceReferenceHeight.toFloat().coerceAtLeast(1f)
        val rect = Rect(
            (logicalLeft * scaleX).roundToInt().coerceIn(0, actualOriginalWidth),
            (logicalTop * scaleY).roundToInt().coerceIn(0, actualOriginalHeight),
            (logicalRight * scaleX).roundToInt().coerceIn(0, actualOriginalWidth),
            (logicalBottom * scaleY).roundToInt().coerceIn(0, actualOriginalHeight)
        )
        if (rect.width() <= 0 || rect.height() <= 0) {
            return emptyList()
        }
        if (useActualOriginalAsSourceReference) {
            recordDiagnostic(
                "查看原图绿框使用实际图片尺寸映射: id=${record.id}, " +
                    "storedOriginal=${logicalOriginalWidth}x$logicalOriginalHeight, " +
                    "actual=${actualOriginalWidth}x$actualOriginalHeight, " +
                    "source=${uploadSourceRect?.x},${uploadSourceRect?.y}," +
                    "${uploadSourceRect?.width},${uploadSourceRect?.height}"
            )
        }
        return listOf(rect)
    }

    private fun shouldUseActualOriginalSizeForUploadSourceRect(
        rect: FaceRect,
        logicalOriginalWidth: Int,
        logicalOriginalHeight: Int,
        actualOriginalWidth: Int,
        actualOriginalHeight: Int
    ): Boolean {
        if (rect.isNormalized() ||
            logicalOriginalWidth <= 0 ||
            logicalOriginalHeight <= 0 ||
            actualOriginalWidth <= 0 ||
            actualOriginalHeight <= 0
        ) {
            return false
        }
        if (logicalOriginalWidth == actualOriginalWidth && logicalOriginalHeight == actualOriginalHeight) {
            return false
        }
        val rectRight = rect.x + rect.width
        val rectBottom = rect.y + rect.height
        val fitsActual = rect.x >= -2f &&
            rect.y >= -2f &&
            rectRight <= actualOriginalWidth + 2f &&
            rectBottom <= actualOriginalHeight + 2f
        if (!fitsActual) {
            return false
        }
        val swappedDimensions = kotlin.math.abs(logicalOriginalWidth - actualOriginalHeight) <= 2 &&
            kotlin.math.abs(logicalOriginalHeight - actualOriginalWidth) <= 2
        val logicalRatio = logicalOriginalWidth.toFloat() / logicalOriginalHeight.toFloat().coerceAtLeast(1f)
        val actualRatio = actualOriginalWidth.toFloat() / actualOriginalHeight.toFloat().coerceAtLeast(1f)
        val aspectMismatch = kotlin.math.abs(logicalRatio - actualRatio) > 0.08f
        return swappedDimensions || aspectMismatch
    }

    private fun inferFullImageUploadSourceRect(
        faceRectImageWidth: Int,
        faceRectImageHeight: Int,
        logicalOriginalWidth: Int,
        logicalOriginalHeight: Int
    ): Rect? {
        if (faceRectImageWidth <= 0 || faceRectImageHeight <= 0 ||
            logicalOriginalWidth <= 0 || logicalOriginalHeight <= 0
        ) {
            return null
        }
        val sameWidth = kotlin.math.abs(faceRectImageWidth - logicalOriginalWidth) <= 2
        val sameHeight = kotlin.math.abs(faceRectImageHeight - logicalOriginalHeight) <= 2
        return if (sameWidth && sameHeight) {
            Rect(0, 0, logicalOriginalWidth, logicalOriginalHeight)
        } else {
            null
        }
    }

    private fun drawOriginalFaceBoxes(bitmap: Bitmap, boxes: List<Rect>) {
        if (boxes.isEmpty()) {
            return
        }
        if (!bitmap.isMutable) {
            recordDiagnostic("查看原图绿框跳过: bitmap不可变, size=${bitmap.width}x${bitmap.height}")
            return
        }
        val canvas = Canvas(bitmap)
        val stroke = maxOf(2f, minOf(bitmap.width, bitmap.height) * 0.0018f)
        val paint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            color = Color.rgb(0, 220, 90)
            style = Paint.Style.STROKE
            strokeWidth = stroke
        }
        boxes.forEach { box ->
            canvas.drawRect(box, paint)
        }
    }

    private fun showExpertOriginalImage(record: RecognitionRecord) {

        val expert = record.experts.firstOrNull()

        if (expert == null || expert.photoPath.isBlank()) {

            Toast.makeText(this, "这条记录没有专家照片", Toast.LENGTH_SHORT).show()

            recordDiagnostic("查看专家原图失败: photoPath为空, id=${record.id}")

            return

        }

        val url = expertPhotoUrl(expert.photoPath)

        Toast.makeText(this, "正在加载专家照片...", Toast.LENGTH_SHORT).show()

        recordDiagnostic("开始查看专家原图: id=${record.id}, name=${expert.name}, url=$url")

        val request = Request.Builder().url(url).build()

        okHttpClient.newCall(request).enqueue(object : Callback {

            override fun onFailure(call: Call, e: IOException) {

                recordDiagnostic("查看专家原图网络失败: id=${record.id}, url=$url", e)

                runOnUiThread {

                    Toast.makeText(this@MainActivity, "专家照片加载失败", Toast.LENGTH_SHORT).show()

                }

            }

            override fun onResponse(call: Call, response: Response) {

                response.use {

                    if (!it.isSuccessful) {

                        recordDiagnostic("查看专家原图 HTTP 失败: id=${record.id}, code=${it.code}, url=$url")

                        runOnUiThread {

                            Toast.makeText(this@MainActivity, "专家照片加载失败: HTTP ${it.code}", Toast.LENGTH_SHORT).show()

                        }

                        return

                    }

                    val bytes = it.body?.bytes()

                    if (bytes == null || bytes.isEmpty()) {

                        recordDiagnostic("查看专家原图失败: 空响应, id=${record.id}, url=$url")

                        runOnUiThread {

                            Toast.makeText(this@MainActivity, "专家照片为空", Toast.LENGTH_SHORT).show()

                        }

                        return

                    }

                    val bitmap = BitmapFactory.decodeByteArray(bytes, 0, bytes.size)

                    if (bitmap == null) {

                        recordDiagnostic("查看专家原图失败: decode失败, id=${record.id}, bytes=${bytes.size}, url=$url")

                        runOnUiThread {

                            Toast.makeText(this@MainActivity, "专家照片无法打开", Toast.LENGTH_SHORT).show()

                        }

                        return

                    }

                    runOnUiThread {

                        showBitmapDialog(

                            title = "专家原图",

                            summary = "${expert.name}  ${bitmap.width}x${bitmap.height}  %.1f KB".format(Locale.getDefault(), bytes.size / 1024f),

                            bitmap = bitmap

                        )

                    }

                    recordDiagnostic(

                        "查看专家原图: id=${record.id}, name=${expert.name}, " +

                            "size=${bitmap.width}x${bitmap.height}, bytes=${bytes.size}"

                    )

                }

            }

        })

    }

    private fun showBitmapDialog(title: String, summary: String, bitmap: Bitmap) {

        val content = LinearLayout(this).apply {

            orientation = LinearLayout.VERTICAL

            setPadding(dp(12), dp(8), dp(12), 0)

        }

        content.addView(TextView(this).apply {

            text = summary

            setTextColor(ContextCompat.getColor(this@MainActivity, R.color.text_secondary))

            textSize = 12f

            setPadding(0, 0, 0, dp(8))

        })

        content.addView(ImageView(this).apply {

            setImageBitmap(bitmap)

            adjustViewBounds = true

            scaleType = ImageView.ScaleType.FIT_CENTER

            setBackgroundColor(ContextCompat.getColor(this@MainActivity, R.color.bg_dark))

            layoutParams = LinearLayout.LayoutParams(

                LinearLayout.LayoutParams.MATCH_PARENT,

                LinearLayout.LayoutParams.WRAP_CONTENT

            )

        })

        val scrollView = ScrollView(this).apply {

            addView(content)

        }

        val dialog = AlertDialog.Builder(this)

            .setTitle(title)

            .setView(scrollView)

            .setPositiveButton("关闭", null)

            .create()

        dialog.setOnShowListener {

            dialog.window?.setLayout(

                (resources.displayMetrics.widthPixels * 0.94f).toInt(),

                LinearLayout.LayoutParams.WRAP_CONTENT

            )

        }

        dialog.show()

    }

    private fun historyExpertSummary(record: RecognitionRecord): String {

        return when {

            record.experts.isNotEmpty() -> "识别到 ${record.experts.size} 位：${record.experts.joinToString("，") { it.name }}"

            !record.errorMessage.isNullOrEmpty() -> humanReadableCloudError(record.errorMessage ?: "")

            else -> "照片：${record.uploadWidth.takeIf { it > 0 } ?: record.originalWidth}x${record.uploadHeight.takeIf { it > 0 } ?: record.originalHeight}"

        }

    }

    private fun cloudErrorMessage(responseCode: Int, bodyString: String): String {

        val decoded = humanReadableCloudError(bodyString)

        return if (responseCode > 0 && decoded.isNotBlank()) {

            "HTTP $responseCode: $decoded"

        } else if (responseCode > 0) {

            "HTTP $responseCode: 云端未返回匹配结果"

        } else {

            decoded.ifBlank { "云端未返回匹配结果" }

        }

    }

    private fun humanReadableCloudError(rawMessage: String): String {

        val trimmed = rawMessage.trim()

        if (trimmed.isEmpty()) {

            return ""

        }

        val httpMatch = Regex("^HTTP\\s+(\\d+):\\s*(.*)$").find(trimmed)

        if (httpMatch != null) {

            val code = httpMatch.groupValues[1]

            val body = httpMatch.groupValues[2]

            val decodedBody = decodeCloudErrorBody(body)

            return "HTTP $code: ${decodedBody ?: body}"

        }

        return decodeCloudErrorBody(trimmed) ?: trimmed

    }

    private fun decodeCloudErrorBody(bodyString: String): String? {

        val trimmed = bodyString.trim()

        if (!trimmed.startsWith("{")) {

            return null

        }

        return try {

            val bodyObj = Gson().fromJson(trimmed, JsonObject::class.java)

            val messageKeys = arrayOf("error", "message", "msg", "detail")

            messageKeys.firstNotNullOfOrNull { key ->

                val value = bodyObj.get(key)

                if (value != null && !value.isJsonNull) {

                    value.asString.takeIf { it.isNotBlank() }

                } else {

                    null

                }

            }

        } catch (e: Exception) {

            null

        }

    }

    private fun statusLabel(status: String): String {

        return when (status) {

            STATUS_CAPTURING -> "正在拍照"

            STATUS_LOCAL_PROCESSING -> "本地检测中"

            STATUS_UPLOADING -> "正在识别"

            STATUS_SUCCESS -> "识别成功"

            STATUS_NO_FACE -> "未检测到人脸"

            STATUS_NO_MATCH -> "未匹配"

            STATUS_FAILED -> "失败"

            STATUS_INTERRUPTED -> "可重试"

            else -> status

        }

    }

    private fun statusColor(status: String): Int {

        val colorRes = when (status) {

            STATUS_SUCCESS -> R.color.accent_aurora_green

            STATUS_CAPTURING, STATUS_LOCAL_PROCESSING, STATUS_UPLOADING -> R.color.accent_warning_orange

            else -> R.color.text_secondary

        }

        return ContextCompat.getColor(this, colorRes)

    }

    private fun dp(value: Int): Int {

        return (value * resources.displayMetrics.density).toInt()

    }

    /**

     * 3. 记录并处理 Android 系统转发到手机端 App 的按键事件。

     */

    override fun dispatchKeyEvent(event: KeyEvent): Boolean {

        if (event.action == KeyEvent.ACTION_DOWN) {

            val keyCode = event.keyCode

            val keyName = KeyEvent.keyCodeToString(keyCode)

            val deviceName = event.device?.name ?: "unknown"

            recordDiagnostic(

                "收到系统按键事件: keyCode=$keyCode, keyName=$keyName, " +

                    "scanCode=${event.scanCode}, repeat=${event.repeatCount}, " +

                    "source=${event.source}, device=$deviceName"

            )

            

            // 镜腿向前滑动 / 音量加键 -> 轮播到下个专家卡片

            if (keyCode == KeyEvent.KEYCODE_VOLUME_UP || keyCode == KeyEvent.KEYCODE_DPAD_RIGHT) {

                showNextExpert()

                return true

            } 

            // 镜腿向后滑动 / 音量减键 -> 轮播到上个专家卡片

            else if (keyCode == KeyEvent.KEYCODE_VOLUME_DOWN || keyCode == KeyEvent.KEYCODE_DPAD_LEFT) {

                showPrevExpert()

                return true

            }

            else if (keyCode == KeyEvent.KEYCODE_CAMERA ||

                keyCode == KeyEvent.KEYCODE_ENTER ||

                keyCode == KeyEvent.KEYCODE_DPAD_CENTER) {

                triggerCaptureFromExternalEvent("系统按键 $keyName")

                return true

            }

        }

        return super.dispatchKeyEvent(event)

    }

    /**

     * 4. 无线流连接：通过 CXR-L 协议建立协同链路

     */

    private fun requestCxrAuthorizationAndConnect() {

        try {

            recordDiagnostic("开始 Rokid 授权检查: runtime=${runtimePermissionStatus()}")

            val authHelper = AuthorizationHelper

            val hasRequiredRokidApp = authHelper.isRequiredRokidAppInstalled(this) ||

                authHelper.isRequiredHiRokidInstalled(this)

            recordDiagnostic(

                "Rokid 官方 App 状态: required=${authHelper.isRequiredRokidAppInstalled(this)}, " +

                    "hi=${authHelper.isRequiredHiRokidInstalled(this)}, connectHi=${authHelper.isConnectHiRokid()}"

            )

            if (!hasRequiredRokidApp) {

                updateStatus("请先安装/升级 Rokid AI 或 Hi Rokid App，并完成眼镜无线连接", isWorking = false)

                return

            }

            val authResult = authHelper.requestAuthorization(

                this,

                REQUIRED_GLASS_PERMISSIONS,

                REQUEST_CODE_CXR_AUTH

            )

            recordDiagnostic(

                "requestAuthorization 返回: direct=${authResult != null}, " +

                    "code=${authResult?.first}, hasIntent=${authResult?.second != null}, glassPerm=${glassPermissionStatus()}"

            )

            if (authResult?.first == Activity.RESULT_OK && authResult.second != null) {

                handleCxrAuthorizationResult(authResult.first, authResult.second)

            } else {

                updateStatus("等待 Rokid 官方 App 授权眼镜相机/媒体权限...", isWorking = false)

            }

        } catch (e: Exception) {

            Log.e(TAG, "CXR-L authorization request failed", e)

            recordDiagnostic("CXR-L 授权初始化异常", e)

            updateStatus("CXR-L 授权初始化失败: ${e.message}", isWorking = false)

        }

    }

    private fun handleCxrAuthorizationResult(resultCode: Int, data: Intent?) {

        recordDiagnostic("处理 Rokid 授权结果: resultCode=$resultCode, hasData=${data != null}")

        when (val result = AuthorizationHelper.parseAuthorizationResult(resultCode, data)) {

            is AuthResult.AuthSuccess -> {

                cxrAuthToken = result.token

                recordDiagnostic("Rokid 授权成功: tokenLength=${result.token.length}, glassPerm=${glassPermissionStatus()}")

                initCxrLink(result.token)

            }

            is AuthResult.AuthCancel -> {

                recordDiagnostic("Rokid 授权取消")

                updateStatus("已取消 Rokid 眼镜授权，无法启动无线拍照", isWorking = false)

            }

            is AuthResult.AuthFail -> {

                recordDiagnostic("Rokid 授权失败: glassPerm=${glassPermissionStatus()}")

                updateStatus("Rokid 眼镜授权失败，请在官方 App 中确认权限", isWorking = false)

            }

            else -> {

                recordDiagnostic("Rokid 授权返回未知状态: ${result?.javaClass?.name}")

                updateStatus("Rokid 眼镜授权返回未知状态，请重试", isWorking = false)

            }

        }

    }

    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {

        super.onActivityResult(requestCode, resultCode, data)

        if (requestCode == REQUEST_CODE_CXR_AUTH) {

            handleCxrAuthorizationResult(resultCode, data)

        } else if (requestCode == REQUEST_CODE_PICK_VIDEO) {

            if (resultCode == Activity.RESULT_OK) {

                handlePickedVideo(data)

            } else {

                recordDiagnostic("系统视频选择器取消: resultCode=$resultCode")

            }

        } else if (requestCode == REQUEST_CODE_PICK_IMAGE) {

            if (resultCode == Activity.RESULT_OK) {

                handlePickedImage(data)

            } else {

                recordDiagnostic("系统图片选择器取消: resultCode=$resultCode")

            }

        }

    }

    private fun initCxrLink(authToken: String = cxrAuthToken ?: "") {

        if (authToken.isEmpty()) {

            updateStatus("缺少 Rokid 授权 token，无法连接眼镜", isWorking = false)

            return

        }

        try {

            updateStatus("正在通过官方 CXR-L 无线链路连接眼镜...", isWorking = false)

            recordDiagnostic("初始化 CXR-L: tokenPresent=${authToken.isNotEmpty()}, tokenLength=${authToken.length}")

            cxrLink?.disconnect()

            cxrLink = null

            isCxrServiceConnected = false

            isGlassWirelessConnected = false

            

            val link = CXRLink(applicationContext)

            cxrLink = link

            val sessionConfigured = link.configCXRSession(

                CxrDefs.CXRSession(CxrDefs.CXRSessionType.CUSTOMVIEW)

            )

            Log.i(TAG, "CXR-L session configured: $sessionConfigured")

            recordDiagnostic("CXR-L 会话配置: type=CUSTOMVIEW, result=$sessionConfigured")

            if (!sessionConfigured) {

                cxrLink = null

                updateStatus("CXR-L 会话配置失败，请重新授权连接", isWorking = false)

                return

            }

            link.apply {

                recordDiagnostic("当前 CUSTOMVIEW 会话未启用眼镜端物理按键转发；物理键需 CUSTOMAPP + 眼镜端 App")

                setCXRLinkCbk(object : ICXRLinkCbk {

                    override fun onCXRLConnected(connected: Boolean) {

                        isCxrServiceConnected = connected

                        isGlassWirelessConnected = if (connected) {

                            try {

                                link.isGlassBtConnected()

                            } catch (e: Exception) {

                                recordDiagnostic("读取眼镜蓝牙连接状态异常", e)

                                false

                            }

                        } else {

                            false

                        }

                        recordDiagnostic(

                            "CXR-L 服务回调: serviceConnected=$connected, " +

                                "glassBtConnected=$isGlassWirelessConnected, glassPerm=${glassPermissionStatus()}"

                        )

                        runOnUiThread {

                            if (connected) {

                                if (isGlassWirelessConnected) {

                                    updateStatus("CXR-L 无线链路已就绪，可触发眼镜拍照", isWorking = false)

                                    Toast.makeText(this@MainActivity, "眼镜无线链路已就绪", Toast.LENGTH_SHORT).show()

                                } else {

                                    updateStatus("已连接 Rokid 服务，请在官方 App 中确认眼镜已无线连接", isWorking = false)

                                }

                            } else {

                                updateStatus("眼镜无线链路已断开，请检查 Rokid 官方 App 连接状态", isWorking = false)

                                hideArOverlay()

                            }

                        }

                    }

                    override fun onGlassBtConnected(connected: Boolean) {

                        isGlassWirelessConnected = connected

                        recordDiagnostic("眼镜无线连接回调: connected=$connected")

                        runOnUiThread {

                            if (connected) {

                                updateStatus("眼镜无线连接已建立，可触发拍照核验", isWorking = false)

                            } else {

                                updateStatus("眼镜无线连接已断开，请在 Rokid 官方 App 中重新连接", isWorking = false)

                            }

                        }

                    }

                    override fun onGlassDeviceInfo(info: GlassInfo) {

                        Log.i(TAG, "Glass device info: $info")

                        recordDiagnostic("眼镜设备信息回调: $info")

                    }

                    override fun onGlassWearingStatus(wearing: Boolean) {

                        recordDiagnostic("眼镜佩戴状态回调: wearing=$wearing")

                    }

                    override fun onGlassAiAssistStart() {

                        recordDiagnostic("收到 CXR-L AI 对话开始事件: onGlassAiAssistStart，仅记录不触发抓拍")

                    }

                    override fun onGlassAiAssistStop() {

                        recordDiagnostic("收到 CXR-L AI 对话结束事件: onGlassAiAssistStop")

                    }

                    override fun onGlassAiInterrupt(interrupt: Boolean) {

                        recordDiagnostic("眼镜 AI 打断状态: interrupt=$interrupt")

                    }

                })

                

                // 监听眼镜端的图像流

                setCXRImageCbk(object : IImageStreamCbk {

                    override fun onImageReceived(data: ByteArray?) {

                        recordDiagnostic(

                            "眼镜图片回调: bytes=${data?.size ?: 0}, pendingCapture=$pendingGlassCapture, " +

                                "matching=$isMatchingRequestRunning"

                        )

                        data?.let {

                            val frameBytes = it.copyOf()

                            latestFrameBytes = frameBytes

                            val lateTaskId = timedOutCaptureTaskId

                            val acceptsLateCapture = !pendingGlassCapture &&

                                lateTaskId != null &&

                                System.currentTimeMillis() <= timedOutCaptureAcceptUntil

                            if (pendingGlassCapture || acceptsLateCapture) {

                                val captureTaskId = if (pendingGlassCapture) activeCaptureTaskId else lateTaskId

                                val isLateCapture = acceptsLateCapture && !pendingGlassCapture

                                val callbackCostMs = if (activeCaptureRequestStartedAt > 0L) {

                                    System.currentTimeMillis() - activeCaptureRequestStartedAt

                                } else {

                                    -1L

                                }

                                val requestBrief = "${activeCaptureRequestWidth}x$activeCaptureRequestHeight q=$activeCaptureRequestQuality"

                                pendingGlassCapture = false

                                activeCaptureTaskId = null

                                if (isLateCapture) {

                                    timedOutCaptureTaskId = null

                                    timedOutCaptureAcceptUntil = 0L

                                }

                                isMatchingRequestRunning = false

                                mainHandler.removeCallbacks(glassCaptureTimeoutRunnable)

                                updateRecognitionRecord(captureTaskId) {

                                    it.status = STATUS_LOCAL_PROCESSING

                                    it.statusText = if (isLateCapture) {

                                        "超时后收到眼镜照片，正在本地检测人脸"

                                    } else {

                                        "已收到眼镜照片，正在本地检测人脸"

                                    }

                                    it.errorMessage = null

                                }

                                recordDiagnostic(

                                    "处理${if (isLateCapture) "迟到" else "正常"}抓拍图片: " +

                                        "recordId=$captureTaskId, request=$requestBrief, callbackCostMs=$callbackCostMs, bytes=${frameBytes.size}"

                                )

                                processCapturedFrameForMatch(captureTaskId, frameBytes)

                            } else {

                                // 非抓拍帧只用于预览，避免抓拍主路径重复解码同一张图。

                                val bitmap = BitmapFactory.decodeByteArray(frameBytes, 0, frameBytes.size)

                                runOnUiThread {

                                    if (bitmap != null) {

                                        binding.ivPreview.setImageBitmap(bitmap)

                                    }

                                }

                            }

                        }

                    }

                    override fun onImageError(code: Int, msg: String?) {

                        if (pendingGlassCapture) {

                            val errorTaskId = activeCaptureTaskId

                            pendingGlassCapture = false

                            activeCaptureTaskId = null

                            isMatchingRequestRunning = false

                            mainHandler.removeCallbacks(glassCaptureTimeoutRunnable)

                            updateRecognitionRecord(errorTaskId) {

                                it.status = STATUS_FAILED

                                it.statusText = "眼镜图像流异常"

                                it.errorMessage = msg ?: "code=$code"

                            }

                        }

                        Log.e(TAG, "CXR Image Stream Error: $msg")

                        recordDiagnostic("眼镜图像流异常: code=$code, msg=${msg ?: "-"}")

                        runOnUiThread {

                            updateStatus("眼镜图像流异常: ${msg ?: code}", isWorking = false)

                        }

                    }

                })

                

                // 发起连接

                val bindStarted = connect(authToken)

                recordDiagnostic("CXR-L bindService 发起: result=$bindStarted")

                if (!bindStarted) {

                    updateStatus("CXR-L 媒体流服务连接失败，请确认官方 App 已启动", isWorking = false)

                }

            }

        } catch (e: Exception) {

            Log.e(TAG, "CXR-L Link init failed", e)

            recordDiagnostic("CXR-L 初始化异常", e)

            updateStatus("CXR-L 初始化失败: ${e.message}", isWorking = false)

        }

    }

    /**

     * 5. 抓拍方案：通过 CXR-L 无线命令触发眼镜拍照，拿到回调帧后再本地初筛与上传

     */

    private fun takePhotoAndMatch() {

        recordDiagnostic(

            "准备抓拍: service=$isCxrServiceConnected, glass=$isGlassWirelessConnected, " +

                "matching=$isMatchingRequestRunning, pending=$pendingGlassCapture, token=${cxrAuthToken != null}"

        )

        if (pendingGlassCapture || isMatchingRequestRunning) {

            Toast.makeText(this, "正在等待上一张照片回传，请稍候", Toast.LENGTH_SHORT).show()

            recordDiagnostic("抓拍被忽略: 上一次眼镜拍照尚未回传")

            return

        }

        playCaptureBeep()

        val link = cxrLink

        if (link == null || !isCxrServiceConnected) {

            Toast.makeText(this, "CXR-L 服务尚未连接，请先完成 Rokid 授权", Toast.LENGTH_SHORT).show()

            recordDiagnostic("抓拍前检查失败: linkNull=${link == null}, serviceConnected=$isCxrServiceConnected")

            playResultBeep(success = false)

            requestCxrAuthorizationAndConnect()

            return

        }

        val permissionCheckStartedAt = System.currentTimeMillis()

        val hasCameraGlassPermission = try {

            AuthorizationHelper.hasGlassPermission(GlassPermission.CAMERA)

        } catch (e: Exception) {

            recordDiagnostic("读取 Rokid CAMERA 权限异常", e)

            false

        }

        recordDiagnostic("抓拍前权限检查完成: camera=$hasCameraGlassPermission, costMs=${System.currentTimeMillis() - permissionCheckStartedAt}")

        if (!hasCameraGlassPermission) {

            recordDiagnostic("抓拍前检查失败: Rokid CAMERA 权限无效, glassPerm=${glassPermissionStatus()}")

            updateStatus("Rokid 眼镜相机授权已失效，请重新授权后再拍照", isWorking = false)

            playResultBeep(success = false)

            requestCxrAuthorizationAndConnect()

            return

        }

        val connectionCheckStartedAt = System.currentTimeMillis()

        val usedCachedGlassConnection = isGlassWirelessConnected

        val glassConnected = if (usedCachedGlassConnection) {

            true

        } else {

            try {

                link.isGlassBtConnected()

            } catch (e: Exception) {

                recordDiagnostic("抓拍前读取眼镜连接状态异常", e)

                false

            }

        }

        isGlassWirelessConnected = glassConnected

        recordDiagnostic("抓拍前连接检查完成: glass=$glassConnected, costMs=${System.currentTimeMillis() - connectionCheckStartedAt}, usedCached=$usedCachedGlassConnection")

        if (!glassConnected) {

            val record = createRecognitionRecord()

            updateRecognitionRecord(record.id) {

                it.status = STATUS_FAILED

                it.statusText = "眼镜未无线连接"

                it.errorMessage = "请先在 Rokid 官方 App 中连接眼镜"

            }

            recordDiagnostic("抓拍前检查失败: isGlassBtConnected=false")

            updateStatus("眼镜未无线连接，请先在 Rokid 官方 App 中连接眼镜", isWorking = false)

            playResultBeep(success = false)

            return

        }

        val record = createRecognitionRecord()

        val requestWidth = glassCaptureWidth

        val requestHeight = glassCaptureHeight

        val requestQuality = glassCaptureQuality

        recordDiagnostic("抓拍记录创建完成: id=${record.id}")

        isMatchingRequestRunning = true

        pendingGlassCapture = true

        activeCaptureTaskId = record.id

        timedOutCaptureTaskId = null

        timedOutCaptureAcceptUntil = 0L

        activeCaptureRequestStartedAt = System.currentTimeMillis()

        activeCaptureRequestWidth = requestWidth

        activeCaptureRequestHeight = requestHeight

        activeCaptureRequestQuality = requestQuality

        activeCaptureTimeoutMs = captureTimeoutMsFor(requestWidth, requestHeight)

        capturedFrameBytes = null

        lastLocalFaceCrop = null

        updateStatus("正在通过无线链路触发眼镜拍照...", isWorking = true)

        recordDiagnostic(

            "调用 CXR takePhoto: width=$requestWidth, height=$requestHeight, " +

                "quality=$requestQuality"

        )

        val requested = try {

            link.takePhoto(requestWidth, requestHeight, requestQuality)

        } catch (e: Exception) {

            Log.e(TAG, "CXR takePhoto failed", e)

            recordDiagnostic("CXR takePhoto 抛出异常", e)

            false

        }

        recordDiagnostic("CXR takePhoto 返回: requested=$requested")

        if (!requested) {

            pendingGlassCapture = false

            activeCaptureTaskId = null

            isMatchingRequestRunning = false

            updateRecognitionRecord(record.id) {

                it.status = STATUS_FAILED

                it.statusText = "眼镜拍照请求失败"

                it.errorMessage = "CXR-L takePhoto 返回 false"

            }

            Log.w(

                TAG,

                "CXR takePhoto returned false. serviceConnected=$isCxrServiceConnected, " +

                    "glassConnected=$isGlassWirelessConnected, hasCameraPermission=$hasCameraGlassPermission"

            )

            recordDiagnostic(

                "抓拍请求失败详情: service=$isCxrServiceConnected, glass=$isGlassWirelessConnected, " +

                    "cameraPerm=$hasCameraGlassPermission, glassPerm=${glassPermissionStatus()}"

            )

            updateStatus("眼镜拍照请求失败，请检查 CXR-L 权限和无线连接", isWorking = false)

            playResultBeep(success = false)

            return

        }

        mainHandler.removeCallbacks(glassCaptureTimeoutRunnable)

        mainHandler.postDelayed(glassCaptureTimeoutRunnable, activeCaptureTimeoutMs)

        recordDiagnostic("抓拍请求已发送，等待图片回调，timeoutMs=$activeCaptureTimeoutMs")

    }

    private fun captureTimeoutMsFor(width: Int, height: Int): Long {

        val megapixels = width.toLong() * height.toLong()

        return when {

            megapixels >= 10_000_000L -> 30000L

            megapixels >= 5_000_000L -> 22000L

            else -> GLASS_CAPTURE_TIMEOUT_MS

        }

    }

    private fun processCapturedFrameForMatch(
        recordId: String?,
        bytes: ByteArray,
        sourceLabel: String = "抓拍帧",
        processInline: Boolean = false
    ) {
        capturedFrameBytes = bytes // 锁存抓拍的一帧数据，防止网络延迟后流画面更新导致裁剪错位
        recordDiagnostic("开始处理$sourceLabel: bytes=${bytes.size}")
        if (recordId != null) {
            updateRecognitionRecord(recordId) {
                it.status = STATUS_LOCAL_PROCESSING
                it.statusText = "正在本地检测人脸"
            }
        }

        runOnUiThread {

            val statusText = if (sourceLabel.contains("图库")) {

                "已读取图库照片，正在本地检测人脸..."

            } else {

                "已收到眼镜照片，正在本地检测人脸..."

            }

            updateStatus(statusText, isWorking = true)

        }

        val processFrame = processFrame@{

            try {

                var decoded = decodeBitmapForProcessing(bytes, sourceLabel, processingMaxSideFor(sourceLabel))

                if (decoded == null) {

                    updateRecognitionRecord(recordId) {

                        it.status = STATUS_FAILED

                        it.statusText = "图片解析失败"

                        it.errorMessage = "图片字节无法解码"

                    }

                    recordDiagnostic("$sourceLabel 解析失败: bytes=${bytes.size}")

                    if (!sourceLabel.contains("图库")) {

                        runOnUiThread {

                            playResultBeep(success = false)

                            updateStatus("❌ 图片解析失败", isWorking = false)

                        }

                    }

                    return@processFrame

                }

                var bitmap = decoded.bitmap

                recordDiagnostic(

                    "$sourceLabel 解析成功: bitmap=${bitmap.width}x${bitmap.height}, " +

                        "bytes=${bytes.size}, sample=${decoded.sampleSize}, exif=${decoded.exifOrientation}, " +

                        "requested=${activeCaptureRequestWidth}x$activeCaptureRequestHeight q=$activeCaptureRequestQuality"

                )

                val inputImage = InputImage.fromBitmap(bitmap, 0)

                var faces = Tasks.await(faceDetector.process(inputImage))

                if (faces.isEmpty() && sourceLabel.contains("图库") && decoded.sampleSize > 1) {

                    recordDiagnostic(

                        "图库低分辨率未检测到人脸，尝试高分辨率重检: sample=${decoded.sampleSize}, " +

                            "bitmap=${bitmap.width}x${bitmap.height}"

                    )

                    val highResDecoded = decodeBitmapForProcessing(

                        bytes,

                        sourceLabel,

                        GALLERY_RETRY_PROCESS_MAX_IMAGE_SIDE

                    )

                    if (highResDecoded != null && highResDecoded.sampleSize < decoded.sampleSize) {

                        bitmap.recycle()

                        decoded = highResDecoded

                        bitmap = decoded.bitmap

                        faces = Tasks.await(faceDetector.process(InputImage.fromBitmap(bitmap, 0)))

                        recordDiagnostic(

                            "图库高分辨率重检完成: faces=${faces.size}, bitmap=${bitmap.width}x${bitmap.height}, " +

                                "sample=${decoded.sampleSize}, exif=${decoded.exifOrientation}"

                        )

                    } else {

                        highResDecoded?.bitmap?.recycle()

                    }

                }

                if (faces.isEmpty()) {

                    val retryMaxSide = if (sourceLabel.contains("图库")) {

                        GALLERY_RETRY_PROCESS_MAX_IMAGE_SIDE

                    } else {

                        IMAGE_SENSITIVE_RETRY_PROCESS_MAX_SIDE

                    }

                    var sensitiveDecoded: DecodedBitmap? = null

                    if (decoded.sampleSize > 1 && maxOf(bitmap.width, bitmap.height) < retryMaxSide) {

                        sensitiveDecoded = decodeBitmapForProcessing(

                            bytes,

                            "$sourceLabel 敏感补检",

                            retryMaxSide

                        )

                    }

                    val fallbackBitmap = sensitiveDecoded?.bitmap ?: bitmap

                    val sensitiveFaces = Tasks.await(

                        sensitiveFaceDetector.process(InputImage.fromBitmap(fallbackBitmap, 0))

                    )

                    if (sensitiveFaces.isNotEmpty()) {

                        if (sensitiveDecoded != null) {

                            bitmap.recycle()

                            decoded = sensitiveDecoded

                            bitmap = decoded.bitmap

                        }

                        faces = sensitiveFaces

                        recordDiagnostic(

                            "$sourceLabel 敏感补检命中: faces=${faces.size}, bitmap=${bitmap.width}x${bitmap.height}, " +

                                "sample=${decoded.sampleSize}, maxSide=$retryMaxSide"

                        )

                    } else {

                        recordDiagnostic(

                            "$sourceLabel 敏感补检未命中: bitmap=${fallbackBitmap.width}x${fallbackBitmap.height}, " +

                                "sample=${sensitiveDecoded?.sampleSize ?: decoded.sampleSize}"

                        )

                        sensitiveDecoded?.bitmap?.recycle()

                    }

                }

                if (sourceLabel.contains("图库") && shouldRunGallerySupplementalFaceDetection(decoded, bitmap, faces)) {

                    recordDiagnostic(

                        "图库疑似小脸或多人漏检，启动高分辨率补检: faces=${faces.size}, " +

                            "bitmap=${bitmap.width}x${bitmap.height}, sample=${decoded.sampleSize}"

                    )

                    val supplementalDecoded = decodeBitmapForProcessing(

                        bytes,

                        "$sourceLabel 小脸补检",

                        GALLERY_RETRY_PROCESS_MAX_IMAGE_SIDE

                    )

                    if (supplementalDecoded != null && supplementalDecoded.sampleSize < decoded.sampleSize) {

                        val supplementalFaces = Tasks.await(

                            sensitiveFaceDetector.process(InputImage.fromBitmap(supplementalDecoded.bitmap, 0))

                        )

                        if (supplementalFaces.size > faces.size) {

                            bitmap.recycle()

                            decoded = supplementalDecoded

                            bitmap = decoded.bitmap

                            faces = supplementalFaces

                            recordDiagnostic(

                                "图库高分辨率补检采用: faces=${faces.size}, bitmap=${bitmap.width}x${bitmap.height}, " +

                                    "sample=${decoded.sampleSize}"

                            )

                        } else {

                            supplementalDecoded.bitmap.recycle()

                            recordDiagnostic(

                                "图库高分辨率补检未增加人脸: originalFaces=${faces.size}, supplementalFaces=${supplementalFaces.size}"

                            )

                        }

                    } else {

                        supplementalDecoded?.bitmap?.recycle()

                        recordDiagnostic("图库高分辨率补检跳过: 无更高分辨率可用")

                    }

                }

                updateRecognitionRecord(recordId) {

                    it.originalWidth = decoded.originalWidth

                    it.originalHeight = decoded.originalHeight

                }

                runOnUiThread {

                    binding.ivPreview.setImageBitmap(bitmap)

                }

                recordDiagnostic("本地人脸检测完成: faces=${faces.size}")
                handleLocalFaceDetectionResult(recordId, bitmap, faces, sourceLabel, bytes, decoded)

            } catch (e: Exception) {

                Log.e(TAG, "Capture frame error", e)

                updateRecognitionRecord(recordId) {

                    it.status = STATUS_FAILED

                    it.statusText = "图片处理或本地人脸检测异常"

                    it.errorMessage = e.message

                }

                recordDiagnostic("$sourceLabel 处理异常", e)

                if (!sourceLabel.contains("图库")) {

                    runOnUiThread {

                        playResultBeep(success = false)

                        updateStatus("❌ 图片处理异常: ${e.message}", isWorking = false)

                    }

                }

            }

        }

        if (processInline) {
            if (recordId != null) {
                saveOriginalImageForRecordAsync(recordId, bytes, sourceLabel)
            }
            processFrame()
        } else {
            executeWorker("处理$sourceLabel", processFrame)
            if (recordId != null) {
                saveOriginalImageForRecordAsync(recordId, bytes, sourceLabel)
            }
        }

    }

    private fun saveOriginalImageForRecordAsync(recordId: String, bytes: ByteArray, sourceLabel: String) {
        executeWorker("保存$sourceLabel 原图") {
            try {
                if (findRecognitionRecord(recordId) == null) {
                    recordDiagnostic("$sourceLabel 原图保存跳过: 记录已不存在, id=$recordId")
                    return@executeWorker
                }
                val historyBytes = if (sourceLabel.contains("图库") && bytes.size > 3 * 1024 * 1024) {
                    compressLargeImage(bytes, 2560, 85)
                } else {
                    bytes
                }
                val originalPath = saveHistoryImage(recordId, "original", historyBytes)
                updateRecognitionRecord(recordId) {
                    it.originalImagePath = originalPath
                }
                recordDiagnostic(
                    "$sourceLabel 原图后台保存完成: id=$recordId, sourceBytes=${bytes.size}, " +
                        "savedBytes=${historyBytes.size}"
                )
            } catch (e: Exception) {
                recordDiagnostic("$sourceLabel 原图后台保存异常: id=$recordId", e)
            }
        }
    }

    /**

     * 5.1 手机端本地初筛：无脸不上云；有脸则裁剪人脸区域后再上传，减少无效云端调用。

     */

    private fun handleLocalFaceDetectionResult(
        recordId: String?,
        sourceBitmap: Bitmap,
        faces: List<Face>,
        sourceLabel: String = "抓拍帧",
        originalBytes: ByteArray? = null,
        decodedMeta: DecodedBitmap? = null
    ) {

        val isGallery = sourceLabel.contains("图库")

        if (faces.isEmpty()) {

            updateRecognitionRecord(recordId) {

                it.status = STATUS_NO_FACE

                it.statusText = "未检测到人脸"

                it.errorMessage = "本地检测未发现人脸，未调用云端接口"

            }

            recordDiagnostic("本地人脸初筛 ($sourceLabel): 未检测到人脸，停止云端请求")

            if (!isGallery) {

                runOnUiThread {

                    playResultBeep(success = false)

                    updateStatus("未检测到人脸，已取消云端识别", isWorking = false)

                    Toast.makeText(this, "未检测到人脸，请调整视角后重试", Toast.LENGTH_SHORT).show()

                }

            }

            return

        }

        if (isGallery) {

            galleryBatchFaceCount += 1

        }

        try {
            val uploadMaxSide = uploadMaxSideFor(faces.size)

            var uploadBitmap: Bitmap
            var cropRect: Rect
            var localFaceRects: List<FaceRect>

            val highResCrop = if (originalBytes != null && decodedMeta != null && decodedMeta.sampleSize > 1) {
                cropHighResFaces(originalBytes, decodedMeta, sourceBitmap, faces, uploadMaxSide)
            } else null

            if (highResCrop != null) {
                uploadBitmap = highResCrop.bitmap
                cropRect = highResCrop.sourceCropRect
                localFaceRects = highResCrop.localFaceRects
            } else {
                val faceBounds = buildFaceUnionBounds(sourceBitmap, faces)
                val uploadImage = buildFaceUploadImage(sourceBitmap, faces, faceBounds, uploadMaxSide)
                uploadBitmap = uploadImage.bitmap
                cropRect = uploadImage.sourceCropRect
                localFaceRects = uploadImage.localFaceRects
            }

            val uploadBytes = bitmapToJpegBytes(uploadBitmap, FACE_UPLOAD_JPEG_QUALITY)

            val logicalOriginalWidth = decodedMeta?.originalWidth ?: sourceBitmap.width
            val logicalOriginalHeight = decodedMeta?.originalHeight ?: sourceBitmap.height
            val uploadSourceRectForRecord = if (highResCrop != null) {
                faceRectFromPixelRect(cropRect)
            } else {
                scalePixelRectToFaceRect(
                    rect = cropRect,
                    fromWidth = sourceBitmap.width,
                    fromHeight = sourceBitmap.height,
                    toWidth = logicalOriginalWidth,
                    toHeight = logicalOriginalHeight
                ) ?: faceRectFromPixelRect(cropRect)
            }

            recordDiagnostic(
                "本地人脸预处理 ($sourceLabel): faces=${faces.size}, source=${sourceBitmap.width}x${sourceBitmap.height}, " +
                    "crop=${cropRect.left},${cropRect.top}," +
                    "${cropRect.right},${cropRect.bottom}, " +
                    "upload=${uploadBitmap.width}x${uploadBitmap.height}, minSide=${minOf(uploadBitmap.width, uploadBitmap.height)}, " +
                    "bytes=${uploadBytes.size}, quality=$FACE_UPLOAD_JPEG_QUALITY, maxSide=$uploadMaxSide, " +
                    "localUploadRects=${localFaceRects.size}, " +
                    "uploadSource=${uploadSourceRectForRecord.x},${uploadSourceRectForRecord.y}," +
                    "${uploadSourceRectForRecord.width},${uploadSourceRectForRecord.height}"
            )

            capturedFrameBytes = uploadBytes
            lastLocalFaceCrop = uploadBitmap

            if (recordId != null) {
                updateRecognitionRecord(recordId) {
                    it.uploadImagePath = saveHistoryImage(recordId, "upload", uploadBytes)
                    it.uploadWidth = uploadBitmap.width
                    it.uploadHeight = uploadBitmap.height
                    it.faceRectImageWidth = uploadBitmap.width
                    it.faceRectImageHeight = uploadBitmap.height
                    it.uploadSourceRect = uploadSourceRectForRecord
                    it.localFaceRects.clear()
                    it.localFaceRects.addAll(localFaceRects)
                    it.status = STATUS_UPLOADING
                    it.statusText = "正在上传云端识别"
                    it.errorMessage = null
                }
            }

            val base64Data = Base64.encodeToString(uploadBytes, Base64.NO_WRAP)

            val formattedBase64 = "data:image/jpeg;base64,$base64Data"

            if (!isGallery) {

                runOnUiThread {

                    val status = if (faces.size > 1) {

                        "本地检测到${faces.size}张人脸，正在上传人脸区域..."

                    } else {

                        "本地检测到人脸，正在上传识别..."

                    }

                    updateStatus(status, isWorking = true)

                }

            }

            val maxFaceNum = cloudMaxFaceNumFor(faces.size)

            recordDiagnostic("云端识别参数 ($sourceLabel): localFaces=${faces.size}, maxFaceNum=$maxFaceNum")

            postFaceSearchRequest(recordId, formattedBase64, maxFaceNum, sourceLabel)

        } catch (e: Exception) {

            Log.e(TAG, "Local face preprocessing failed", e)

            updateRecognitionRecord(recordId) {

                it.status = STATUS_FAILED

                it.statusText = "本地人脸预处理失败"

                it.errorMessage = e.message

            }

            recordDiagnostic("本地人脸预处理异常 ($sourceLabel)", e)

            if (!isGallery) {

                runOnUiThread {

                    playResultBeep(success = false)

                    updateStatus("❌ 本地人脸预处理失败: ${e.message}", isWorking = false)

                }

            }

        }

    }

    private fun buildFaceUnionBounds(sourceBitmap: Bitmap, faces: List<Face>): Rect {

        var left = sourceBitmap.width

        var top = sourceBitmap.height

        var right = 0

        var bottom = 0

        faces.forEach { face ->

            val bounds = Rect(face.boundingBox)

            bounds.left = bounds.left.coerceIn(0, sourceBitmap.width)

            bounds.top = bounds.top.coerceIn(0, sourceBitmap.height)

            bounds.right = bounds.right.coerceIn(0, sourceBitmap.width)

            bounds.bottom = bounds.bottom.coerceIn(0, sourceBitmap.height)

            if (bounds.width() > 0 && bounds.height() > 0) {

                left = minOf(left, bounds.left)

                top = minOf(top, bounds.top)

                right = maxOf(right, bounds.right)

                bottom = maxOf(bottom, bounds.bottom)

            }

        }

        if (right <= left || bottom <= top) {

            return Rect(0, 0, sourceBitmap.width, sourceBitmap.height)

        }

        return Rect(left, top, right, bottom)

    }

    private fun compressLargeImage(bytes: ByteArray, maxSide: Int, quality: Int): ByteArray {
        try {
            val options = BitmapFactory.Options().apply { inJustDecodeBounds = true }
            BitmapFactory.decodeByteArray(bytes, 0, bytes.size, options)
            val sampleSize = calculateInSampleSize(options.outWidth, options.outHeight, maxSide)
            val decodeOptions = BitmapFactory.Options().apply { inSampleSize = sampleSize }
            val rawBitmap = BitmapFactory.decodeByteArray(bytes, 0, bytes.size, decodeOptions) ?: return bytes
            val exif = readExifOrientation(bytes)
            val oriented = applyExifOrientation(rawBitmap, exif)
            if (oriented !== rawBitmap) rawBitmap.recycle()

            val maxDim = maxOf(oriented.width, oriented.height)
            val finalBitmap = if (maxDim > maxSide) {
                val scale = maxSide.toFloat() / maxDim
                val scaled = Bitmap.createScaledBitmap(oriented, (oriented.width * scale).toInt(), (oriented.height * scale).toInt(), true)
                oriented.recycle()
                scaled
            } else {
                oriented
            }

            val out = ByteArrayOutputStream()
            finalBitmap.compress(Bitmap.CompressFormat.JPEG, quality, out)
            finalBitmap.recycle()
            return out.toByteArray()
        } catch (e: Exception) {
            recordDiagnostic("压缩超大历史原图失败", e)
            return bytes
        }
    }

    private fun mapRectToUnrotated(rect: Rect, rotatedW: Int, rotatedH: Int, orientation: Int): Rect {
        val isSwapped = orientation == ExifInterface.ORIENTATION_TRANSPOSE ||
                orientation == ExifInterface.ORIENTATION_ROTATE_90 ||
                orientation == ExifInterface.ORIENTATION_TRANSVERSE ||
                orientation == ExifInterface.ORIENTATION_ROTATE_270
        val unrotatedW = if (isSwapped) rotatedH else rotatedW
        val unrotatedH = if (isSwapped) rotatedW else rotatedH

        fun mapPoint(x: Int, y: Int): Pair<Int, Int> {
            return when (orientation) {
                ExifInterface.ORIENTATION_FLIP_HORIZONTAL -> Pair(unrotatedW - x, y)
                ExifInterface.ORIENTATION_ROTATE_180 -> Pair(unrotatedW - x, unrotatedH - y)
                ExifInterface.ORIENTATION_FLIP_VERTICAL -> Pair(x, unrotatedH - y)
                ExifInterface.ORIENTATION_TRANSPOSE -> Pair(y, x)
                ExifInterface.ORIENTATION_ROTATE_90 -> Pair(y, unrotatedW - x)
                ExifInterface.ORIENTATION_TRANSVERSE -> Pair(unrotatedH - y, unrotatedW - x)
                ExifInterface.ORIENTATION_ROTATE_270 -> Pair(unrotatedH - y, x)
                else -> Pair(x, y)
            }
        }

        val p1 = mapPoint(rect.left, rect.top)
        val p2 = mapPoint(rect.right, rect.top)
        val p3 = mapPoint(rect.right, rect.bottom)
        val p4 = mapPoint(rect.left, rect.bottom)

        val uMin = minOf(p1.first, p2.first, p3.first, p4.first)
        val vMin = minOf(p1.second, p2.second, p3.second, p4.second)
        val uMax = maxOf(p1.first, p2.first, p3.first, p4.first)
        val vMax = maxOf(p1.second, p2.second, p3.second, p4.second)

        return Rect(uMin, vMin, uMax, vMax)
    }

    private fun cropHighResFaces(
        originalBytes: ByteArray,
        decodedMeta: DecodedBitmap,
        detectionBitmap: Bitmap,
        faces: List<Face>,
        uploadMaxSide: Int
    ): FaceUploadImage? {
        try {
            val faceBounds = buildFaceUnionBounds(detectionBitmap, faces)
            val padX = (faceBounds.width() * FACE_CROP_HORIZONTAL_PADDING).toInt()
            val padTop = (faceBounds.height() * FACE_CROP_TOP_PADDING).toInt()
            val padBottom = (faceBounds.height() * FACE_CROP_BOTTOM_PADDING).toInt()

            val detLeft = (faceBounds.left - padX).coerceAtLeast(0)
            val detTop = (faceBounds.top - padTop).coerceAtLeast(0)
            val detRight = (faceBounds.right + padX).coerceAtMost(detectionBitmap.width)
            val detBottom = (faceBounds.bottom + padBottom).coerceAtMost(detectionBitmap.height)

            val detCropRect = if (detRight <= detLeft || detBottom <= detTop) {
                Rect(0, 0, detectionBitmap.width, detectionBitmap.height)
            } else {
                expandRectToMinimumSide(Rect(detLeft, detTop, detRight, detBottom), detectionBitmap.width, detectionBitmap.height, MIN_UPLOAD_IMAGE_SIDE)
            }

            val displayCropRect = Rect(
                (detCropRect.left.toFloat() / detectionBitmap.width.toFloat() * decodedMeta.originalWidth).roundToInt()
                    .coerceIn(0, decodedMeta.originalWidth),
                (detCropRect.top.toFloat() / detectionBitmap.height.toFloat() * decodedMeta.originalHeight).roundToInt()
                    .coerceIn(0, decodedMeta.originalHeight),
                (detCropRect.right.toFloat() / detectionBitmap.width.toFloat() * decodedMeta.originalWidth).roundToInt()
                    .coerceIn(0, decodedMeta.originalWidth),
                (detCropRect.bottom.toFloat() / detectionBitmap.height.toFloat() * decodedMeta.originalHeight).roundToInt()
                    .coerceIn(0, decodedMeta.originalHeight)
            )

            val unrotatedDetRect = mapRectToUnrotated(detCropRect, detectionBitmap.width, detectionBitmap.height, decodedMeta.exifOrientation)

            val isSwapped = decodedMeta.exifOrientation == ExifInterface.ORIENTATION_TRANSPOSE ||
                    decodedMeta.exifOrientation == ExifInterface.ORIENTATION_ROTATE_90 ||
                    decodedMeta.exifOrientation == ExifInterface.ORIENTATION_TRANSVERSE ||
                    decodedMeta.exifOrientation == ExifInterface.ORIENTATION_ROTATE_270
            val unrotatedDetW = if (isSwapped) detectionBitmap.height else detectionBitmap.width
            val unrotatedDetH = if (isSwapped) detectionBitmap.width else detectionBitmap.height

            val scaleX = decodedMeta.originalWidth.toFloat() / unrotatedDetW.toFloat()
            val scaleY = decodedMeta.originalHeight.toFloat() / unrotatedDetH.toFloat()

            val origLeft = (unrotatedDetRect.left * scaleX).toInt().coerceAtLeast(0)
            val origTop = (unrotatedDetRect.top * scaleY).toInt().coerceAtLeast(0)
            val origRight = (unrotatedDetRect.right * scaleX).toInt().coerceAtMost(decodedMeta.originalWidth)
            val origBottom = (unrotatedDetRect.bottom * scaleY).toInt().coerceAtMost(decodedMeta.originalHeight)
            val origCropRect = Rect(origLeft, origTop, origRight, origBottom)

            if (origCropRect.width() <= 0 || origCropRect.height() <= 0) return null

            val decoder = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
                BitmapRegionDecoder.newInstance(originalBytes, 0, originalBytes.size)
            } else {
                @Suppress("DEPRECATION")
                BitmapRegionDecoder.newInstance(originalBytes, 0, originalBytes.size, false)
            } ?: return null

            var sampleSize = 1
            while (origCropRect.width() / (sampleSize * 2) >= uploadMaxSide && origCropRect.height() / (sampleSize * 2) >= uploadMaxSide) {
                sampleSize *= 2
            }

            val options = BitmapFactory.Options().apply {
                inSampleSize = sampleSize
                inPreferredConfig = Bitmap.Config.ARGB_8888
            }

            val rawCropped = decoder.decodeRegion(origCropRect, options)
            decoder.recycle()
            if (rawCropped == null) return null

            val finalCropped = applyExifOrientation(rawCropped, decodedMeta.exifOrientation)
            if (finalCropped !== rawCropped) rawCropped.recycle()

            val maxDim = maxOf(finalCropped.width, finalCropped.height)
            val uploadBitmap = if (maxDim > uploadMaxSide) {
                val scale = uploadMaxSide.toFloat() / maxDim
                val scaled = Bitmap.createScaledBitmap(finalCropped, (finalCropped.width * scale).toInt(), (finalCropped.height * scale).toInt(), true)
                finalCropped.recycle()
                scaled
            } else {
                finalCropped
            }

            val scaleDetX = uploadBitmap.width.toFloat() / detCropRect.width().toFloat()
            val scaleDetY = uploadBitmap.height.toFloat() / detCropRect.height().toFloat()
            val localFaceRects = faces
                .sortedWith(compareBy<Face> { it.boundingBox.left }.thenBy { it.boundingBox.top })
                .mapNotNull { face ->
                    mapLocalFaceToUploadRect(face.boundingBox, detCropRect, scaleDetX, scaleDetY, uploadBitmap.width, uploadBitmap.height)
                }

            return FaceUploadImage(uploadBitmap, displayCropRect, localFaceRects)
        } catch (e: Exception) {
            recordDiagnostic("高清图库区域解码失败", e)
            return null
        }
    }

    private fun buildFaceUploadImage(

        sourceBitmap: Bitmap,

        faces: List<Face>,

        faceBounds: Rect,

        maxUploadSide: Int

    ): FaceUploadImage {

        val padX = (faceBounds.width() * FACE_CROP_HORIZONTAL_PADDING).toInt()

        val padTop = (faceBounds.height() * FACE_CROP_TOP_PADDING).toInt()

        val padBottom = (faceBounds.height() * FACE_CROP_BOTTOM_PADDING).toInt()

        val left = (faceBounds.left - padX).coerceAtLeast(0)

        val top = (faceBounds.top - padTop).coerceAtLeast(0)

        val right = (faceBounds.right + padX).coerceAtMost(sourceBitmap.width)

        val bottom = (faceBounds.bottom + padBottom).coerceAtMost(sourceBitmap.height)

        val cropRect = if (right <= left || bottom <= top) {

            Rect(0, 0, sourceBitmap.width, sourceBitmap.height)

        } else {

            expandRectToMinimumSide(

                Rect(left, top, right, bottom),

                sourceBitmap.width,

                sourceBitmap.height,

                MIN_UPLOAD_IMAGE_SIDE

            )

        }

        val cropped = Bitmap.createBitmap(sourceBitmap, cropRect.left, cropRect.top, cropRect.width(), cropRect.height())

        val uploadBitmap = resizeBitmapForUpload(cropped, maxUploadSide)

        val scaleX = uploadBitmap.width.toFloat() / cropRect.width().toFloat()

        val scaleY = uploadBitmap.height.toFloat() / cropRect.height().toFloat()

        val localFaceRects = faces

            .sortedWith(compareBy<Face> { it.boundingBox.left }.thenBy { it.boundingBox.top })

            .mapNotNull { face ->

                mapLocalFaceToUploadRect(face.boundingBox, cropRect, scaleX, scaleY, uploadBitmap.width, uploadBitmap.height)

            }

        return FaceUploadImage(uploadBitmap, cropRect, localFaceRects)

    }

    private fun mapLocalFaceToUploadRect(

        faceBounds: Rect,

        cropRect: Rect,

        scaleX: Float,

        scaleY: Float,

        uploadWidth: Int,

        uploadHeight: Int

    ): FaceRect? {

        val left = faceBounds.left.coerceIn(cropRect.left, cropRect.right)

        val top = faceBounds.top.coerceIn(cropRect.top, cropRect.bottom)

        val right = faceBounds.right.coerceIn(cropRect.left, cropRect.right)

        val bottom = faceBounds.bottom.coerceIn(cropRect.top, cropRect.bottom)

        if (right <= left || bottom <= top) {

            return null

        }

        val mappedLeft = ((left - cropRect.left) * scaleX).coerceIn(0f, uploadWidth.toFloat())

        val mappedTop = ((top - cropRect.top) * scaleY).coerceIn(0f, uploadHeight.toFloat())

        val mappedRight = ((right - cropRect.left) * scaleX).coerceIn(0f, uploadWidth.toFloat())

        val mappedBottom = ((bottom - cropRect.top) * scaleY).coerceIn(0f, uploadHeight.toFloat())

        if (mappedRight <= mappedLeft || mappedBottom <= mappedTop) {

            return null

        }

        return FaceRect(

            x = mappedLeft,

            y = mappedTop,

            width = mappedRight - mappedLeft,

            height = mappedBottom - mappedTop

        )

    }

    private fun expandRectToMinimumSide(rect: Rect, imageWidth: Int, imageHeight: Int, minSide: Int): Rect {

        var left = rect.left.coerceIn(0, imageWidth)

        var top = rect.top.coerceIn(0, imageHeight)

        var right = rect.right.coerceIn(0, imageWidth)

        var bottom = rect.bottom.coerceIn(0, imageHeight)

        if (right <= left || bottom <= top) {

            return Rect(0, 0, imageWidth, imageHeight)

        }

        if (right - left < minSide) {

            val extra = minSide - (right - left)

            left -= extra / 2

            right += extra - extra / 2

            if (left < 0) {

                right = (right - left).coerceAtMost(imageWidth)

                left = 0

            }

            if (right > imageWidth) {

                left = (left - (right - imageWidth)).coerceAtLeast(0)

                right = imageWidth

            }

        }

        if (bottom - top < minSide) {

            val extra = minSide - (bottom - top)

            top -= extra / 2

            bottom += extra - extra / 2

            if (top < 0) {

                bottom = (bottom - top).coerceAtMost(imageHeight)

                top = 0

            }

            if (bottom > imageHeight) {

                top = (top - (bottom - imageHeight)).coerceAtLeast(0)

                bottom = imageHeight

            }

        }

        return Rect(left, top, right, bottom)

    }

    private fun resizeBitmapForUpload(bitmap: Bitmap, maxUploadSide: Int): Bitmap {

        var result = bitmap

        val currentMaxSide = maxOf(result.width, result.height)

        if (currentMaxSide > maxUploadSide) {

            val scale = maxUploadSide.toFloat() / currentMaxSide.toFloat()

            val targetWidth = (result.width * scale).toInt().coerceAtLeast(1)

            val targetHeight = (result.height * scale).toInt().coerceAtLeast(1)

            result = Bitmap.createScaledBitmap(result, targetWidth, targetHeight, true)

        }

        val currentMinSide = minOf(result.width, result.height)

        if (currentMinSide in 1 until MIN_UPLOAD_IMAGE_SIDE) {

            val scale = MIN_UPLOAD_IMAGE_SIDE.toFloat() / currentMinSide.toFloat()

            val targetWidth = (result.width * scale).toInt().coerceAtLeast(MIN_UPLOAD_IMAGE_SIDE)

            val targetHeight = (result.height * scale).toInt().coerceAtLeast(MIN_UPLOAD_IMAGE_SIDE)

            result = Bitmap.createScaledBitmap(result, targetWidth, targetHeight, true)

        }

        return result

    }

    private fun uploadMaxSideFor(faceCount: Int): Int {

        return if (faceCount > 1) {

            MULTI_FACE_MAX_UPLOAD_IMAGE_SIDE

        } else {

            MAX_UPLOAD_IMAGE_SIDE

        }

    }

    private fun processingMaxSideFor(sourceLabel: String): Int {

        return if (sourceLabel.contains("图库")) {

            GALLERY_FAST_PROCESS_MAX_IMAGE_SIDE

        } else {

            GLASS_PROCESS_MAX_IMAGE_SIDE

        }

    }

    private fun shouldRunGallerySupplementalFaceDetection(
        decoded: DecodedBitmap,
        bitmap: Bitmap,
        faces: List<Face>
    ): Boolean {

        if (decoded.sampleSize <= 1 || faces.isEmpty() || faces.size >= CLOUD_MAX_FACE_NUM) {

            return false

        }

        val sourceMaxSide = maxOf(decoded.originalWidth, decoded.originalHeight)

        if (sourceMaxSide < GALLERY_SUPPLEMENTAL_MIN_SOURCE_SIDE) {

            return false

        }

        val largestFaceRatio = faces.maxOf {

            localFaceAreaRatio(it.boundingBox, bitmap.width, bitmap.height)

        }

        val smallestFaceRatio = faces.minOf {

            localFaceAreaRatio(it.boundingBox, bitmap.width, bitmap.height)

        }

        return largestFaceRatio < GALLERY_SUPPLEMENTAL_LARGE_FACE_RATIO ||

            smallestFaceRatio < GALLERY_SUPPLEMENTAL_SMALL_FACE_RATIO

    }

    private fun localFaceAreaRatio(rect: Rect, width: Int, height: Int): Float {

        val clipped = clippedRect(rect, width, height) ?: return 0f

        return clipped.width().toFloat() * clipped.height().toFloat() /

            (width.toFloat() * height.toFloat()).coerceAtLeast(1f)

    }

    private fun decodeBitmapForProcessing(bytes: ByteArray, sourceLabel: String, maxSide: Int): DecodedBitmap? {

        val bounds = BitmapFactory.Options().apply { inJustDecodeBounds = true }

        BitmapFactory.decodeByteArray(bytes, 0, bytes.size, bounds)

        if (bounds.outWidth <= 0 || bounds.outHeight <= 0) {

            return null

        }

        val sampleSize = calculateInSampleSize(bounds.outWidth, bounds.outHeight, maxSide)

        val options = BitmapFactory.Options().apply {

            inSampleSize = sampleSize

            // 图库照片使用 ARGB_8888 保证人脸检测准确度；眼镜抓拍使用 RGB_565 节省内存

            inPreferredConfig = if (sourceLabel.contains("图库")) Bitmap.Config.ARGB_8888 else Bitmap.Config.RGB_565

        }

        val rawBitmap = BitmapFactory.decodeByteArray(bytes, 0, bytes.size, options) ?: return null

        val exifOrientation = readExifOrientation(bytes)

        val orientedBitmap = applyExifOrientation(rawBitmap, exifOrientation)

        if (orientedBitmap !== rawBitmap) {

            rawBitmap.recycle()

        }

        if (sampleSize > 1 || exifOrientation != ExifInterface.ORIENTATION_NORMAL) {

            recordDiagnostic(

                "$sourceLabel 解码优化: source=${bounds.outWidth}x${bounds.outHeight}, " +

                    "decoded=${orientedBitmap.width}x${orientedBitmap.height}, sample=$sampleSize, exif=$exifOrientation"

            )

        }

        val rotates = exifOrientation == ExifInterface.ORIENTATION_ROTATE_90 ||

            exifOrientation == ExifInterface.ORIENTATION_ROTATE_270 ||

            exifOrientation == ExifInterface.ORIENTATION_TRANSPOSE ||

            exifOrientation == ExifInterface.ORIENTATION_TRANSVERSE

        val originalWidth = if (rotates) bounds.outHeight else bounds.outWidth

        val originalHeight = if (rotates) bounds.outWidth else bounds.outHeight

        return DecodedBitmap(orientedBitmap, sampleSize, exifOrientation, originalWidth, originalHeight)

    }

    private fun calculateInSampleSize(width: Int, height: Int, maxSide: Int): Int {

        if (maxSide <= 0) return 1

        var sampleSize = 1

        val sourceMaxSide = maxOf(width, height)

        while (sourceMaxSide / sampleSize > maxSide && sampleSize < 16) {

            sampleSize *= 2

        }

        return sampleSize.coerceAtLeast(1)

    }

    private fun readExifOrientation(bytes: ByteArray): Int {

        return try {

            ExifInterface(ByteArrayInputStream(bytes)).getAttributeInt(

                ExifInterface.TAG_ORIENTATION,

                ExifInterface.ORIENTATION_NORMAL

            )

        } catch (e: Exception) {

            ExifInterface.ORIENTATION_NORMAL

        }

    }

    private fun imageSizeFromBytes(bytes: ByteArray): Pair<Int, Int>? {

        if (bytes.isEmpty()) {

            return null

        }

        return try {

            val options = BitmapFactory.Options().apply {

                inJustDecodeBounds = true

            }

            BitmapFactory.decodeByteArray(bytes, 0, bytes.size, options)

            if (options.outWidth > 0 && options.outHeight > 0) {

                options.outWidth to options.outHeight

            } else {

                null

            }

        } catch (_: Exception) {

            null

        }

    }

    private fun readExifOrientation(path: String): Int {

        return try {

            ExifInterface(path).getAttributeInt(

                ExifInterface.TAG_ORIENTATION,

                ExifInterface.ORIENTATION_NORMAL

            )

        } catch (e: Exception) {

            ExifInterface.ORIENTATION_NORMAL

        }

    }

    private fun applyExifOrientation(bitmap: Bitmap, orientation: Int): Bitmap {

        val matrix = Matrix()

        when (orientation) {

            ExifInterface.ORIENTATION_FLIP_HORIZONTAL -> matrix.setScale(-1f, 1f)

            ExifInterface.ORIENTATION_ROTATE_180 -> matrix.setRotate(180f)

            ExifInterface.ORIENTATION_FLIP_VERTICAL -> matrix.setScale(1f, -1f)

            ExifInterface.ORIENTATION_TRANSPOSE -> {

                matrix.setRotate(90f)

                matrix.postScale(-1f, 1f)

            }

            ExifInterface.ORIENTATION_ROTATE_90 -> matrix.setRotate(90f)

            ExifInterface.ORIENTATION_TRANSVERSE -> {

                matrix.setRotate(-90f)

                matrix.postScale(-1f, 1f)

            }

            ExifInterface.ORIENTATION_ROTATE_270 -> matrix.setRotate(-90f)

            else -> return bitmap

        }

        return try {

            Bitmap.createBitmap(bitmap, 0, 0, bitmap.width, bitmap.height, matrix, true)

        } catch (e: Exception) {

            recordDiagnostic("EXIF 方向修正失败: orientation=$orientation", e)

            bitmap

        }

    }

    private fun bitmapToJpegBytes(bitmap: Bitmap, quality: Int): ByteArray {

        val stream = ByteArrayOutputStream()

        stream.use {

            bitmap.compress(Bitmap.CompressFormat.JPEG, quality, it)

            return it.toByteArray()

        }

    }

    private fun cloudMaxFaceNumFor(localFaceCount: Int): Int {

        return localFaceCount.coerceIn(1, CLOUD_MAX_FACE_NUM)

    }

    private fun parseFaceRect(matchItem: JsonObject): FaceRect? {

        val rectObj = firstJsonObject(matchItem, "face_rect", "faceRect", "FaceRect", "rect", "Rect", "location", "Location")

            ?: return null

        return parseFaceRectObject(rectObj)

    }

    private fun parseNamedFaceRect(parent: JsonObject, vararg names: String): FaceRect? {

        return parseFaceRectObject(firstJsonObject(parent, *names))

    }

    private fun parseFaceRectObject(rectObj: JsonObject?): FaceRect? {

        rectObj ?: return null

        val x = firstJsonFloat(rectObj, "x", "X", "left", "Left", "originX", "OriginX") ?: return null

        val y = firstJsonFloat(rectObj, "y", "Y", "top", "Top", "originY", "OriginY") ?: return null

        val width = firstJsonFloat(rectObj, "width", "Width", "w", "W") ?: return null

        val height = firstJsonFloat(rectObj, "height", "Height", "h", "H") ?: return null

        return FaceRect(x, y, width, height).takeIf { width > 0f && height > 0f }

    }

    private fun firstJsonObject(parent: JsonObject, vararg names: String): JsonObject? {

        names.forEach { name ->

            val element = parent.get(name)

            if (element != null && element.isJsonObject) {

                return element.asJsonObject

            }

        }

        return null

    }

    private fun firstJsonFloat(parent: JsonObject, vararg names: String): Float? {

        names.forEach { name ->

            val element = parent.get(name)

            if (element != null && !element.isJsonNull) {

                try {

                    return element.asFloat

                } catch (e: Exception) {

                    // Try the next alias.

                }

            }

        }

        return null

    }

    private fun jsonString(parent: JsonObject, name: String, defaultValue: String = ""): String {

        val element = parent.get(name)

        if (element == null || element.isJsonNull) {

            return defaultValue

        }

        return try {

            element.asString ?: defaultValue

        } catch (_: Exception) {

            defaultValue

        }

    }

    private fun jsonLong(parent: JsonObject, name: String): Long? {

        val element = parent.get(name)

        if (element == null || element.isJsonNull) {

            return null

        }

        return try {

            element.asLong

        } catch (_: Exception) {

            null

        }

    }

    private fun jsonInt(parent: JsonObject, name: String): Int? {

        val element = parent.get(name)

        if (element == null || element.isJsonNull) {

            return null

        }

        return try {

            element.asInt

        } catch (_: Exception) {

            null

        }

    }

    private fun jsonFloat(parent: JsonObject, name: String): Float? {

        val element = parent.get(name)

        if (element == null || element.isJsonNull) {

            return null

        }

        return try {

            element.asFloat

        } catch (_: Exception) {

            null

        }

    }

    /**

     * 6. 网络中转请求：将抓拍上传至您的云服务器进行人脸检索，支持抓取定位框与系统头像

     */

    private fun postFaceSearchRequest(

        recordId: String?,

        base64Image: String,

        maxFaceNum: Int = DEFAULT_CLOUD_MAX_FACE_NUM,

        sourceLabel: String = "抓拍帧"

    ) {

        val isGallery = sourceLabel.contains("图库")

        val requestUrl = "$serverBaseUrl/dlsgzs/api/face/search"

        val requestMaxFaceNum = cloudMaxFaceNumFor(maxFaceNum)

        recordDiagnostic("准备云端识别请求 ($sourceLabel): url=$requestUrl, imageChars=${base64Image.length}, maxFaceNum=$requestMaxFaceNum")

        val jsonPayload = JsonObject().apply {

            addProperty("image", base64Image)

            addProperty("max_face_num", requestMaxFaceNum)

            addProperty("search_mode", "speed")

        }

        val requestBodyString = jsonPayload.toString()

        val request: Request

        try {

            val requestBody = requestBodyString

                .toRequestBody("application/json; charset=utf-8".toMediaTypeOrNull())

            request = Request.Builder()

                .url(requestUrl)

                .post(requestBody)

                .build()

            recordDiagnostic("云端识别请求已构建 ($sourceLabel): bodyChars=${requestBodyString.length}")

        } catch (e: Exception) {

            Log.e(TAG, "Invalid server request", e)

            updateRecognitionRecord(recordId) {

                it.status = STATUS_FAILED

                it.statusText = "服务器地址或请求参数无效"

                it.errorMessage = e.message

            }

            recordDiagnostic("云端识别请求构建异常 ($sourceLabel)", e)

            if (!isGallery) {

                runOnUiThread {

                    playResultBeep(success = false)

                    updateStatus("❌ 服务器地址或请求参数无效: ${e.message}", isWorking = false)

                }

            }

            return

        }

        fun handleSuccess(bodyString: String, responseCode: Int) {

            if (responseCode in 200..299 && bodyString.isNotEmpty()) {

                try {

                    val resultObj = Gson().fromJson(bodyString, JsonObject::class.java)

                    val success = resultObj.get("success")?.asBoolean ?: false

                    recordDiagnostic("云端 JSON 解析 ($sourceLabel): success=$success")

                    if (success) {

                        val resultsArray = resultObj.getAsJsonArray("results")

                        if (resultsArray != null && resultsArray.size() > 0) {

                            recordDiagnostic("云端匹配结果数量 ($sourceLabel): ${resultsArray.size()}")

                            val expertsForRecord = mutableListOf<ExpertInfo>()

                            val nameList = StringBuilder()

                            

                            for (i in 0 until resultsArray.size()) {

                                val matchItem = resultsArray.get(i).asJsonObject

                                val score = matchItem.get("score")?.asFloat ?: 0f

                                val expert = matchItem.getAsJsonObject("expert")

                                

                                val name = expert.get("name")?.asString ?: "-"

                                val company = expert.get("company")?.asString ?: "无工作单位"

                                val major = expert.get("major")?.asString ?: "未填写"

                                val phone = expert.get("phone")?.asString ?: "-"

                                val idCard = expert.get("id_card")?.asString ?: "-"

                                val photoPath = expert.get("photo_path")?.asString ?: ""

                                

                                val faceRect = parseFaceRect(matchItem)

                                recordDiagnostic(

                                    "云端匹配项 ($sourceLabel): index=$i, name=$name, score=$score, " +

                                        "faceRect=${faceRect?.let { "${it.x},${it.y},${it.width},${it.height}" } ?: "null"}"

                                )

                                 

                                expertsForRecord.add(ExpertInfo(name, company, major, phone, idCard, score, photoPath, faceRect))

                                

                                if (i > 0) nameList.append("，")

                                nameList.append(name)

                            }

                            // 数据落库与图片裁剪物理处理，在后台执行以防卡顿主线程。

                            executeWorker("落库云端识别结果 ($sourceLabel)") {

                                val mainRecord = findRecognitionRecord(recordId)

                                val originalBytes = loadHistoryBytes(mainRecord?.originalImagePath)

                                val recognitionImageBytes = loadHistoryBytes(mainRecord?.uploadImagePath) ?: originalBytes

                                val cropTargets = mutableListOf<Pair<String, ExpertInfo>>()

                                val fallbackRects = mainRecord?.localFaceRects ?: emptyList()

                                val expertsWithRects = expertsForRecord.mapIndexed { index, expert ->

                                    if (expert.faceRect != null || fallbackRects.isEmpty()) {

                                        expert

                                    } else {

                                        val fallbackRect = fallbackRects.getOrNull(index) ?: fallbackRects.firstOrNull()

                                        if (fallbackRect != null) {

                                            recordDiagnostic(

                                                "云端未返回人脸框 ($sourceLabel)，使用本地上传图人脸框: index=$index, " +

                                                    "rect=${fallbackRect.x},${fallbackRect.y},${fallbackRect.width},${fallbackRect.height}"

                                            )

                                            expert.copy(faceRect = fallbackRect)

                                        } else {

                                            expert

                                        }

                                    }

                                }

                                

                                for (i in expertsWithRects.indices) {

                                    val expert = expertsWithRects[i]

                                    if (i == 0) {

                                        // 第 1 位专家更新原主卡片

                                        updateRecognitionRecord(recordId) {

                                            it.status = STATUS_SUCCESS

                                            it.statusText = "识别成功"

                                            it.errorMessage = null

                                            it.experts.clear()

                                            it.experts.add(expert)

                                        }

                                        if (!recordId.isNullOrEmpty()) {

                                            cropTargets.add(recordId to expert)

                                        }

                                    } else {

                                        // 其余专家各自生成独立的历史卡片

                                        val newId = "${System.currentTimeMillis()}_${Random().nextInt(100000)}"

                                        val newRecord = RecognitionRecord(

                                            id = newId,

                                            createdAt = (mainRecord?.createdAt ?: System.currentTimeMillis()) - i * 10, // 微小时间偏移使列表时间倒序保持顺序正确

                                            updatedAt = System.currentTimeMillis(),

                                            status = STATUS_SUCCESS,

                                            statusText = "识别成功"

                                        )

                                        

                                        // 物理复制大图实现独立卡片解耦

                                        val dupPath = duplicateOriginalImage(mainRecord?.originalImagePath, newId)

                                        newRecord.originalImagePath = dupPath

                                        newRecord.originalWidth = mainRecord?.originalWidth ?: 0

                                        newRecord.originalHeight = mainRecord?.originalHeight ?: 0

                                        newRecord.uploadWidth = mainRecord?.uploadWidth ?: 0

                                        newRecord.uploadHeight = mainRecord?.uploadHeight ?: 0

                                        newRecord.faceRectImageWidth = mainRecord?.faceRectImageWidth ?: 0

                                        newRecord.faceRectImageHeight = mainRecord?.faceRectImageHeight ?: 0

                                        newRecord.uploadSourceRect = mainRecord?.uploadSourceRect

                                        newRecord.localFaceRects.addAll(mainRecord?.localFaceRects ?: emptyList())

                                        newRecord.experts.add(expert)

                                        cropTargets.add(newId to expert)

                                        

                                        synchronized(recognitionRecords) {

                                            recognitionRecords.add(0, newRecord)

                                        }

                                    }

                                }

                                saveRecognitionRecords()

                                 if (sourceLabel.contains("图库")) {

                                     galleryBatchExpertCount += expertsWithRects.size

                                 }

                                

                                // 处理完成后切回主线程渲染前台 UI

                                val displayBytes = recognitionImageBytes ?: originalBytes

                                runOnUiThread {

                                    if (displayBytes != null) {

                                        capturedFrameBytes = displayBytes

                                        lastLocalFaceCrop = BitmapFactory.decodeByteArray(displayBytes, 0, displayBytes.size)

                                    }

                                    matchedExpertsList.clear()

                                    matchedExpertsList.addAll(expertsWithRects)

                                    currentDisplayIndex = 0

                                    

                                    // 仅当不是图库照片时，才将匹配成功的卡片展示在前台并语音播放，防止批量识别干扰

                                    if (!isGallery) {

                                        showExpertInfoAt(currentDisplayIndex)

                                        playResultBeep(success = true)

                                        speakOut("核验通过，发现评标专家：$nameList")

                                        updateStatus("评标专家比对成功", isWorking = false)

                                    }

                                }

                                if (recognitionImageBytes != null) {

                                    cropTargets.forEach { (targetRecordId, expert) ->

                                        val rect = expert.faceRect ?: return@forEach

                                        val crop = cropAndSaveBestFaceImage(

                                            recognitionImageBytes,

                                            originalBytes,

                                            rect,

                                            targetRecordId

                                        )

                                        if (crop != null) {

                                            updateRecognitionRecord(targetRecordId) {

                                                it.uploadImagePath = crop.path

                                                it.uploadWidth = crop.width

                                                it.uploadHeight = crop.height

                                            }

                                        }

                                    }

                                }

                                cropTargets.forEach { (targetRecordId, _) ->

                                    publishRecognitionRecordIfNeeded(targetRecordId, sourceLabel)

                                }

                            }

                            return

                        }

                    }

                    

                    val errMsg = resultObj.get("error")?.asString ?: "未匹配到登记的专家档案"

                    updateRecognitionRecord(recordId) {

                        it.status = STATUS_NO_MATCH

                        it.statusText = "未匹配到登记专家"

                        it.errorMessage = errMsg

                        it.experts.clear()

                    }

                    recordDiagnostic("云端业务未匹配 ($sourceLabel): error=$errMsg")

                    if (!isGallery) {

                        runOnUiThread {

                            playResultBeep(success = false)

                            updateStatus(errMsg, isWorking = false)

                            speakOut("比对失败")

                            hideArOverlay()

                        }

                    }

                } catch (e: Exception) {

                    updateRecognitionRecord(recordId) {

                        it.status = STATUS_FAILED

                        it.statusText = "结果解析失败"

                        it.errorMessage = e.message

                    }

                    recordDiagnostic("云端响应解析异常 ($sourceLabel): preview=${bodyString.take(300)}", e)

                    if (!isGallery) {

                        runOnUiThread {

                            playResultBeep(success = false)

                            updateStatus("❌ 结果解析失败", isWorking = false)

                        }

                    }

                }

            } else {

                val cloudMessage = cloudErrorMessage(responseCode, bodyString)

                updateRecognitionRecord(recordId) {

                    it.status = STATUS_NO_MATCH

                    it.statusText = "云端未返回匹配结果"

                    it.errorMessage = cloudMessage

                    it.experts.clear()

                }

                recordDiagnostic(

                    "云端 HTTP 失败或空响应 ($sourceLabel): code=$responseCode, message=$cloudMessage, " +

                        "bodyPreview=${bodyString.take(300)}"

                )

                if (!isGallery) {

                    runOnUiThread {

                        playResultBeep(success = false)

                        updateStatus("⚠️ $cloudMessage", isWorking = false)

                        speakOut("核验未通过")

                        hideArOverlay()

                    }

                }

            }

        }

        fun handleFailure(e: Exception) {

            updateRecognitionRecord(recordId) {

                it.status = STATUS_FAILED

                it.statusText = "云端识别网络异常，可手动重试"

                it.errorMessage = e.message

            }

            recordDiagnostic("云端识别网络异常 ($sourceLabel): url=$requestUrl", e)

            if (!isGallery) {

                runOnUiThread {

                    playResultBeep(success = false)

                    updateStatus("❌ 网络故障，请确认您服务器的IP端口是否可达", isWorking = false)

                }

            }

        }

        if (isGallery) {

            // 图库批量识别同步执行：阻塞当前工作线程，实现最大并发受工作线程池 (MAX_PARALLEL_WORKERS = 3) 完美控制，绝不超频上云

            try {

                okHttpClient.newCall(request).execute().use { response ->

                    val bodyString = response.body?.string() ?: ""

                    recordDiagnostic("云端识别同步响应 ($sourceLabel): code=${response.code}, success=${response.isSuccessful}, bodyChars=${bodyString.length}")

                    handleSuccess(bodyString, response.code)

                }

            } catch (e: Exception) {

                handleFailure(e)

            }

        } else {

            // 普通抓拍继续异步入队

            okHttpClient.newCall(request).enqueue(object : Callback {

                override fun onFailure(call: Call, e: IOException) {

                    handleFailure(e)

                }

                override fun onResponse(call: Call, response: Response) {

                    val bodyString = response.body?.string() ?: ""

                    recordDiagnostic("云端识别响应 ($sourceLabel): code=${response.code}, success=${response.isSuccessful}, bodyChars=${bodyString.length}")

                    handleSuccess(bodyString, response.code)

                }

            })

        }

    }

    /**

     * 7. 渲染卡片 (支持轮播且支持头像多端异步显示与裁剪比对)

     */

    private fun showExpertInfoAt(index: Int) {

        if (index < 0 || index >= matchedExpertsList.size) return

        

        mainHandler.removeCallbacks(hideArRunnable)

        val expert = matchedExpertsList[index]

        // A. 手机端 UI 卡片渲染

        if (matchedExpertsList.size > 1) {

            binding.tvArHeader.text = String.format(Locale.getDefault(), "候选专家 %d/%d", index + 1, matchedExpertsList.size)

            binding.tvArHeader.setTextColor(ContextCompat.getColor(this, R.color.accent_warning_orange))

            binding.tvArScore.setTextColor(ContextCompat.getColor(this, R.color.accent_warning_orange))

        } else {

            binding.tvArHeader.text = "评标专家比对通过"

            binding.tvArHeader.setTextColor(ContextCompat.getColor(this, R.color.accent_aurora_green))

            binding.tvArScore.setTextColor(ContextCompat.getColor(this, R.color.accent_aurora_green))

        }

        

        binding.tvArScore.text = String.format(Locale.getDefault(), "%.1f%%", expert.score)

        binding.tvArName.text = expert.name

        binding.tvArCompany.text = expert.company

        binding.tvArMajor.text = expert.major

        binding.tvArPhone.text = expert.phone

        // 清空之前的头像占位，准备异步填充

        binding.ivCropFace.setImageBitmap(null)

        binding.ivSystemFace.setImageBitmap(null)

        currentLiveFace = null

        currentSystemFace = null

        if (binding.arOverlayLayout.visibility != View.VISIBLE) {

            val fadeIn = AlphaAnimation(0f, 1f).apply { duration = 300 }

            binding.arOverlayLayout.startAnimation(fadeIn)

            binding.arOverlayLayout.visibility = View.VISIBLE

        }

        // B. 眼镜 HUD 端空间防抖渲染 (通过 DisplayManager 获取外接 AR 眼镜显示屏进行投射)

        try {

            val displayManager = getSystemService(Context.DISPLAY_SERVICE) as DisplayManager

            val displays = displayManager.displays

            var glassDisplay: Display? = null

            for (d in displays) {

                if (d.displayId != Display.DEFAULT_DISPLAY) {

                    glassDisplay = d

                    break

                }

            }

            

            if (glassDisplay != null) {

                if (arPresentation == null) {

                    arPresentation = CxrArPresentation(this, glassDisplay)

                }

                arPresentation?.let {

                    if (!it.isShowing) {

                        it.show()

                    }

                    it.showExpertInfo(expert.name, expert.company, expert.major, expert.phone, expert.score, index, matchedExpertsList.size, null, null)

                }

            }

        } catch (e: Exception) {

            Log.e(TAG, "AR presentation render error", e)

        }

        // C. 启动头像数据异步拉取与流截帧裁剪

        if (expert.faceRect != null) {

            cropLiveFace(capturedFrameBytes, expert.faceRect)

        } else {

            lastLocalFaceCrop?.let { localFaceCrop ->

                currentLiveFace = localFaceCrop

                binding.ivCropFace.setImageBitmap(localFaceCrop)

                arPresentation?.setLiveFace(localFaceCrop)

            }

        }

        loadSystemFace(expert.photoPath)

        val delayMs = if (matchedExpertsList.size > 1) 8000L else 5000L

        mainHandler.postDelayed(hideArRunnable, delayMs)

    }

    /**

     * 8. 异步执行现场人脸定位裁剪

     */

    private fun cropLiveFace(bytes: ByteArray?, rect: FaceRect?) {

        if (bytes == null || rect == null) {

            return

        }

        executeWorker("裁剪现场人脸") {

            try {

                val bitmap = BitmapFactory.decodeByteArray(bytes, 0, bytes.size)

                if (bitmap != null) {

                    val cropped = cropBitmapForFace(bitmap, rect)

                    if (cropped != null) {

                        currentLiveFace = cropped

                        

                        runOnUiThread {

                            // 刷新手机端现场图

                            binding.ivCropFace.setImageBitmap(cropped)

                            // 刷新眼镜 AR HUD 端现场图

                            arPresentation?.setLiveFace(cropped)

                        }

                    }

                }

            } catch (e: Exception) {

                Log.e(TAG, "Crop live face error", e)

            }

        }

    }

    private fun cropAndSaveBestFaceImage(
        recognitionImageBytes: ByteArray,
        originalImageBytes: ByteArray?,
        rect: FaceRect,
        destRecordId: String
    ): SavedFaceCrop? {
        var recognitionBitmap: Bitmap? = null
        val candidates = mutableListOf<FaceCropCandidate>()
        return try {
            recognitionBitmap = BitmapFactory.decodeByteArray(recognitionImageBytes, 0, recognitionImageBytes.size)
                ?: return null

            addFaceCropCandidate(candidates, "upload-face-rect", recognitionBitmap, rect)

            if (candidates.isEmpty()) {
                recordDiagnostic("专家现场图裁剪无候选: destRecordId=$destRecordId, rect=$rect")
                return null
            }

            val selected = candidates.first()
            val stream = ByteArrayOutputStream()
            selected.bitmap.compress(Bitmap.CompressFormat.JPEG, 90, stream)
            val cropBytes = stream.toByteArray()
            val path = saveHistoryImage(destRecordId, "upload", cropBytes)

            recordDiagnostic(
                "专家现场图裁剪完成: destRecordId=$destRecordId, selected=${selected.label}, " +
                    "size=${selected.bitmap.width}x${selected.bitmap.height}"
            )

            SavedFaceCrop(path, selected.bitmap.width, selected.bitmap.height)
        } catch (e: Exception) {
            recordDiagnostic("裁剪并保存人脸图片异常: destRecordId=$destRecordId", e)
            null
        } finally {
            recognitionBitmap?.recycle()
            candidates.forEach { it.bitmap.recycle() }
        }
    }

    private fun addFaceCropCandidate(

        candidates: MutableList<FaceCropCandidate>,

        label: String,

        sourceBitmap: Bitmap,

        rect: FaceRect

    ) {

        val cropped = cropBitmapForFace(sourceBitmap, rect) ?: return

        candidates.add(FaceCropCandidate(label, cropped))

    }

    private fun cropBitmapForFace(sourceBitmap: Bitmap, rect: FaceRect): Bitmap? {

        val pixelRect = rect.toPixelRect(sourceBitmap.width, sourceBitmap.height) ?: return null

        val padX = (pixelRect.width() * 0.15f).roundToInt()

        val padY = (pixelRect.height() * 0.15f).roundToInt()

        val left = (pixelRect.left - padX).coerceAtLeast(0)

        val top = (pixelRect.top - padY).coerceAtLeast(0)

        val right = (pixelRect.right + padX).coerceAtMost(sourceBitmap.width)

        val bottom = (pixelRect.bottom + padY).coerceAtMost(sourceBitmap.height)

        if (right <= left || bottom <= top) {

            return null

        }

        return Bitmap.createBitmap(sourceBitmap, left, top, right - left, bottom - top)

    }

    private fun scoreFaceCrop(bitmap: Bitmap): Int {

        return try {

            val faces = Tasks.await(

                faceDetector.process(InputImage.fromBitmap(bitmap, 0)),

                1500,

                TimeUnit.MILLISECONDS

            )

            if (faces.isEmpty()) {

                0

            } else {

                val largestFaceArea = faces.maxOf { face ->

                    val bounds = face.boundingBox

                    (bounds.width().coerceAtLeast(0) * bounds.height().coerceAtLeast(0))

                }

                faces.size * 1_000_000 + largestFaceArea

            }

        } catch (e: Exception) {

            0

        }

    }

    private fun scaleFaceRect(rect: FaceRect, fromWidth: Int, fromHeight: Int, toWidth: Int, toHeight: Int): FaceRect {

        if (fromWidth <= 0 || fromHeight <= 0 || toWidth <= 0 || toHeight <= 0) {

            return rect

        }

        val scaleX = toWidth.toFloat() / fromWidth.toFloat()

        val scaleY = toHeight.toFloat() / fromHeight.toFloat()

        return FaceRect(

            x = rect.x * scaleX,

            y = rect.y * scaleY,

            width = rect.width * scaleX,

            height = rect.height * scaleY

        )

    }

    private fun faceRectFromPixelRect(rect: Rect): FaceRect {

        return FaceRect(

            x = rect.left.toFloat(),

            y = rect.top.toFloat(),

            width = rect.width().toFloat(),

            height = rect.height().toFloat()

        )

    }

    private fun scalePixelRectToFaceRect(
        rect: Rect,
        fromWidth: Int,
        fromHeight: Int,
        toWidth: Int,
        toHeight: Int
    ): FaceRect? {

        if (fromWidth <= 0 || fromHeight <= 0 || toWidth <= 0 || toHeight <= 0 ||
            rect.width() <= 0 || rect.height() <= 0
        ) {

            return null

        }

        val scaleX = toWidth.toFloat() / fromWidth.toFloat()

        val scaleY = toHeight.toFloat() / fromHeight.toFloat()

        return FaceRect(

            x = rect.left * scaleX,

            y = rect.top * scaleY,

            width = rect.width() * scaleX,

            height = rect.height() * scaleY

        )

    }

    private fun duplicateOriginalImage(srcPath: String?, destRecordId: String): String? {

        if (srcPath.isNullOrEmpty()) return null

        return try {

            val srcFile = File(srcPath)

            if (srcFile.exists()) {

                val destFile = File(historyDir(), "${destRecordId}_original.jpg")

                srcFile.copyTo(destFile, overwrite = true)

                destFile.absolutePath

            } else {

                null

            }

        } catch (e: Exception) {

            recordDiagnostic("复制原始大图失败: srcPath=$srcPath, destRecordId=$destRecordId", e)

            null

        }

    }

    private fun expertPhotoUrl(photoPath: String): String {

        if (photoPath.startsWith("http://") || photoPath.startsWith("https://")) {

            return photoPath

        }

        val normalizedPath = if (photoPath.startsWith("/")) photoPath else "/$photoPath"

        return serverBaseUrl.trimEnd('/') + normalizedPath

    }

    /**

     * 9. 异步下载系统存档照片

     */

    private fun loadSystemFace(photoPath: String) {

        if (photoPath.isEmpty()) {

            return

        }

        val url = expertPhotoUrl(photoPath)

        val request = Request.Builder().url(url).build()

        

        okHttpClient.newCall(request).enqueue(object : Callback {

            override fun onFailure(call: Call, e: IOException) {

                Log.e(TAG, "Failed to load system face: $url", e)

            }

            override fun onResponse(call: Call, response: Response) {

                if (response.isSuccessful) {

                    val bytes = response.body?.bytes()

                    if (bytes != null) {

                        val bitmap = BitmapFactory.decodeByteArray(bytes, 0, bytes.size)

                        if (bitmap != null) {

                            currentSystemFace = bitmap

                            runOnUiThread {

                                // 刷新手机端系统存档图

                                binding.ivSystemFace.setImageBitmap(bitmap)

                                // 刷新眼镜 AR HUD 端系统存档图

                                arPresentation?.setSystemFace(bitmap)

                            }

                        }

                    }

                }

            }

        })

    }

    /**

     * 10. 轮播控制：下一个 (向前滑动)

     */

    private fun showNextExpert() {

        if (matchedExpertsList.size > 1) {

            currentDisplayIndex = (currentDisplayIndex + 1) % matchedExpertsList.size

            showExpertInfoAt(currentDisplayIndex)

            speakOut(matchedExpertsList[currentDisplayIndex].name) 

        }

    }

    /**

     * 11. 轮播控制：上一个 (向后滑动)

     */

    private fun showPrevExpert() {

        if (matchedExpertsList.size > 1) {

            currentDisplayIndex = (currentDisplayIndex - 1 + matchedExpertsList.size) % matchedExpertsList.size

            showExpertInfoAt(currentDisplayIndex)

            speakOut(matchedExpertsList[currentDisplayIndex].name)

        }

    }

    private fun hideArOverlay() {

        if (binding.arOverlayLayout.visibility == View.VISIBLE) {

            val fadeOut = AlphaAnimation(1f, 0f).apply { duration = 300 }

            binding.arOverlayLayout.startAnimation(fadeOut)

            binding.arOverlayLayout.visibility = View.GONE

        }

        

        try {

            arPresentation?.dismiss()

        } catch (e: Exception) {

            // ignore

        }

        arPresentation = null // 重置为空以防重新发现眼镜副屏时复用旧 Display 导致 InvalidDisplayException 闪退

    }

    private fun recordDiagnostic(message: String, throwable: Throwable? = null) {

        val line = "[${diagnosticTimeFormat.format(Date())}] $message"

        val fullLine = if (throwable != null) {

            "$line\n${Log.getStackTraceString(throwable).lineSequence().take(8).joinToString("\n")}"

        } else {

            line

        }

        synchronized(diagnosticLines) {

            diagnosticLines.addLast(fullLine)

            while (diagnosticLines.size > MAX_DIAGNOSTIC_LINES) {

                diagnosticLines.removeFirst()

            }

        }

        if (throwable == null && isRealtimeCloudDiagnosticMessage(message)) {
            rememberRealtimeCloudDiagnosticLine(fullLine)
        }

        if (throwable != null) {

            Log.e(TAG, message, throwable)

        } else {

            Log.d(TAG, message)

        }

        runOnUiThread {

            if (::binding.isInitialized) {

                if (binding.settingsPage.visibility != View.VISIBLE) {
                    return@runOnUiThread
                }

                binding.tvDiagnostics.text = diagnosticLogText()

                binding.diagnosticsScroll.post {

                    binding.diagnosticsScroll.fullScroll(View.FOCUS_DOWN)

                }

            }

        }

    }

    private fun isRealtimeCloudDiagnosticMessage(message: String): Boolean {
        return message.startsWith("实时云端识别") ||
            message.startsWith("实时云端候选") ||
            message.startsWith("实时 NoFace") ||
            message.startsWith("实时同人") ||
            message.startsWith("实时识别记录")
    }

    private fun rememberRealtimeCloudDiagnosticLine(line: String) {
        synchronized(realtimeCloudEventLines) {
            realtimeCloudEventLines.addLast(line)
            while (realtimeCloudEventLines.size > MAX_REALTIME_CLOUD_EVENT_LINES) {
                realtimeCloudEventLines.removeFirst()
            }
        }
    }

    private fun diagnosticLogText(): String {

        return synchronized(diagnosticLines) {

            if (diagnosticLines.isEmpty()) {

                getString(R.string.diagnostics_empty)

            } else {

                diagnosticLines.joinToString("\n")

            }

        }

    }

    private fun copyDiagnosticsToClipboard() {

        val diagnostics = collectDiagnosticsSnapshot()

        val clipboard = getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager

        clipboard.setPrimaryClip(ClipData.newPlainText("Rokid glasses diagnostics", diagnostics))

        Toast.makeText(this, "诊断信息已复制，可直接发给开发排查", Toast.LENGTH_SHORT).show()

        recordDiagnostic("用户复制诊断信息: chars=${diagnostics.length}")

    }

    private fun collectDiagnosticsSnapshot(): String {

        val logText = synchronized(diagnosticLines) {

            diagnosticLines.joinToString("\n")

        }

        val realtimeCloudLogText = synchronized(realtimeCloudEventLines) {

            realtimeCloudEventLines.joinToString("\n")

        }

        return buildString {

            appendLine("Field Recognition Companion Diagnostics")

            appendLine("time=${Date()}")

            appendLine("app=${appVersionBrief()}")

            appendLine("device=${deviceBrief()}")

            appendLine("serverBaseUrl=$serverBaseUrl")

            appendLine("soundPromptEnabled=$soundPromptEnabled")

            appendLine("captureParams=${captureParamsBrief()}")

            val rtmpSnapshot = latestRtmpReceiverSnapshot
            val rtmpLastDataAgeMs = if (rtmpSnapshot.lastDataAtMs > 0L) {
                System.currentTimeMillis() - rtmpSnapshot.lastDataAtMs
            } else {
                -1L
            }
            val rtmpFirstVideoAgeMs = if (rtmpSnapshot.firstVideoAtMs > 0L) {
                System.currentTimeMillis() - rtmpSnapshot.firstVideoAtMs
            } else {
                -1L
            }

            appendLine(
                "embeddedRtmpReceiver=running:${rtmpSnapshot.running},listening:${rtmpSnapshot.listening}," +
                    "connected:${rtmpSnapshot.clientConnected},port:${rtmpSnapshot.port},stream:${rtmpSnapshot.streamName}," +
                    "remote:${rtmpSnapshot.remoteAddress},app:${rtmpSnapshot.appName}," +
                    "video:${rtmpSnapshot.videoTags},audio:${rtmpSnapshot.audioTags},bytes:${rtmpSnapshot.totalPayloadBytes}," +
                    "codec:${rtmpSnapshot.lastVideoCodec},audioCodec:${rtmpSnapshot.lastAudioCodec}," +
                    "keyframes:${rtmpSnapshot.keyframeCount},avcSeq:${rtmpSnapshot.avcSequenceHeaderCount}," +
                    "firstVideoAgeMs:$rtmpFirstVideoAgeMs,lastDataAgeMs:$rtmpLastDataAgeMs"
            )

            appendLine("realtimeStreamRunning=$isRealtimeStreamRunning")

            val realtimeNow = System.currentTimeMillis()
            val pendingPreviewFrame = synchronized(rtmpPreviewFrameDispatchLock) {
                pendingRtmpPreviewFrame?.decodedFrames ?: 0L
            }
            val realtimeBudgetSnapshot = synchronized(realtimeCloudBudgetLock) {
                trimRealtimeCloudBudgetLocked(realtimeNow)
                "http:$activeRealtimeCloudHttpRequestCount/$REALTIME_CLOUD_HTTP_MAX_IN_FLIGHT," +
                    "rolling:${realtimeCloudHttpRequestStarts.size}/$REALTIME_CLOUD_HTTP_ROLLING_MAX_REQUESTS," +
                    "rescueSinceMs:${if (lastRealtimeRescueHttpAt > 0L) realtimeNow - lastRealtimeRescueHttpAt else -1}"
            }
            val rescueQueueSnapshot = synchronized(realtimeRescueLock) {
                trimRealtimeRescueCandidatesLocked(realtimeNow)
                "active:$activeRealtimeRescueRequestCount/$REALTIME_RESCUE_MAX_IN_FLIGHT," +
                    "queued:${realtimeRescueCandidates.size}"
            }
            appendLine(
                "activeRealtimeCloudRequests=$activeRealtimeCloudRequestCount/${realtimeCloudMaxConcurrentRequests(realtimeNow)}," +
                    "crowdMode=${isRealtimeCrowdModeActive(realtimeNow)},session=${currentRealtimeRecognitionSessionId()}"
            )

            appendLine("realtimeCloudBudget=$realtimeBudgetSnapshot,rescue=$rescueQueueSnapshot")

            appendLine("realtimeTracks=${realtimeTrackDiagnosticsSummary(realtimeNow)}")

            appendLine(
                "realtimePreview=latestFrame:$latestRtmpPreviewFrameIndex,renderedFrame:$lastRtmpPreviewRenderedFrameIndex," +
                    "pendingFrame:$pendingPreviewFrame,dispatchPosted:$isRtmpPreviewFrameDispatchPosted," +
                    "preview:${latestRtmpPreviewFrameWidth}x$latestRtmpPreviewFrameHeight/${latestRtmpPreviewFrameBytes}B," +
                    "receiveAgeMs:${if (lastRtmpPreviewFrameReceivedAt > 0L) realtimeNow - lastRtmpPreviewFrameReceivedAt else -1}," +
                    "renderAgeMs:${if (lastRtmpPreviewFrameRenderedAt > 0L) realtimeNow - lastRtmpPreviewFrameRenderedAt else -1}," +
                    "renderRunning:$isRtmpPreviewRenderRunning,renderRunningMs:${if (rtmpPreviewRenderStartedAt > 0L) realtimeNow - rtmpPreviewRenderStartedAt else -1}," +
                    "detectRunning:$isRtmpPreviewFaceDetectionRunning,detectRunningMs:${if (rtmpPreviewFaceDetectionStartedAt > 0L) realtimeNow - rtmpPreviewFaceDetectionStartedAt else -1}"
            )

            appendLine(
                "realtimeLastDetect=frame:$lastRealtimeDetectFrame,ageMs:${if (lastRealtimeDetectAt > 0L) realtimeNow - lastRealtimeDetectAt else -1}," +
                    "detected:$lastRealtimeDetectDetectedCount,valid:$lastRealtimeDetectValidCount," +
                    "uploadable:$lastRealtimeDetectUploadableCount,wait:$lastRealtimeDetectWaitingCount," +
                    "low:$lastRealtimeDetectLowQualityCount,detectMs:$lastRealtimeDetectCostMs,evalMs:$lastRealtimeEvaluateCostMs," +
                    "bitmap:${lastRealtimeDetectBitmapWidth}x$lastRealtimeDetectBitmapHeight/${lastRealtimeDetectBytes}B"
            )

            appendLine(
                "realtimeLastCloud=track:$lastRealtimeCloudTrackId,frame:$lastRealtimeCloudFrame," +
                    "ageMs:${if (lastRealtimeCloudCompletedAt > 0L) realtimeNow - lastRealtimeCloudCompletedAt else -1}," +
                    "result:$lastRealtimeCloudResult,costMs:$lastRealtimeCloudCostMs,message:${lastRealtimeCloudMessage.take(80)}"
            )

            appendLine("activeCaptureRequest=${activeCaptureRequestWidth}x$activeCaptureRequestHeight q=$activeCaptureRequestQuality timeoutMs=$activeCaptureTimeoutMs startedAt=$activeCaptureRequestStartedAt")

            appendLine("runtimePermissions=${runtimePermissionStatus()}")

            appendLine("galleryPermissions=${galleryPermissionStatus()}")

            appendLine("videoPermissions=${videoPermissionStatus()}")

            appendLine("glassPermissions=${glassPermissionStatus()}")

            appendLine("requiredRokidAppInstalled=${safeBoolean { AuthorizationHelper.isRequiredRokidAppInstalled(this@MainActivity) }}")

            appendLine("requiredHiRokidInstalled=${safeBoolean { AuthorizationHelper.isRequiredHiRokidInstalled(this@MainActivity) }}")

            appendLine("isConnectHiRokid=${safeBoolean { AuthorizationHelper.isConnectHiRokid() }}")

            appendLine("cxrAuthTokenPresent=${cxrAuthToken != null}")

            appendLine("isCxrServiceConnected=$isCxrServiceConnected")

            appendLine("isGlassWirelessConnected=$isGlassWirelessConnected")

            appendLine("pendingGlassCapture=$pendingGlassCapture")

            appendLine("isMatchingRequestRunning=$isMatchingRequestRunning")

            appendLine("latestFrameBytes=${latestFrameBytes?.size ?: 0}")

            appendLine("capturedFrameBytes=${capturedFrameBytes?.size ?: 0}")

            appendLine("lastLocalFaceCrop=${lastLocalFaceCrop?.width ?: 0}x${lastLocalFaceCrop?.height ?: 0}")

            appendLine("matchedExperts=${matchedExpertsList.size}")

            if (realtimeCloudLogText.isNotBlank()) {

                appendLine("----- realtime cloud events -----")

                appendLine(realtimeCloudLogText)

            }

            appendLine("----- recent logs -----")

            appendLine(logText)

        }

    }

    private fun runtimePermissionStatus(): String {

        return requiredRuntimePermissions().joinToString(",") { permission ->

            val granted = ContextCompat.checkSelfPermission(this, permission) == PackageManager.PERMISSION_GRANTED

            "${permission.substringAfterLast('.')}=$granted"

        }

    }

    private fun galleryPermissionStatus(): String {

        return galleryImagePermissions().joinToString(",") { permission ->

            val granted = ContextCompat.checkSelfPermission(this, permission) == PackageManager.PERMISSION_GRANTED

            "${permission.substringAfterLast('.')}=$granted"

        }

    }

    private fun videoPermissionStatus(): String {

        return galleryVideoPermissions().joinToString(",") { permission ->

            val granted = ContextCompat.checkSelfPermission(this, permission) == PackageManager.PERMISSION_GRANTED

            "${permission.substringAfterLast('.')}=$granted"

        }

    }

    private fun glassPermissionStatus(): String {

        return REQUIRED_GLASS_PERMISSIONS.joinToString(",") { permission ->

            val granted = try {

                AuthorizationHelper.hasGlassPermission(permission)

            } catch (e: Exception) {

                recordDiagnostic("读取 Rokid 权限异常: ${permission.name}", e)

                false

            }

            "${permission.name}=$granted"

        }

    }

    private fun appVersionBrief(): String {

        return try {

            val info = packageManager.getPackageInfo(packageName, 0)

            "${info.versionName}(${info.longVersionCode}) package=$packageName"

        } catch (e: Exception) {

            "unknown package=$packageName"

        }

    }

    private fun deviceBrief(): String {

        return "${Build.MANUFACTURER}/${Build.MODEL} android=${Build.VERSION.RELEASE} sdk=${Build.VERSION.SDK_INT}"

    }

    private inline fun safeBoolean(block: () -> Boolean): String {

        return try {

            block().toString()

        } catch (e: Exception) {

            "error:${e.javaClass.simpleName}:${e.message ?: "-"}"

        }

    }

    private fun updateStatus(statusText: String, isWorking: Boolean) {

        recordDiagnostic("状态更新: working=$isWorking, text=$statusText")

        runOnUiThread {

            binding.tvStatus.text = statusText

            if (isWorking) {

                binding.tvStatus.setTextColor(ContextCompat.getColor(this, R.color.accent_warning_orange))

            } else {

                binding.tvStatus.setTextColor(ContextCompat.getColor(this, R.color.text_primary))

            }

        }

    }

    // TTS 播报初始化

    override fun onInit(status: Int) {

        recordDiagnostic("TTS 初始化回调: status=$status")

        if (status == TextToSpeech.SUCCESS) {

            val audioResult = tts?.setAudioAttributes(

                AudioAttributes.Builder()

                    .setUsage(AudioAttributes.USAGE_ASSISTANCE_NAVIGATION_GUIDANCE)

                    .setContentType(AudioAttributes.CONTENT_TYPE_SPEECH)

                    .build()

            )

            val result = tts?.setLanguage(Locale.CHINESE)

            if (result != TextToSpeech.LANG_MISSING_DATA && result != TextToSpeech.LANG_NOT_SUPPORTED) {

                isTtsInitialized = true

            }

            recordDiagnostic("TTS 中文设置结果: audioResult=$audioResult, result=$result, initialized=$isTtsInitialized")

        }

    }

    private fun speakOut(text: String) {

        if (text.isBlank()) {

            return

        }

        if (!soundPromptEnabled) {

            recordDiagnostic("TTS 播报跳过: soundPromptEnabled=false, text=$text")

            return

        }

        if (isTtsInitialized && tts != null) {

            val result = tts?.speak(text, TextToSpeech.QUEUE_FLUSH, null, "FaceMatchTTS")

            recordDiagnostic("TTS 播报请求: result=$result, text=$text")

        } else {

            recordDiagnostic("TTS 播报跳过: initialized=$isTtsInitialized, text=$text")

        }

    }

    private fun playCaptureBeep() {

        playPromptTone("抓拍提示音", ToneGenerator.TONE_PROP_ACK, CAPTURE_BEEP_DURATION_MS)

    }

    private fun playResultBeep(success: Boolean) {

        if (success) {

            playPromptTone("识别成功提示音", ToneGenerator.TONE_PROP_ACK, RESULT_BEEP_DURATION_MS)

        } else {

            playPromptTone("识别失败提示音", ToneGenerator.TONE_PROP_NACK, RESULT_BEEP_DURATION_MS)

        }

    }

    private fun playPromptTone(label: String, toneType: Int, durationMs: Int) {

        if (!soundPromptEnabled) {

            recordDiagnostic("$label 跳过: soundPromptEnabled=false")

            return

        }

        try {

            val tone = ToneGenerator(AudioManager.STREAM_NOTIFICATION, PROMPT_TONE_VOLUME)

            val started = tone.startTone(toneType, durationMs)

            recordDiagnostic("$label: started=$started, stream=notification, durationMs=$durationMs")

            mainHandler.postDelayed({

                try {

                    tone.release()

                } catch (e: Exception) {

                    // ignore

                }

            }, (durationMs + 100).toLong())

        } catch (e: Exception) {

            recordDiagnostic("$label 播放失败", e)

        }

    }

    private fun requiredRuntimePermissions(): Array<String> {

        val permissions = mutableListOf(Manifest.permission.CAMERA)

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {

            permissions.add(Manifest.permission.BLUETOOTH_CONNECT)

        }

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {

            permissions.add(Manifest.permission.NEARBY_WIFI_DEVICES)

        }

        return permissions.toTypedArray()

    }

    private fun allPermissionsGranted() = requiredRuntimePermissions().all {

        ContextCompat.checkSelfPermission(baseContext, it) == PackageManager.PERMISSION_GRANTED

    }

    private fun galleryImagePermissions(): Array<String> {

        return if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.UPSIDE_DOWN_CAKE) {

            arrayOf(

                Manifest.permission.READ_MEDIA_IMAGES,

                Manifest.permission.READ_MEDIA_VISUAL_USER_SELECTED

            )

        } else if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {

            arrayOf(Manifest.permission.READ_MEDIA_IMAGES)

        } else {

            arrayOf(Manifest.permission.READ_EXTERNAL_STORAGE)

        }

    }

    private fun galleryImagePermissionsGranted(): Boolean {

        return if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.UPSIDE_DOWN_CAKE) {

            ContextCompat.checkSelfPermission(this, Manifest.permission.READ_MEDIA_IMAGES) == PackageManager.PERMISSION_GRANTED ||

                ContextCompat.checkSelfPermission(this, Manifest.permission.READ_MEDIA_VISUAL_USER_SELECTED) == PackageManager.PERMISSION_GRANTED

        } else {

            galleryImagePermissions().all {

                ContextCompat.checkSelfPermission(this, it) == PackageManager.PERMISSION_GRANTED

            }

        }

    }

    private fun galleryVideoPermissions(): Array<String> {

        return if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.UPSIDE_DOWN_CAKE) {

            arrayOf(

                Manifest.permission.READ_MEDIA_VIDEO,

                Manifest.permission.READ_MEDIA_VISUAL_USER_SELECTED

            )

        } else if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {

            arrayOf(Manifest.permission.READ_MEDIA_VIDEO)

        } else {

            arrayOf(Manifest.permission.READ_EXTERNAL_STORAGE)

        }

    }

    private fun galleryVideoPermissionsGranted(): Boolean {

        return fullVideoLibraryPermissionGranted() || limitedMediaSelectionGranted()

    }

    private fun fullVideoLibraryPermissionGranted(): Boolean {

        return if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {

            ContextCompat.checkSelfPermission(this, Manifest.permission.READ_MEDIA_VIDEO) == PackageManager.PERMISSION_GRANTED

        } else {

            ContextCompat.checkSelfPermission(this, Manifest.permission.READ_EXTERNAL_STORAGE) == PackageManager.PERMISSION_GRANTED

        }

    }

    private fun limitedMediaSelectionGranted(): Boolean {

        return if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.UPSIDE_DOWN_CAKE) {

            ContextCompat.checkSelfPermission(this, Manifest.permission.READ_MEDIA_VISUAL_USER_SELECTED) == PackageManager.PERMISSION_GRANTED

        } else {

            false

        }

    }

    override fun onRequestPermissionsResult(

        requestCode: Int, permissions: Array<String>, grantResults: IntArray

    ) {

        super.onRequestPermissionsResult(requestCode, permissions, grantResults)

        if (requestCode == REQUEST_CODE_PERMISSIONS) {

            recordDiagnostic(

                "运行时权限回调: ${permissions.zip(grantResults.toTypedArray()).joinToString(",") { (permission, result) ->

                    "${permission.substringAfterLast('.')}=${result == PackageManager.PERMISSION_GRANTED}"

                }}"

            )

            if (allPermissionsGranted()) {

                requestCxrAuthorizationAndConnect()

            } else {

                recordDiagnostic("运行时权限被拒绝: ${runtimePermissionStatus()}")

                Toast.makeText(this, "核心权限被拒绝，无法启动眼镜连接", Toast.LENGTH_SHORT).show()

            }

        } else if (requestCode == REQUEST_CODE_GALLERY_IMAGES) {

            recordDiagnostic(

                "图库权限回调: ${permissions.zip(grantResults.toTypedArray()).joinToString(",") { (permission, result) ->

                    "${permission.substringAfterLast('.')}=${result == PackageManager.PERMISSION_GRANTED}"

                }}"

            )

            if (galleryImagePermissionsGranted()) {

                loadGalleryPreview(force = true)

            } else {

                updateGalleryStatus("未获得图库照片权限")

                Toast.makeText(this, "未获得图库照片权限，无法读取最近照片", Toast.LENGTH_SHORT).show()

            }

        } else if (requestCode == REQUEST_CODE_GALLERY_VIDEOS) {

            recordDiagnostic(

                "视频权限回调: ${permissions.zip(grantResults.toTypedArray()).joinToString(",") { (permission, result) ->

                    "${permission.substringAfterLast('.')}=${result == PackageManager.PERMISSION_GRANTED}"

                }}"

            )

            if (galleryVideoPermissionsGranted()) {

                loadVideoPreview(force = true)

            } else {

                updateVideoStatus("未获得图库视频权限")

                Toast.makeText(this, "未获得图库视频权限，无法读取最近视频", Toast.LENGTH_SHORT).show()

            }

        }

    }

    override fun onDestroy() {

        recordDiagnostic("Activity销毁: service=$isCxrServiceConnected, glass=$isGlassWirelessConnected")

        stopEmbeddedRtmpReceiver("Activity 销毁")

        stopRealtimeStreamTest("Activity 销毁")

        unregisterRtmpReceiverBroadcasts()

        if (::binding.isInitialized) {
            binding.ivPreview.setImageDrawable(null)
            binding.ivRealtimeStreamPreview.setImageDrawable(null)
        }
        currentRtmpPreviewBitmap = null
        latestRealtimeOverlaySnapshot = null

        super.onDestroy()

        cxrLink?.disconnect()

        cxrLink = null

        faceDetector.close()

        sensitiveFaceDetector.close()

        videoFaceDetector.close()

        realtimeFaceDetector?.close()

        closeLookbackFaceDetector()

        workExecutor.shutdown()

        if (::realtimeCloudExecutor.isInitialized) realtimeCloudExecutor.shutdown()

        if (::thumbnailExecutor.isInitialized) thumbnailExecutor.shutdown()

        tts?.stop()

        tts?.shutdown()

        mainHandler.removeCallbacks(hideArRunnable)

        mainHandler.removeCallbacks(glassCaptureTimeoutRunnable)

        mainHandler.removeCallbacks(sharedRecordSyncRunnable)

    }

    companion object {

        private const val TAG = "RokidCxrWireless"

        private const val REQUEST_CODE_PERMISSIONS = 30

        private const val REQUEST_CODE_CXR_AUTH = 31

        private const val REQUEST_CODE_GALLERY_IMAGES = 32

        private const val REQUEST_CODE_GALLERY_VIDEOS = 33

        private const val REQUEST_CODE_PICK_VIDEO = 34
        private const val REQUEST_CODE_PICK_IMAGE = 35

        private const val MAX_PARALLEL_WORKERS = 3

        private const val DEFAULT_GLASS_CAPTURE_WIDTH = 2560

        private const val DEFAULT_GLASS_CAPTURE_HEIGHT = 1440

        private const val DEFAULT_GLASS_CAPTURE_QUALITY = 92

        private const val CAPTURE_MIN_SIZE = 320

        private const val CAPTURE_MAX_SIZE = 4096

        private const val CAPTURE_MIN_QUALITY = 50

        private const val CAPTURE_MAX_QUALITY = 100

        private const val GLASS_CAPTURE_TIMEOUT_MS = 15000L

        private const val LATE_CAPTURE_ACCEPT_MS = 10000L

        private const val EXTERNAL_CAPTURE_DEBOUNCE_MS = 1500L

        private const val FACE_UPLOAD_JPEG_QUALITY = 92

        private const val MAX_UPLOAD_IMAGE_SIDE = 1280

        private const val MULTI_FACE_MAX_UPLOAD_IMAGE_SIDE = 1920

        private const val MIN_UPLOAD_IMAGE_SIDE = 224

        private const val GLASS_PROCESS_MAX_IMAGE_SIDE = 1200

        private const val GALLERY_FAST_PROCESS_MAX_IMAGE_SIDE = 1200

        private const val GALLERY_RETRY_PROCESS_MAX_IMAGE_SIDE = 4096

        private const val IMAGE_SENSITIVE_RETRY_PROCESS_MAX_SIDE = 2400

        private const val GALLERY_SUPPLEMENTAL_MIN_SOURCE_SIDE = 2400

        private const val GALLERY_SUPPLEMENTAL_SMALL_FACE_RATIO = 0.035f

        private const val GALLERY_SUPPLEMENTAL_LARGE_FACE_RATIO = 0.08f

        private const val FACE_CROP_HORIZONTAL_PADDING = 0.70f

        private const val FACE_CROP_TOP_PADDING = 0.75f

        private const val FACE_CROP_BOTTOM_PADDING = 1.00f

        private const val PROMPT_TONE_VOLUME = 100

        private const val CAPTURE_BEEP_DURATION_MS = 160

        private const val RESULT_BEEP_DURATION_MS = 180

        private const val MAX_DIAGNOSTIC_LINES = 80

        private const val MAX_REALTIME_CLOUD_EVENT_LINES = 24

        private const val DEFAULT_GALLERY_BATCH_SIZE = 5

        private const val MAX_GALLERY_BATCH_SIZE = 20

        private const val GALLERY_PREVIEW_SIZE = 30

        private const val GALLERY_GRID_COLUMNS = 3

        private const val GALLERY_PULL_HINT_DISTANCE_DP = 28

        private const val GALLERY_PULL_REFRESH_DISTANCE_DP = 72

        private const val GALLERY_PROGRESS_HIDE_DELAY_MS = 1200L

        private const val VIDEO_PREVIEW_SIZE = 20

        private const val VIDEO_GRID_COLUMNS = 2

        private const val VIDEO_QUICK_SAMPLE_INTERVAL_MS = 300L

        private const val VIDEO_QUICK_SHORT_DURATION_MS = 15000L

        private const val VIDEO_QUICK_SHORT_INTERVAL_MS = 200L

        private const val VIDEO_QUICK_DENSE_DURATION_MS = 60000L

        private const val VIDEO_MAX_QUICK_SAMPLE_FRAMES = 180

        private const val VIDEO_QUICK_DECODE_MAX_SIDE = 640

        private const val VIDEO_QUICK_PROCESS_MAX_SIDE = 960

        private const val VIDEO_CODEC_DEQUEUE_TIMEOUT_US = 10_000L

        private const val VIDEO_CODEC_MAX_IDLE_LOOPS = 2_000

        private const val VIDEO_FINE_SAMPLE_INTERVAL_MS = 150L

        private const val VIDEO_FINE_WINDOW_BEFORE_MS = 800L

        private const val VIDEO_FINE_WINDOW_AFTER_MS = 800L

        private const val VIDEO_MAX_FINE_SAMPLE_FRAMES = 50

        private const val VIDEO_FINE_PROCESS_MAX_SIDE = 960

        private const val VIDEO_MAX_UPLOAD_IMAGE_SIDE = 1600

        private const val VIDEO_FRAME_JPEG_QUALITY = 92

        private const val VIDEO_MAX_LOCAL_CANDIDATES = 12

        private const val VIDEO_MAX_CLOUD_UPLOADS = 10

        private const val VIDEO_RESCUE_CLOUD_MAX_FACE_NUM = 3

        private const val VIDEO_MIN_FACE_AREA_RATIO = 0.0006f

        private const val VIDEO_MIN_UPLOAD_QUALITY_SCORE = 250

        private const val VIDEO_SIDE_PROFILE_MIN_YAW = 40f

        private const val VIDEO_SIDE_PROFILE_MIN_UPLOAD_QUALITY_SCORE = 30

        private const val VIDEO_PERSON_STRONG_HASH_DISTANCE = 7

        private const val VIDEO_PERSON_RELAXED_HASH_DISTANCE = 14

        private const val VIDEO_PERSON_TRACK_MAX_GAP_MS = 1100L

        private const val VIDEO_PERSON_MAX_PREDICTION_RATIO = 2.0f

        private const val VIDEO_PERSON_BASE_CENTER_DISTANCE = 0.14f

        private const val VIDEO_PERSON_CENTER_DISTANCE_GROWTH = 0.20f

        private const val VIDEO_PERSON_MAX_CENTER_DISTANCE = 0.34f

        private const val VIDEO_PERSON_MAX_SIZE_RATIO = 4.0f

        private const val VIDEO_PERSON_MATCH_MIN_SCORE = 45

        private const val VIDEO_PERSON_BASE_MATCH_SCORE = 100

        private const val VIDEO_PERSON_CENTER_PENALTY = 200f

        private const val VIDEO_PERSON_TIME_PENALTY_DIVISOR_MS = 40L

        private const val VIDEO_PERSON_SIZE_RATIO_PENALTY = 18f

        private const val VIDEO_PERSON_TRACKING_ID_BONUS = 35

        private const val VIDEO_PERSON_HASH_BONUS_PER_BIT = 2

        private const val VIDEO_TRACKLET_MIN_NON_OVERLAP_MS = 100L

        private const val VIDEO_TRACKLET_MAX_STITCH_GAP_MS = 8_000L

        private const val VIDEO_TRACKLET_REPRESENTATIVE_COUNT = 3

        private const val VIDEO_TRACKLET_DHASH_PENALTY = 2

        private const val VIDEO_TRACKLET_AHASH_PENALTY = 1

        private const val VIDEO_TRACKLET_HISTOGRAM_BONUS = 60f

        private const val VIDEO_TRACKLET_MIN_APPEARANCE_SCORE = 78

        private const val VIDEO_TRACKLET_GAP_PENALTY_DIVISOR_MS = 120L

        private const val VIDEO_TRACKLET_STITCH_MIN_SCORE = 62

        private const val VIDEO_MAX_CANDIDATE_YAW = 80f

        private const val VIDEO_MAX_CANDIDATE_PITCH = 50f

        private const val VIDEO_YAW_FREE_ANGLE = 15f

        private const val VIDEO_YAW_PENALTY_PER_DEGREE = 12f

        private const val VIDEO_MAX_RESCUE_UPLOADS = 5

        private const val VIDEO_RESCUE_MIN_SKIN_RATIO = 0.004f

        private const val VIDEO_RESCUE_SKIN_SCORE_WEIGHT = 12_000f

        private const val VIDEO_RESCUE_SKIN_SAMPLE_SIDE = 240

        private const val VIDEO_RESCUE_FACE_MASK_PADDING = 0.18f

        private const val VIDEO_RESCUE_MASK_MIN_FACE_SIDE = 35

        private const val VIDEO_RESCUE_MASK_MAX_YAW = 55f

        private const val VIDEO_RESCUE_MASK_MAX_PITCH = 45f

        private const val VIDEO_RESCUE_STRONG_HASH_DISTANCE = 8

        private const val VIDEO_RESCUE_RELAXED_HASH_DISTANCE = 15

        private const val VIDEO_RESCUE_CONTINUITY_GAP_MS = 1800L

        private const val VIDEO_RESCUE_CLUSTER_MAX_GAP_MS = 1000L

        private const val VIDEO_RESCUE_MAX_CENTER_DISTANCE = 0.24f

        private const val VIDEO_RESCUE_RELAXED_CENTER_DISTANCE = 0.32f

        private const val VIDEO_RESCUE_MAX_SIZE_RATIO = 4.5f

        private const val VIDEO_RESCUE_PERSON_MATCH_MIN_SCORE = 48

        private const val VIDEO_RESCUE_LOCAL_COVERAGE_GAP_MS = 1800L

        private const val VIDEO_RESCUE_LOCAL_MAX_CENTER_DISTANCE = 0.28f

        private const val VIDEO_RESCUE_LOCAL_MAX_SIZE_RATIO = 8.0f

        private const val VIDEO_RESCUE_SIDE_REPLACEMENT_GAP_MS = 900L

        private const val VIDEO_RESCUE_REPLACE_MIN_YAW = 40f

        private const val VIDEO_RESCUE_REPLACE_MAX_LOCAL_QUALITY = 30

        private const val VIDEO_RESCUE_LOCAL_MAX_DHASH_DISTANCE = 28

        private const val VIDEO_RESCUE_TRACK_SIGNATURE_GAP_MS = 900L

        private const val VIDEO_RESCUE_TRACK_MAX_CENTER_DISTANCE = 0.32f

        private const val VIDEO_RESCUE_TRACK_MAX_SIZE_RATIO = 10.0f

        private const val VIDEO_RESCUE_TRACK_MAX_DHASH_DISTANCE = 30

        private const val VIDEO_RESCUE_TRACK_MIN_HISTOGRAM_SIMILARITY = 0.82f

        private const val VIDEO_RESCUE_SOURCE_TRACK_GAP_MS = 800L

        private const val VIDEO_RESCUE_SOURCE_MAX_TRACK_DISTANCE = 0.24f

        private const val VIDEO_RESCUE_SOURCE_MAX_SIZE_RATIO = 6.0f

        private const val VIDEO_RESCUE_SOURCE_PROXIMITY_PADDING = 0.12f

        private const val VIDEO_RESCUE_SOURCE_MAX_REGION_GAP = 0.04f

        private const val VIDEO_FACE_HASH_DUP_DISTANCE = 5

        private const val VIDEO_CROSS_TRACK_HASH_DUP_DISTANCE = 5

        private const val VIDEO_HASH_SIZE = 8

        private const val VIDEO_DHASH_WIDTH = 8

        private const val VIDEO_DHASH_HEIGHT = 8

        private const val VIDEO_APPEARANCE_SAMPLE_SIDE = 64

        private const val VIDEO_APPEARANCE_HUE_BINS = 12

        private const val VIDEO_APPEARANCE_VALUE_BINS = 4

        private const val VIDEO_SHARPNESS_SAMPLE_SIDE = 160

        private const val VIDEO_PROGRESS_HIDE_DELAY_MS = 1200L

        private const val VIDEO_PULL_HINT_DISTANCE_DP = 28

        private const val VIDEO_PULL_REFRESH_DISTANCE_DP = 72

        private const val REALTIME_STREAM_PREVIEW_MAX_SIDE = 720

        private const val REALTIME_STREAM_DETECT_INTERVAL_MS = 700L

        private const val REALTIME_STREAM_CODEC_TIMEOUT_US = 10_000L

        private const val REALTIME_STREAM_MAX_IDLE_LOOPS = 3_000

        private const val REALTIME_STREAM_MAX_INSPECTED_FRAMES = 600

        private const val REALTIME_STREAM_MAX_TEST_DURATION_MS = 5L * 60L * 1000L

        private const val REALTIME_STREAM_LOG_EVERY_INSPECTIONS = 10

        private const val REALTIME_MAIN_PREVIEW_LOG_EVERY_FRAMES = 60L

        private const val REALTIME_FACE_LOG_INTERVAL_MS = 3000L

        private const val REALTIME_PREVIEW_FACE_DETECT_TIMEOUT_MS = 1_800L

        private const val REALTIME_PREVIEW_DETECT_INTERVAL_MS = 150L

        private const val REALTIME_PREVIEW_HEALTH_LOG_INTERVAL_MS = 2_000L

        private const val REALTIME_PREVIEW_HEALTH_RTMP_DATA_FRESH_MS = 5_000L

        private const val REALTIME_PREVIEW_HEALTH_MIN_VIDEO_TAGS = 30L

        private const val REALTIME_PREVIEW_RECEIVE_STALL_MS = 3_000L

        private const val REALTIME_PREVIEW_RENDER_STALL_MS = 2_500L

        private const val REALTIME_OVERLAY_HOLD_MS = 600L

        private const val REALTIME_SHARPNESS_SAMPLE_MAX_SIDE = 120

        private const val REALTIME_PREVIEW_PROCESS_STALL_MS = 3_500L

        private const val REALTIME_RESULT_STATUS_HOLD_MS = 12_000L

        private const val REALTIME_MAX_RESULT_TRACKS = 8

        private const val REALTIME_RECORD_DUPLICATE_WINDOW_MS = 30_000L

        private const val REALTIME_RECORD_DEDUPE_CACHE_MS = 2L * 60L * 1000L

        private const val REALTIME_CANDIDATE_MAX_AGE_MS = 3_000L

        private const val REALTIME_LOST_FACE_FLUSH_MS = 450L

        private const val REALTIME_LOOKBACK_WINDOW_MS = 800L

        private const val REALTIME_ENABLE_ML_LOOKBACK_RECHECK = false

        private const val REALTIME_LOOKBACK_FRAME_INTERVAL_MS = 100L

        private const val REALTIME_LOOKBACK_MAX_FRAMES = 8

        private const val REALTIME_LOOKBACK_FACE_DETECT_TIMEOUT_MS = 450L

        private const val REALTIME_LOOKBACK_TOTAL_BUDGET_MS = 900L

        private const val REALTIME_LOOKBACK_MIN_QUALITY_GAIN = 120

        private const val REALTIME_LOOKBACK_MIN_QUALITY_RATIO = 1.12f

        private const val REALTIME_LOOKBACK_MIN_SUITABILITY_GAIN = 100

        private const val REALTIME_LOOKBACK_MAX_CENTER_DISTANCE = 0.16f

        private const val REALTIME_LOOKBACK_MAX_SIZE_RATIO = 3.0f

        private val REALTIME_FACE_BOX_READY_COLOR = Color.rgb(33, 150, 243)

        private val REALTIME_FACE_BOX_WAITING_COLOR = Color.rgb(255, 152, 0)

        private val REALTIME_FACE_BOX_LOW_QUALITY_COLOR = Color.rgb(244, 67, 54)

        private const val REALTIME_TRACK_STALE_MS = 8_000L

        private const val REALTIME_TRACK_MATCH_GAP_MS = 2_500L

        private const val REALTIME_TRACK_MAX_CENTER_DISTANCE = 0.22f

        private const val REALTIME_TRACK_MAX_SIZE_RATIO = 4.0f

        private const val REALTIME_CROWD_TRACK_MAX_CENTER_DISTANCE = 0.14f

        private const val REALTIME_CROWD_TRACK_MAX_SIZE_RATIO = 2.2f

        private const val REALTIME_TRACK_ID_TRUST_GAP_MS = 900L

        private const val REALTIME_TRACK_ID_CENTER_RELAX_RATIO = 1.45f

        private const val REALTIME_TRACK_ID_SIZE_RELAX_RATIO = 1.35f

        private const val REALTIME_TRACK_CANDIDATE_HISTORY_MS = 1_200L

        private const val REALTIME_TRACK_CANDIDATE_HISTORY_MAX = 10

        private const val REALTIME_BEST_CANDIDATE_QUALITY_GAIN = 120

        private const val REALTIME_BEST_CANDIDATE_SUITABILITY_GAIN = 100

        private const val REALTIME_BEST_CANDIDATE_CLOSE_QUALITY_GAP = 80

        private const val REALTIME_BEST_CANDIDATE_POSE_GAIN_DEGREES = 8f

        private const val REALTIME_BEST_CANDIDATE_AREA_RATIO = 1.25f

        private const val REALTIME_MIN_FACE_AREA_RATIO = 0.0018f

        private const val REALTIME_FACE_AREA_BONUS_MAX = 900

        private const val REALTIME_FACE_AREA_BONUS_FULL_RATIO = 0.04f

        private const val REALTIME_FACE_AREA_GATE_BONUS_MAX = 220

        private const val REALTIME_MIN_UPLOAD_QUALITY = 250

        private const val REALTIME_IMMEDIATE_UPLOAD_QUALITY = 900

        private const val REALTIME_SIDE_PROFILE_MIN_YAW = 35f

        private const val REALTIME_SIDE_PROFILE_MIN_UPLOAD_QUALITY = 70

        private const val REALTIME_MAX_UPLOAD_YAW = 80f

        private const val REALTIME_MAX_UPLOAD_PITCH = 55f

        private const val REALTIME_CLOUD_COLLECT_WINDOW_MS = 1_200L

        private const val REALTIME_CLOUD_PERSON_COOLDOWN_MS = 30_000L

        private const val REALTIME_CLOUD_NO_MATCH_RETRY_COOLDOWN_MS = 5_000L

        private const val REALTIME_CLOUD_MAX_CONCURRENT_REQUESTS = 2

        private const val REALTIME_CLOUD_DISPATCH_INTERVAL_MS = 600L

        private const val REALTIME_CLOUD_SCHEDULE_WAIT_LOG_INTERVAL_MS = 2_000L

        private const val REALTIME_CLOUD_FAILURE_PRIORITY_PENALTY_MAX = 3

        private const val REALTIME_CLOUD_HTTP_MAX_IN_FLIGHT = 2

        private const val REALTIME_CLOUD_HTTP_ROLLING_WINDOW_MS = 10_000L

        private const val REALTIME_CLOUD_HTTP_ROLLING_MAX_REQUESTS = 10

        private const val REALTIME_CLOUD_BUDGET_LOG_INTERVAL_MS = 2_000L

        private const val REALTIME_RESCUE_MIN_INTERVAL_MS = 2_500L

        private const val REALTIME_RESCUE_TRACK_NO_FACE_COOLDOWN_MS = 8_000L

        private const val REALTIME_RESCUE_MAX_IN_FLIGHT = 1

        private const val REALTIME_RESCUE_QUEUE_MAX = 6

        private const val REALTIME_RESCUE_CANDIDATE_MAX_AGE_MS = 2_500L

        private const val REALTIME_RESCUE_MIN_FACE_SIDE_PX = 35

        private const val REALTIME_RESCUE_MAX_PRIMARY_FACE_SIDE_PX = 60

        private const val REALTIME_RESCUE_MIN_FACE_AREA_RATIO = 0.0006f

        private const val REALTIME_RESCUE_MIN_SKIN_RATIO = 0.035f

        private const val REALTIME_RESCUE_MIN_QUALITY = 260

        private const val REALTIME_RESCUE_NO_LOCAL_FACE_INTERVAL_MS = 5_000L

        private const val REALTIME_RESCUE_NO_LOCAL_MIN_SKIN_RATIO = 0.006f

        private const val REALTIME_RESCUE_CLOUD_MAX_FACE_NUM = 5

        private const val REALTIME_UPLOAD_MIN_SIDE = 384

        private const val REALTIME_RETRY_UPLOAD_MIN_SIDE = 512

        private const val REALTIME_WIDE_FIRST_MAX_FACE_SIDE_PX = 86

        private const val REALTIME_WIDE_NO_MATCH_PRIMARY_RETRY_MIN_FACE_SIDE_PX = 96

        private const val REALTIME_WIDE_NO_MATCH_PRIMARY_RETRY_MIN_QUALITY = 700

        private const val REALTIME_WIDE_NO_MATCH_PRIMARY_RETRY_MIN_DISPATCH_SCORE = 1_000

        private const val REALTIME_FACE_CROP_HORIZONTAL_PADDING = 1.10f

        private const val REALTIME_FACE_CROP_TOP_PADDING = 1.00f

        private const val REALTIME_FACE_CROP_BOTTOM_PADDING = 1.30f

        private const val REALTIME_RETRY_FACE_CROP_HORIZONTAL_PADDING = 1.80f

        private const val REALTIME_RETRY_FACE_CROP_TOP_PADDING = 1.60f

        private const val REALTIME_RETRY_FACE_CROP_BOTTOM_PADDING = 2.00f

        private const val REALTIME_CROWD_MODE_MIN_FACES = 4

        private const val REALTIME_CROWD_MODE_MIN_TRACKS = 4

        private const val REALTIME_CROWD_MODE_HOLD_MS = 4_000L

        private const val REALTIME_CROWD_CLOUD_MAX_CONCURRENT_REQUESTS = 3

        private const val REALTIME_CROWD_CLOUD_DISPATCH_INTERVAL_MS = 200L

        private const val REALTIME_CROWD_CLOUD_COLLECT_WINDOW_MS = 600L

        private const val REALTIME_CROWD_LOST_FACE_UPLOAD_MS = 450L

        private const val REALTIME_CROWD_IMMEDIATE_UPLOAD_QUALITY = 650

        private const val REALTIME_CROWD_MIN_FACE_AREA_RATIO = 0.0012f

        private const val REALTIME_CROWD_MIN_UPLOAD_QUALITY = 180

        private const val REALTIME_CROWD_SIDE_PROFILE_MIN_UPLOAD_QUALITY = 50

        private const val REALTIME_HARD_MIN_CLOUD_FACE_SIDE_PX = 50

        private const val REALTIME_MIN_CLOUD_FACE_SIDE_PX = 60

        private const val REALTIME_CROWD_MIN_CLOUD_FACE_SIDE_PX = 56

        private const val REALTIME_TINY_CLOUD_FACE_MIN_QUALITY = 2_200

        private const val REALTIME_TINY_CLOUD_FACE_MAX_YAW = 25f

        private const val REALTIME_TINY_CLOUD_FACE_MAX_PITCH = 35f

        private const val REALTIME_TINY_CLOUD_FACE_MIN_SKIN_RATIO = 0.16f

        private const val REALTIME_FACE_SKIN_SAMPLE_SIDE = 32

        private const val REALTIME_MAX_FACE_BOX_ASPECT_RATIO = 2.25f

        private const val REALTIME_MIN_FACE_BOX_SIDE_PX = 32

        private const val REALTIME_SMALL_FACE_SIDE_PX = 46

        private const val REALTIME_CROWD_SMALL_FACE_SIDE_PX = 48

        private const val REALTIME_SMALL_FACE_AREA_RATIO = 0.0024f

        private const val REALTIME_CROWD_SMALL_FACE_AREA_RATIO = 0.0020f

        private const val REALTIME_SMALL_FACE_MIN_SKIN_RATIO = 0.055f

        private const val REALTIME_SMALL_FACE_MIN_QUALITY = 520

        private const val REALTIME_FACE_EDGE_MARGIN_PX = 2

        private const val REALTIME_TINY_SIDE_FACE_YAW = 60f

        private const val REALTIME_TINY_SIDE_FACE_MIN_SIDE_PX = 58

        private const val REALTIME_TINY_SIDE_FACE_MIN_SKIN_RATIO = 0.10f

        private const val REALTIME_TINY_FACE_MAX_PITCH = 45f

        private const val REALTIME_TINY_FACE_HIGH_PITCH_MIN_QUALITY = 900

        private const val REALTIME_NO_FACE_SUPPRESS_BASE_MS = 6_000L

        private const val REALTIME_NO_FACE_SUPPRESS_MAX_MS = 18_000L

        private const val REALTIME_NO_FACE_SUPPRESS_LOG_INTERVAL_MS = 3_000L

        private const val REALTIME_NO_FACE_SUPPRESS_AREA_BREAK_RATIO = 1.8f

        private const val REALTIME_NO_FACE_SUPPRESS_QUALITY_BREAK_GAIN = 500

        private const val REALTIME_NO_FACE_SUPPRESS_QUALITY_BREAK_RATIO = 1.7f

        private const val REALTIME_NO_FACE_SUPPRESS_SIDE_BREAK_PX = 14

        private const val REALTIME_NO_FACE_BREAK_HIGH_QUALITY = 1_200

        private const val REALTIME_NO_FACE_BREAK_MAX_YAW = 15f

        private const val REALTIME_NO_FACE_BREAK_MAX_PITCH = 25f

        private const val REALTIME_QUALITY_JUMP_MIN_GAIN = 350

        private const val REALTIME_QUALITY_JUMP_MIN_RATIO = 1.5f

        private const val REALTIME_SIZE_JUMP_MIN_AREA_RATIO = 1.8f

        private const val REALTIME_SIZE_JUMP_MIN_SIDE_GAIN_PX = 24

        private const val REALTIME_LOST_FACE_COOLDOWN_BREAK_QUALITY = 900

        private const val REALTIME_LOST_FACE_COOLDOWN_BREAK_GATE_QUALITY = 900

        private const val REALTIME_LOST_FACE_COOLDOWN_BREAK_MIN_AREA = 0.004f

        private const val REALTIME_LOST_FACE_COOLDOWN_BYPASS_MIN_SIDE_PX = 60

        private const val REALTIME_LOST_FACE_COOLDOWN_BYPASS_MIN_QUALITY = 350

        private const val REALTIME_LOST_FACE_COOLDOWN_BYPASS_MIN_GATE_QUALITY = 400

        private const val REALTIME_LOST_FACE_COOLDOWN_BYPASS_MIN_DISPATCH_SCORE = 500

        private const val RTMP_RECEIVER_PORT = 1935

        private const val RTMP_RECEIVER_RESTART_DELAY_MS = 300L

        private const val RTMP_PUSH_APP_NAME = "live"

        private const val DEFAULT_RTMP_STREAM_KEY = "rokid"

        private const val DEFAULT_CLOUD_MAX_FACE_NUM = 5

        private const val CLOUD_MAX_FACE_NUM = 10

        private const val PAGE_CAPTURE = "capture"

        private const val PAGE_GALLERY = "gallery"

        private const val PAGE_VIDEO = "video"

        private const val PAGE_HISTORY = "history"

        private const val PAGE_SETTINGS = "settings"

        private const val HISTORY_PREFS_NAME = "recognition_history"

        private const val HISTORY_PREFS_KEY = "records"

        private const val GALLERY_PREFS_NAME = "gallery_state"

        private const val GALLERY_PREF_PROCESSED_KEYS = "processed_photo_keys"

        private const val PROCESSED_GALLERY_KEY_LIMIT = 1000

        private const val CAPTURE_PREFS_NAME = "capture_params"

        private const val CAPTURE_PREF_WIDTH = "width"

        private const val CAPTURE_PREF_HEIGHT = "height"

        private const val CAPTURE_PREF_QUALITY = "quality"

        private const val SOUND_PREFS_NAME = "sound_settings"

        private const val SOUND_PREF_ENABLED = "sound_prompt_enabled"

        private const val SHARE_PREFS_NAME = "share_settings"

        private const val SHARE_PREF_ENABLED = "share_enabled"

        private const val SHARE_PREF_NICKNAME = "share_nickname"

        private const val SHARE_PREF_DEVICE_ID = "share_device_id"

        private const val SHARE_PREF_RECORDS = "share_records"

        private const val SHARE_PREF_DELETED_IDS = "share_deleted_ids"

        private const val DEFAULT_SHARE_NICKNAME = "未命名设备"

        private const val SHARED_RECORD_POLL_MS = 5_000L

        private const val SHARED_RECORD_RETENTION_MS = 60L * 60L * 1000L

        private const val SHARED_DELETED_ID_RETENTION_MS = SHARED_RECORD_RETENTION_MS + 5L * 60L * 1000L

        private const val SHARED_ORIGINAL_PREFETCH_LIMIT = 3

        private const val SHARED_ORIGINAL_CACHE_DIR = "shared_originals"

        private const val SHARED_ORIGINAL_CACHE_SUFFIX = "_original.jpg"

        private const val SHARE_PUBLISH_MAX_RETRIES = 3

        private const val SHARE_PUBLISH_RETRY_DELAY_MS = 1_500L

        private const val HISTORY_RETENTION_MS = 3L * 24L * 60L * 60L * 1000L

        private const val STATUS_CAPTURING = "capturing"

        private const val STATUS_LOCAL_PROCESSING = "local_processing"

        private const val STATUS_UPLOADING = "uploading"

        private const val STATUS_SUCCESS = "success"

        private const val STATUS_NO_FACE = "no_face"

        private const val STATUS_NO_MATCH = "no_match"

        private const val STATUS_FAILED = "failed"

        private const val STATUS_INTERRUPTED = "interrupted"

        private val REQUIRED_GLASS_PERMISSIONS = arrayOf(

            GlassPermission.CAMERA,

            GlassPermission.MEDIA

        )

    }

}

data class RecognitionRecord(

    var id: String = "",

    var createdAt: Long = 0L,

    var updatedAt: Long = 0L,

    var status: String = "",

    var statusText: String = "",

    var errorMessage: String? = null,

    var originalImagePath: String? = null,

    var uploadImagePath: String? = null,

    var originalWidth: Int = 0,

    var originalHeight: Int = 0,

    var uploadWidth: Int = 0,

    var uploadHeight: Int = 0,

    var faceRectImageWidth: Int = 0,

    var faceRectImageHeight: Int = 0,

    var uploadSourceRect: FaceRect? = null,

    var localFaceRects: MutableList<FaceRect> = mutableListOf(),

    var sharePending: Boolean = false,

    var shareRetryCount: Int = 0,

    var sharedAt: Long = 0L,

    var sharedShareId: String? = null,

    var experts: MutableList<ExpertInfo> = mutableListOf()

)

data class SharedRecognitionRecord(

    var shareId: String = "",

    var clientRecordId: String = "",

    var deviceId: String = "",

    var nickname: String = "",

    var source: String = "",

    var capturedAt: Long = 0L,

    var createdAt: Long = 0L,

    var expiresAt: Long = 0L,

    var originalUrl: String = "",

    var faceUrl: String = "",

    var originalWidth: Int = 0,

    var originalHeight: Int = 0,

    var uploadWidth: Int = 0,

    var uploadHeight: Int = 0,

    var faceRectImageWidth: Int = 0,

    var faceRectImageHeight: Int = 0,

    var uploadSourceRect: FaceRect? = null,

    var expert: ExpertInfo = ExpertInfo("-", "无工作单位", "未填写", "-", "-", 0f, "", null)

)

data class HistoryRecordItem(

    val createdAt: Long,

    val localRecord: RecognitionRecord? = null,

    val sharedRecord: SharedRecognitionRecord? = null

)

data class DecodedBitmap(

    val bitmap: Bitmap,

    val sampleSize: Int,

    val exifOrientation: Int,

    val originalWidth: Int,

    val originalHeight: Int

)

data class GalleryPhoto(

    val uri: Uri,

    val displayName: String,

    val dateTaken: Long,

    val sizeBytes: Long,

    val width: Int,

    val height: Int

)

data class GalleryVideo(

    val uri: Uri,

    val displayName: String,

    val dateTaken: Long,

    val sizeBytes: Long,

    val width: Int,

    val height: Int,

    val durationMs: Long

)

data class VideoMetadata(

    val width: Int,

    val height: Int,

    val durationMs: Long

)

data class FaceUploadImage(

    val bitmap: Bitmap,

    val sourceCropRect: Rect,

    val localFaceRects: List<FaceRect>

)

data class ExpertInfo(

    val name: String,

    val company: String,

    val major: String,

    val phone: String,

    val idCard: String? = "-",

    val score: Float,

    val photoPath: String,

    val faceRect: FaceRect?

)

data class FaceRect(

    val x: Float,

    val y: Float,

    val width: Float,

    val height: Float

) {

    fun isNormalized(): Boolean {

        return x in 0f..1f && y in 0f..1f && width in 0f..1f && height in 0f..1f

    }

    fun toPixelRect(imageWidth: Int, imageHeight: Int): Rect? {

        if (imageWidth <= 0 || imageHeight <= 0 || width <= 0f || height <= 0f) {

            return null

        }

        val leftFloat: Float

        val topFloat: Float

        val widthFloat: Float

        val heightFloat: Float

        if (isNormalized()) {

            leftFloat = x * imageWidth

            topFloat = y * imageHeight

            widthFloat = width * imageWidth

            heightFloat = height * imageHeight

        } else {

            leftFloat = x

            topFloat = y

            widthFloat = width

            heightFloat = height

        }

        val left = leftFloat.roundToInt().coerceIn(0, imageWidth)

        val top = topFloat.roundToInt().coerceIn(0, imageHeight)

        val right = (leftFloat + widthFloat).roundToInt().coerceIn(0, imageWidth)

        val bottom = (topFloat + heightFloat).roundToInt().coerceIn(0, imageHeight)

        if (right <= left || bottom <= top) {

            return null

        }

        return Rect(left, top, right, bottom)

    }

}

data class FaceCropCandidate(

    val label: String,

    val bitmap: Bitmap

)

data class RealtimeFaceEvaluation(
    val faceRect: Rect,
    val qualityScore: Int,
    val dispatchScore: Int,
    val cloudGateQuality: Int,
    val sharpnessScore: Int,
    val areaBonus: Int,
    val canUpload: Boolean,
    val rejectReason: String,
    val faceAreaRatio: Float,
    val faceCenterX: Float,
    val faceCenterY: Float,
    val skinRatio: Float
)

data class RealtimeCloudCandidateDecision(
    val canUpload: Boolean,
    val rejectReason: String
)

data class RealtimeFaceEvaluationSummary(
    val evaluations: Map<Face, RealtimeFaceEvaluation>,
    val detectedCount: Int,
    val eligibleCount: Int,
    val uploadableCount: Int,
    val skippedInvalid: Int,
    val skippedTooSmall: Int,
    val skippedSmallArea: Int,
    val skippedPose: Int,
    val skippedLikelyFalsePositive: Int,
    val skippedQuality: Int
) {
    companion object {
        fun empty(): RealtimeFaceEvaluationSummary {
            return RealtimeFaceEvaluationSummary(
                evaluations = emptyMap(),
                detectedCount = 0,
                eligibleCount = 0,
                uploadableCount = 0,
                skippedInvalid = 0,
                skippedTooSmall = 0,
                skippedSmallArea = 0,
                skippedPose = 0,
                skippedLikelyFalsePositive = 0,
                skippedQuality = 0
            )
        }
    }
}

data class RealtimeOverlayBox(
    val rect: Rect,
    val color: Int,
    val label: String
)

data class RealtimeOverlayState(
    val color: Int,
    val label: String,
    val readyForCloud: Boolean,
    val waiting: Boolean
)

data class RealtimeOverlaySnapshot(
    val boxes: List<RealtimeOverlayBox>,
    val frameWidth: Int,
    val frameHeight: Int,
    val createdAt: Long,
    val statusText: String,
    val readyCount: Int,
    val waitingCount: Int,
    val lowQualityCount: Int
)

data class RealtimeFaceScore(
    val qualityScore: Int,
    val dispatchScore: Int,
    val sharpnessScore: Int,
    val areaBonus: Int
)

data class RealtimeHistorySelection(
    val candidate: RealtimeFaceCandidate?,
    val historySize: Int,
    val qualityGain: Int,
    val suitabilityGain: Int,
    val reason: String
)

data class RealtimeFaceCandidate(
    val createdAt: Long,
    val decodedFrames: Long,
    val qualityScore: Int,
    val dispatchScore: Int,
    val cloudGateQuality: Int,
    val sharpnessScore: Int,
    val areaBonus: Int,
    val frameBytes: ByteArray,
    val frameWidth: Int,
    val frameHeight: Int,
    val faceRectInFrame: Rect,
    val faceAreaRatio: Float,
    val faceCenterX: Float,
    val faceCenterY: Float,
    val yaw: Float,
    val pitch: Float,
    val roll: Float,
    val skinRatio: Float,
    val trackingId: Int?
)

data class RealtimeLookbackFrame(
    val receivedAt: Long,
    val decodedFrames: Long,
    val jpegBytes: ByteArray
)

data class RtmpPreviewFramePacket(
    val jpegBytes: ByteArray,
    val width: Int,
    val height: Int,
    val decodedFrames: Long
)

data class RealtimeUploadPayload(
    val uploadBytes: ByteArray,
    val uploadWidth: Int,
    val uploadHeight: Int,
    val localFaceRect: FaceRect,
    val sourceCropRect: FaceRect,
    val cropMode: String,
    val cropWidth: Int,
    val cropHeight: Int
)

data class RealtimeCloudBudgetPermit(
    val kind: String,
    val trackId: Long?,
    val rescue: Boolean,
    val startedAt: Long
)

data class RealtimeRescueCandidate(
    val createdAt: Long,
    val decodedFrames: Long,
    val frameBytes: ByteArray,
    val frameWidth: Int,
    val frameHeight: Int,
    val reason: String,
    val priority: Int,
    val sourceTrackId: Long?,
    val sourceFaceRect: Rect?,
    val qualityScore: Int,
    val dispatchScore: Int,
    val skinRatio: Float,
    val localFaceCount: Int,
    val maxFaceNum: Int
)

data class RealtimeRescueUploadPlan(
    val sessionId: Long,
    val candidate: RealtimeRescueCandidate,
    val budgetPermit: RealtimeCloudBudgetPermit
)

data class RealtimeRescueTrackHint(
    val trackId: Long,
    val lastSeenAt: Long,
    val neverUploaded: Boolean,
    val matchedRecently: Boolean,
    val consecutiveFailures: Int
)

data class RealtimePersonTrack(
    val id: Long,
    var trackingId: Int?,
    val firstSeenAt: Long,
    var lastSeenAt: Long,
    var centerX: Float,
    var centerY: Float,
    var sizeRatio: Float,
    var bestCandidate: RealtimeFaceCandidate? = null,
    val candidateHistory: ArrayDeque<RealtimeFaceCandidate> = ArrayDeque(),
    var lastCloudUploadAt: Long = 0L,
    var lastCloudUploadQuality: Int = 0,
    var lastCloudUploadAreaRatio: Float = 0f,
    var lastCloudUploadFaceWidth: Int = 0,
    var lastCloudUploadFaceHeight: Int = 0,
    var lastCloudUploadMatched: Boolean = false,
    var lastCloudUploadNoFace: Boolean = false,
    var cloudRequestInFlight: Boolean = false,
    var lastMatchedNames: String = "",
    var consecutiveNoFaceCount: Int = 0,
    var consecutiveNoMatchCount: Int = 0,
    var noFaceSuppressedUntil: Long = 0L,
    var lastNoFaceSuppressLogAt: Long = 0L,
    var lastNoFaceAt: Long = 0L,
    var lastNoFaceQuality: Int = 0,
    var lastNoFaceAreaRatio: Float = 0f,
    var lastNoFaceFaceWidth: Int = 0,
    var lastNoFaceFaceHeight: Int = 0
)

data class RealtimeCloudUploadPlan(
    val sessionId: Long,
    val trackId: Long,
    val candidate: RealtimeFaceCandidate,
    val reason: String,
    val activeCountAtStart: Int,
    val maxConcurrent: Int,
    val crowdMode: Boolean,
    val batchIndex: Int,
    val noFaceCountAtStart: Int,
    val noFaceSuppressedUntilAtStart: Long,
    val initialBudgetPermit: RealtimeCloudBudgetPermit
)

data class LocalIpv4Candidate(
    val address: String,
    val interfaceName: String
)

data class SavedFaceCrop(

    val path: String,

    val width: Int,

    val height: Int

)

data class VideoFaceCandidate(

    val frameTimeMs: Long,

    val qualityScore: Int,

    val faceHash: Long,

    val differenceHash: Long,

    val mirroredDifferenceHash: Long,

    val appearanceHistogram: IntArray,

    var originalBytes: ByteArray?,

    val originalBitmap: Bitmap?,

    val originalWidth: Int,

    val originalHeight: Int,

    val uploadBytes: ByteArray,

    val uploadWidth: Int,

    val uploadHeight: Int,

    val localFaceRect: FaceRect,

    val sourceCropRect: FaceRect,

    val faceAreaRatio: Float,

    val faceCenterX: Float,

    val faceCenterY: Float,

    val yaw: Float,

    val roll: Float,

    val trackingId: Int? = null,

    val isRescueFrame: Boolean = false,

    var personTrackSignatures: List<VideoPersonSignature> = emptyList(),

    val rescueSourceDetectedFaceRects: List<FaceRect> = emptyList(),

    val rescueRegionRect: FaceRect? = null

)

data class VideoRescueObservation(

    val frameTimeMs: Long,

    val qualityScore: Int,

    val regionHash: Long,

    val skinRatio: Float,

    val localFaceCount: Int,

    val knownFaceRects: List<FaceRect>,

    val detectedFaceRects: List<FaceRect>,

    val unmaskedDetectedFaceCount: Int,

    val regionRect: FaceRect?,

    val regionCenterX: Float,

    val regionCenterY: Float,

    val regionAreaRatio: Float

)

data class VideoRescueRegionAnalysis(

    val skinRatio: Float = 0f,

    val regionHash: Long = 0L,

    val regionRect: FaceRect? = null,

    val regionCenterX: Float = 0.5f,

    val regionCenterY: Float = 0.5f,

    val regionAreaRatio: Float = 0f

)

data class VideoCloudMatch(

    val candidate: VideoFaceCandidate,

    val expert: ExpertInfo

)

data class VideoPersonSignature(

    val frameTimeMs: Long,

    val qualityScore: Int,

    val differenceHash: Long,

    val mirroredDifferenceHash: Long,

    val appearanceHistogram: IntArray,

    val faceAreaRatio: Float,

    val faceCenterX: Float,

    val faceCenterY: Float,

    val yaw: Float

)

data class CloudFaceSearchResult(

    val experts: List<ExpertInfo>,

    val message: String

)

