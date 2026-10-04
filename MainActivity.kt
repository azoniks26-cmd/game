package com.varazdp.wararena

import android.annotation.SuppressLint
import android.app.Activity
import android.content.Intent
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Color
import android.graphics.PixelFormat
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.content.SharedPreferences
import android.media.AudioAttributes
import android.media.AudioFormat
import android.media.AudioManager
import android.media.AudioTrack
import android.media.MediaPlayer
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.text.InputType
import android.view.Choreographer
import android.view.Gravity
import android.view.MotionEvent
import android.view.Surface
import android.view.SurfaceHolder
import android.view.SurfaceView
import android.view.View
import android.view.View as AndroidView
import android.view.ViewGroup
import android.view.WindowInsets
import android.view.WindowInsetsController
import android.view.WindowManager
import android.widget.Button
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.ImageView
import android.widget.LinearLayout
import android.widget.ProgressBar
import android.widget.TextView
import androidx.annotation.Keep
import com.google.android.filament.ColorGrading
import com.google.android.filament.EntityManager
import com.google.android.filament.IndirectLight
import com.google.android.filament.LightManager
import com.google.android.filament.Renderer
import com.google.android.filament.View as FilView
import com.google.android.filament.utils.ModelViewer
import com.google.android.filament.utils.Utils
import org.json.JSONObject
import java.io.OutputStreamWriter
import java.net.HttpURLConnection
import java.net.URL
import java.nio.ByteBuffer
import java.nio.ByteOrder
import kotlin.concurrent.thread
import kotlin.math.cos
import kotlin.math.sin

class MainActivity : Activity() {

    companion object {
        private const val WORKER_URL = "https://wararena-auth.jafarov.workers.dev"
        init {
            Utils.init()
            System.loadLibrary("wararena")
        }
    }

    private lateinit var rootLayout: FrameLayout
    private lateinit var filView: SurfaceView
    private lateinit var uiView: SurfaceView
    private lateinit var modelViewer: ModelViewer
    private lateinit var prefs: SharedPreferences
    private val mainHandler = Handler(Looper.getMainLooper())
    private val choreographer by lazy { Choreographer.getInstance() }
    private var agentLoaded = false
    private var baseTransform: FloatArray? = null
    private var musicPlayer: MediaPlayer? = null
    private var musicVolume = 0.8f
    private var musicPath: String? = null
    private var musicStarted = false
        private var authOverlay: View? = null
    private var authImageBytes: ByteArray? = null

    private val cBg = Color.parseColor("#08070A")
    private val cPanel = Color.parseColor("#14110B")
    private val cPanel2 = Color.parseColor("#1D1810")
    private val cGold = Color.parseColor("#F4C333")
    private val cGoldDim = Color.parseColor("#8A7020")
    private val cText = Color.parseColor("#EDE6DC")
    private val cTextDim = Color.parseColor("#8E8880")
    private val cError = Color.parseColor("#E05555")

    private val frameCallback = object : Choreographer.FrameCallback {
        override fun doFrame(frameTimeNanos: Long) {
            choreographer.postFrameCallback(this)
            val t = frameTimeNanos.toDouble() / 1_000_000.0
            if (agentLoaded) {
                rotateAgent(t)
                modelViewer.render(frameTimeNanos)
            }
            nativeFrame(t)
        }
    }

    @SuppressLint("ClickableViewAccessibility")
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)

        prefs = getSharedPreferences("wa_storage", MODE_PRIVATE)
        musicVolume = (prefs.getString("music_volume", "80")?.toIntOrNull() ?: 80) / 100f

        rootLayout = FrameLayout(this)
        filView = SurfaceView(this)
        uiView = SurfaceView(this)
        uiView.setZOrderMediaOverlay(true)
        uiView.holder.setFormat(PixelFormat.TRANSLUCENT)
        rootLayout.addView(filView, FrameLayout.LayoutParams(-1, -1))
        rootLayout.addView(uiView, FrameLayout.LayoutParams(-1, -1))
        setContentView(rootLayout)

        goImmersive()

        modelViewer = ModelViewer(filView)
        val v = modelViewer.view
        v.renderQuality = v.renderQuality.apply { hdrColorBuffer = FilView.QualityLevel.HIGH }
        v.dynamicResolutionOptions = v.dynamicResolutionOptions.apply { enabled = false }
        v.multiSampleAntiAliasingOptions = v.multiSampleAntiAliasingOptions.apply { enabled = true }
        v.antiAliasing = FilView.AntiAliasing.FXAA
        v.ambientOcclusionOptions = v.ambientOcclusionOptions.apply { enabled = true }
        v.bloomOptions = v.bloomOptions.apply { enabled = true }
        v.colorGrading = ColorGrading.Builder()
            .toneMapping(ColorGrading.ToneMapping.ACES)
            .build(modelViewer.engine)

        val clear = Renderer.ClearOptions()
        clear.clear = true
        clear.clearColor = floatArrayOf(0.025f, 0.022f, 0.03f, 1f)
        modelViewer.renderer.setClearOptions(clear)

        setupLighting()

        uiView.holder.addCallback(object : SurfaceHolder.Callback {
            override fun surfaceCreated(holder: SurfaceHolder) { nativeSurface(holder.surface) }
            override fun surfaceChanged(holder: SurfaceHolder, format: Int, width: Int, height: Int) { nativeSurface(holder.surface) }
            override fun surfaceDestroyed(holder: SurfaceHolder) { nativeSurface(null) }
        })

        rootLayout.setOnTouchListener { _, event ->
            if (authOverlay != null) return@setOnTouchListener true
            val action = when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> 0
                MotionEvent.ACTION_UP -> 1
                MotionEvent.ACTION_MOVE -> 2
                else -> 3
            }
            nativeTouch(action, event.x, event.y)
            true
        }

        val version = packageManager.getPackageInfo(packageName, 0).versionName ?: "0.1.0"
        nativeInit(this, cacheDir.absolutePath, version, resources.displayMetrics.density)
    }

    private fun goImmersive() {
        try {
            if (Build.VERSION.SDK_INT >= 30) {
                window.setDecorFitsSystemWindows(false)
                window.decorView.windowInsetsController?.let { ctrl ->
                    ctrl.systemBarsBehavior = WindowInsetsController.BEHAVIOR_SHOW_TRANSIENT_BARS_BY_SWIPE
                    ctrl.hide(WindowInsets.Type.systemBars())
                }
            } else {
                @Suppress("DEPRECATION")
                window.decorView.systemUiVisibility = (
                    AndroidView.SYSTEM_UI_FLAG_FULLSCREEN
                        or AndroidView.SYSTEM_UI_FLAG_HIDE_NAVIGATION
                        or AndroidView.SYSTEM_UI_FLAG_IMMERSIVE_STICKY
                        or AndroidView.SYSTEM_UI_FLAG_LAYOUT_FULLSCREEN
                        or AndroidView.SYSTEM_UI_FLAG_LAYOUT_HIDE_NAVIGATION
                        or AndroidView.SYSTEM_UI_FLAG_LAYOUT_STABLE)
            }
        } catch (_: Throwable) {}
    }

    override fun onResume() {
        super.onResume()
        goImmersive()
        choreographer.postFrameCallback(frameCallback)
        nativeResume()
        if (musicStarted) {
            try { musicPlayer?.takeIf { !it.isPlaying }?.start() } catch (_: Exception) {}
        }
    }

    override fun onPause() {
        nativePause()
        choreographer.removeFrameCallback(frameCallback)
        musicPlayer?.takeIf { it.isPlaying }?.pause()
        super.onPause()
    }

    override fun onStop() {
        musicPlayer?.takeIf { it.isPlaying }?.pause()
        super.onStop()
    }

    override fun onDestroy() {
        choreographer.removeFrameCallback(frameCallback)
        musicPlayer?.release()
        musicPlayer = null
        if (agentLoaded) modelViewer.destroyModel()
        super.onDestroy()
    }

    @Deprecated("Deprecated in Java")
    override fun onBackPressed() { nativeBack() }

    private fun setupLighting() {
        val engine = modelViewer.engine
        val scene = modelViewer.scene
        scene.indirectLight = IndirectLight.Builder()
            .irradiance(1, floatArrayOf(0.42f, 0.40f, 0.42f))
            .intensity(30000f)
            .build(engine)
        val key = EntityManager.get().create()
        LightManager.Builder(LightManager.Type.DIRECTIONAL)
            .color(1.0f, 0.94f, 0.88f).intensity(85000f)
            .direction(-0.35f, -0.35f, -1.0f).castShadows(false)
            .build(engine, key)
        scene.addEntity(key)
        val rim = EntityManager.get().create()
        LightManager.Builder(LightManager.Type.DIRECTIONAL)
            .color(1.0f, 0.28f, 0.2f).intensity(55000f)
            .direction(0.7f, -0.15f, 0.7f).castShadows(false)
            .build(engine, rim)
        scene.addEntity(rim)
        val fill = EntityManager.get().create()
        LightManager.Builder(LightManager.Type.DIRECTIONAL)
            .color(0.55f, 0.65f, 1.0f).intensity(25000f)
            .direction(0.8f, -0.1f, -0.6f).castShadows(false)
            .build(engine, fill)
        scene.addEntity(fill)
    }

    private fun rotateAgent(t: Double) {
        val asset = modelViewer.asset ?: return
        val base = baseTransform ?: return
        val tm = modelViewer.engine.transformManager
        val inst = tm.getInstance(asset.root)
        if (inst == 0) return
        val angle = (-1.5708 + 0.18 * sin(t * 0.0006)).toFloat()
        val k = 1.15f
        val dz = 0.5f
        val c = cos(angle)
        val s = sin(angle)
        val px = base[12]; val py = base[13]; val pz = base[14]
        val rot = floatArrayOf(
            c * k, 0f, -s * k, 0f,
            0f, k, 0f, 0f,
            s * k, 0f, c * k, 0f,
            px - k * (c * px + s * pz), py - k * py, pz - k * (-s * px + c * pz) + dz, 1f)
        val out = FloatArray(16)
        for (col in 0 until 4) for (row in 0 until 4) {
            var acc = 0f
            for (k2 in 0 until 4) acc += rot[k2 * 4 + row] * base[col * 4 + k2]
            out[col * 4 + row] = acc
        }
        tm.setTransform(inst, out)
    }

    @Keep
    fun onNativeMusicReady(path: String) {
        musicPath = path
        if (prefs.getString("session_token", "").isNullOrEmpty()) return
        mainHandler.post { startMusicInternal() }
    }

    private fun startMusicInternal() {
        val p = musicPath ?: return
        if (musicStarted && musicPlayer?.isPlaying == true) return
        try {
            musicPlayer?.release()
            val mp = MediaPlayer()
            mp.setAudioStreamType(AudioManager.STREAM_MUSIC)
            mp.setDataSource(p)
            mp.isLooping = true
            mp.setVolume(musicVolume, musicVolume)
            mp.setOnPreparedListener { it.start(); musicStarted = true }
            mp.prepareAsync()
            musicPlayer = mp
        } catch (_: Exception) {}
    }

    @Keep
    fun onNativeStartMusic() {
        if (musicPath != null) mainHandler.post { startMusicInternal() } else nativeStartMusicFile()
    }

    @Keep
    fun onNativeStopMusic() {
        mainHandler.post {
            try { musicPlayer?.stop() } catch (_: Exception) {}
            try { musicPlayer?.release() } catch (_: Exception) {}
            musicPlayer = null
            musicStarted = false
        }
    }

    @Keep
    fun onNativeMusicVolume(volume: Float) {
        musicVolume = volume
        musicPlayer?.setVolume(volume, volume)
    }

    @Keep
    fun onNativeClick(pcm: ByteArray, volume: Float) {
        mainHandler.post {
            try {
                val track = AudioTrack.Builder()
                    .setAudioAttributes(
                        AudioAttributes.Builder()
                            .setUsage(AudioAttributes.USAGE_ASSISTANCE_SONIFICATION)
                            .setContentType(AudioAttributes.CONTENT_TYPE_SONIFICATION)
                            .build())
                    .setAudioFormat(
                        AudioFormat.Builder()
                            .setEncoding(AudioFormat.ENCODING_PCM_16BIT)
                            .setSampleRate(48000)
                            .setChannelMask(AudioFormat.CHANNEL_OUT_MONO)
                            .build())
                    .setTransferMode(AudioTrack.MODE_STATIC)
                    .setBufferSizeInBytes(pcm.size)
                    .build()
                track.setVolume(volume)
                track.write(pcm, 0, pcm.size)
                track.play()
                mainHandler.postDelayed({
                    try { track.stop(); track.release() } catch (_: Exception) {}
                }, 160)
            } catch (_: Exception) {}
        }
    }

    @Keep
    fun onNativeTelegram() {
        try { startActivity(Intent(Intent.ACTION_VIEW, Uri.parse("https://t.me/varazdp"))) } catch (_: Exception) {}
    }

    @Keep
    fun onNativeAgent(data: ByteArray) {
        mainHandler.post {
            try {
                val buffer = ByteBuffer.allocateDirect(data.size).order(ByteOrder.nativeOrder())
                buffer.put(data); buffer.flip()
                modelViewer.loadModelGlb(buffer)
                modelViewer.transformToUnitCube()
                val asset = modelViewer.asset
                if (asset != null) {
                    val tm = modelViewer.engine.transformManager
                    val inst = tm.getInstance(asset.root)
                    if (inst != 0) {
                        val arr = FloatArray(16)
                        tm.getTransform(inst, arr)
                        baseTransform = arr
                    }
                }
                agentLoaded = true
                nativeAgentDone()
            } catch (_: Exception) {
                agentLoaded = false
                nativeAgentDone()
            }
        }
    }

    @Keep
    fun onNativeAgentMissing() { mainHandler.post { nativeAgentDone() } }

    @Keep
    fun onNativePref(key: String): String = prefs.getString(key, "") ?: ""

    @Keep
    fun onNativeSetPref(key: String, value: String) { prefs.edit().putString(key, value).apply() }

    @Keep
    fun onNativeSessionGet(): String = prefs.getString("session_token", "") ?: ""

    @Keep
    fun onNativeSessionClear() {
        prefs.edit().remove("session_token").remove("session_nick").apply()
    }

    @Keep
    fun onNativeAuthImage(data: ByteArray) {
        authImageBytes = data
    }

    @Keep
    fun onNativeRequestExit() {
        mainHandler.post {
            try { finishAffinity() } catch (_: Exception) {}
            android.os.Process.killProcess(android.os.Process.myPid())
        }
    }

    @Keep
    fun onNativeLogout() {
        mainHandler.post {
            prefs.edit().remove("session_token").remove("session_nick").apply()
            onNativeStopMusic()
            val i = Intent(this, MainActivity::class.java)
            i.addFlags(Intent.FLAG_ACTIVITY_CLEAR_TOP or Intent.FLAG_ACTIVITY_NEW_TASK)
            startActivity(i)
            finish()
        }
    }

        @Keep
    fun onNativeShowAuth() {
        mainHandler.post { showAuthMain() }
    }

    @Keep
    fun onNativeHideAuth() {
        mainHandler.post { removeAuthOverlay() }
    }

    private fun dp(v: Float): Int = (v * resources.displayMetrics.density + 0.5f).toInt()

    private fun panelBg(radiusDp: Float = 16f, fill: Int = cPanel, strokeDp: Float = 1.5f, stroke: Int = cGold): GradientDrawable {
        return GradientDrawable().apply {
            setColor(fill)
            cornerRadius = dp(radiusDp).toFloat()
            setStroke(dp(strokeDp), stroke)
        }
    }

    private fun inputBg(): GradientDrawable {
        return GradientDrawable().apply {
            setColor(Color.parseColor("#0E0C08"))
            cornerRadius = dp(6f).toFloat()
            setStroke(dp(1f), cGoldDim)
        }
    }

    private fun solidBg(radiusDp: Float, fill: Int): GradientDrawable {
        return GradientDrawable().apply {
            setColor(fill)
            cornerRadius = dp(radiusDp).toFloat()
        }
    }

    private fun styledInput(hint: String, password: Boolean = false): EditText {
        val e = EditText(this)
        e.hint = hint
        e.textSize = 15f
        e.setTextColor(cText)
        e.setHintTextColor(cTextDim)
        e.background = inputBg()
        e.setPadding(dp(14f), dp(12f), dp(14f), dp(12f))
        e.inputType = if (password)
            InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_VARIATION_PASSWORD
        else
            InputType.TYPE_CLASS_TEXT
        return e
    }

    private fun styledButton(label: String, primary: Boolean, onClick: () -> Unit): Button {
        val b = Button(this)
        b.text = label
        b.textSize = 14f
        b.isAllCaps = false
        b.setTextColor(if (primary) Color.parseColor("#1A1408") else cGold)
        b.setTypeface(b.typeface, Typeface.BOLD)
        b.background = if (primary) solidBg(8f, cGold) else panelBg(8f, cPanel2, 1.5f, cGold)
        b.setPadding(dp(28f), dp(14f), dp(28f), dp(14f))
        b.stateListAnimator = null
        b.setOnClickListener { onClick() }
        return b
    }

    private fun addTitle(panel: LinearLayout, text: String, size: Float) {
        val title = TextView(this)
        title.text = text
        title.setTextColor(cGold)
        title.textSize = size
        title.letterSpacing = 0.18f
        title.gravity = Gravity.CENTER
        title.setTypeface(title.typeface, Typeface.BOLD)
        panel.addView(title)

        val divider = View(this)
        val dlp = LinearLayout.LayoutParams(dp(60f), dp(2f))
        dlp.topMargin = dp(14f)
        dlp.gravity = Gravity.CENTER_HORIZONTAL
        panel.addView(divider, dlp)
        divider.background = solidBg(1f, cGold)
    }

    private fun showAuthMain() {
        removeAuthOverlay()
        val overlay = FrameLayout(this)
        overlay.setBackgroundColor(cBg)

        val panel = LinearLayout(this)
        panel.orientation = LinearLayout.VERTICAL
        panel.gravity = Gravity.CENTER_HORIZONTAL
        panel.background = panelBg(16f)
        panel.setPadding(dp(28f), dp(32f), dp(28f), dp(28f))

        val lp = FrameLayout.LayoutParams(dp(300f), ViewGroup.LayoutParams.WRAP_CONTENT)
        lp.gravity = Gravity.CENTER
        overlay.addView(panel, lp)

        addTitle(panel, "AUTHORIZATION", 18f)

        val login = styledButton("LOGIN", true) { showAuthMethod(register = false) }
        val llp = LinearLayout.LayoutParams(dp(220f), ViewGroup.LayoutParams.WRAP_CONTENT)
        llp.topMargin = dp(22f)
        panel.addView(login, llp)

        val reg = styledButton("REGISTER", false) { showAuthMethod(register = true) }
        val rlp = LinearLayout.LayoutParams(dp(220f), ViewGroup.LayoutParams.WRAP_CONTENT)
        rlp.topMargin = dp(12f)
        panel.addView(reg, rlp)

        rootLayout.addView(overlay, FrameLayout.LayoutParams(-1, -1))
        authOverlay = overlay
    }

    private fun showAuthMethod(register: Boolean) {
        removeAuthOverlay()
        val overlay = FrameLayout(this)
        overlay.setBackgroundColor(cBg)

        val panel = LinearLayout(this)
        panel.orientation = LinearLayout.VERTICAL
        panel.gravity = Gravity.CENTER_HORIZONTAL
        panel.background = panelBg(16f)
        panel.setPadding(dp(28f), dp(32f), dp(28f), dp(28f))

        val lp = FrameLayout.LayoutParams(dp(320f), ViewGroup.LayoutParams.WRAP_CONTENT)
        lp.gravity = Gravity.CENTER
        overlay.addView(panel, lp)

        addTitle(panel, "CHOOSE A LOGIN METHOD", 16f)

        val imgWrap = FrameLayout(this)
        imgWrap.background = panelBg(10f, Color.parseColor("#0E0C08"), 1.5f, cGoldDim)
        imgWrap.isClickable = true
        val ilp = LinearLayout.LayoutParams(dp(260f), dp(170f))
        ilp.topMargin = dp(22f)
        panel.addView(imgWrap, ilp)

        val img = ImageView(this)
        val bytes = authImageBytes
        if (bytes != null) {
            try {
                val bmp: Bitmap = BitmapFactory.decodeByteArray(bytes, 0, bytes.size)
                img.setImageBitmap(bmp)
            } catch (_: Exception) {}
        }
        img.adjustViewBounds = true
        img.scaleType = ImageView.ScaleType.CENTER_CROP
        imgWrap.addView(img, FrameLayout.LayoutParams(-1, -1))

        val hint = TextView(this)
        hint.text = "TAP TO CONTINUE"
        hint.setTextColor(cGold)
        hint.textSize = 11f
        hint.letterSpacing = 0.2f
        hint.gravity = Gravity.CENTER
        val hlp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
        hlp.topMargin = dp(16f)
        panel.addView(hint, hlp)

        imgWrap.setOnClickListener { showAuthForm(register) }
        hint.setOnClickListener { showAuthForm(register) }

        val back = styledButton("BACK", false) { showAuthMain() }
        val blp = LinearLayout.LayoutParams(dp(220f), ViewGroup.LayoutParams.WRAP_CONTENT)
        blp.topMargin = dp(22f)
        panel.addView(back, blp)

        rootLayout.addView(overlay, FrameLayout.LayoutParams(-1, -1))
        authOverlay = overlay
    }

    private fun showAuthForm(register: Boolean) {
        removeAuthOverlay()
        val overlay = FrameLayout(this)
        overlay.setBackgroundColor(cBg)

        val panel = LinearLayout(this)
        panel.orientation = LinearLayout.VERTICAL
        panel.gravity = Gravity.CENTER_HORIZONTAL
        panel.background = panelBg(16f)
        panel.setPadding(dp(28f), dp(32f), dp(28f), dp(28f))

        val lp = FrameLayout.LayoutParams(dp(320f), ViewGroup.LayoutParams.WRAP_CONTENT)
        lp.gravity = Gravity.CENTER
        overlay.addView(panel, lp)

        addTitle(panel, if (register) "REGISTRATION" else "LOGIN", 18f)

        val nick = styledInput("Nickname")
        val nlp = LinearLayout.LayoutParams(dp(250f), ViewGroup.LayoutParams.WRAP_CONTENT)
        nlp.topMargin = dp(22f)
        panel.addView(nick, nlp)

        val pass = styledInput("Password", password = true)
        val plp = LinearLayout.LayoutParams(dp(250f), ViewGroup.LayoutParams.WRAP_CONTENT)
        plp.topMargin = dp(12f)
        panel.addView(pass, plp)

        val confirm = styledInput("Confirm Password", password = true)
        if (register) {
            val clp = LinearLayout.LayoutParams(dp(250f), ViewGroup.LayoutParams.WRAP_CONTENT)
            clp.topMargin = dp(12f)
            panel.addView(confirm, clp)
        }

        val status = TextView(this)
        status.setTextColor(cError)
        status.textSize = 12f
        status.gravity = Gravity.CENTER
        val slp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
        slp.topMargin = dp(10f)
        panel.addView(status, slp)

        var okRef: Button? = null
        val ok = styledButton(if (register) "CREATE ACCOUNT" else "SIGN IN", true) {
            val n = nick.text.toString().trim()
            val p = pass.text.toString()
            val c = confirm.text.toString()
            if (n.length < 3 || n.length > 24) { status.text = "Invalid nickname"; return@styledButton }
            if (p.length < 6 || p.length > 64) { status.text = "Password 6-64"; return@styledButton }
            if (register && p != c) { status.text = "Passwords do not match"; return@styledButton }
            status.text = ""
            okRef?.isEnabled = false
            val path = if (register) "/register" else "/login"
            thread {
                val res = httpPost(path, JSONObject().put("nickname", n).put("password", p))
                mainHandler.post {
                    if (res != null && res.optBoolean("ok")) {
                        val token = res.optString("token", "")
                        prefs.edit().putString("session_token", token).putString("session_nick", n).apply()
                        removeAuthOverlay()
                        nativeAuthResult(true)
                    } else {
                        status.text = res?.optString("error") ?: "Network error"
                        okRef?.isEnabled = true
                    }
                }
            }
        }
        okRef = ok
        val okp = LinearLayout.LayoutParams(dp(220f), ViewGroup.LayoutParams.WRAP_CONTENT)
        okp.topMargin = dp(18f)
        panel.addView(ok, okp)

        val back = styledButton("BACK", false) { showAuthMain() }
        val blp = LinearLayout.LayoutParams(dp(220f), ViewGroup.LayoutParams.WRAP_CONTENT)
        blp.topMargin = dp(10f)
        panel.addView(back, blp)

        rootLayout.addView(overlay, FrameLayout.LayoutParams(-1, -1))
        authOverlay = overlay
    }

    private fun removeAuthOverlay() {
        authOverlay?.let { rootLayout.removeView(it) }
        authOverlay = null
    }

    private fun httpPost(path: String, body: JSONObject): JSONObject? {
        return try {
            val url = URL(WORKER_URL + path)
            val conn = url.openConnection() as HttpURLConnection
            conn.requestMethod = "POST"
            conn.setRequestProperty("Content-Type", "application/json")
            conn.connectTimeout = 8000
            conn.readTimeout = 8000
            conn.doOutput = true
            OutputStreamWriter(conn.outputStream).use { it.write(body.toString()) }
            val code = conn.responseCode
            val stream = if (code in 200..299) conn.inputStream else conn.errorStream
            val txt = stream?.bufferedReader()?.use { it.readText() } ?: "{}"
            JSONObject(txt)
        } catch (_: Exception) {
            null
        }
    }

    private external fun nativeInit(activity: Any, cacheDir: String, version: String, density: Float)
    private external fun nativeSurface(surface: Surface?)
    private external fun nativeFrame(timeMs: Double)
    private external fun nativeTouch(action: Int, x: Float, y: Float)
    private external fun nativeResume()
    private external fun nativePause()
    private external fun nativeBack()
    private external fun nativeAgentDone()
    private external fun nativeAuthResult(ok: Boolean)
    private external fun nativeStartMusicFile()
}
