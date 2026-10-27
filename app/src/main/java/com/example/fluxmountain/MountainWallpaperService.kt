package com.example.fluxmountain

import android.app.KeyguardManager
import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.graphics.Canvas
import android.os.Build
import android.os.Handler
import android.os.Looper
import android.service.wallpaper.WallpaperService
import android.view.SurfaceHolder
import kotlin.math.exp
import kotlin.math.max
import kotlin.math.min

class MountainWallpaperService : WallpaperService() {

    companion object {
        private const val SWIPE_MAX_YAW = 22f     // Grad, volle Wischbreite = +/- 22°
        private const val UNLOCK_YAW = -7f        // Grad nach links beim Entsperren
        private const val MAX_YAW = 30f           // harte Obergrenze
        private const val DIST_LOCKED = 4.35f     // Sperrbildschirm: weiter weg
        private const val DIST_UNLOCKED = 4.0f    // entsperrt: minimal näher
        private const val UNLOCK_SECONDS = 1.2f
    }

    override fun onCreateEngine(): Engine = MountainEngine()

    private inner class MountainEngine : Engine() {

        private val handler = Handler(Looper.getMainLooper())
        private val renderer = MountainRenderer()
        private val keyguard by lazy {
            getSystemService(Context.KEYGUARD_SERVICE) as KeyguardManager
        }

        private var visible = false
        private var width = 0
        private var height = 0
        private var lastFrameNs = 0L

        private var xOffset = 0.5f
        private var yaw = 0f
        private var unlock = 1f
        private var unlockTarget = 1f
        private var pendingUnlockAnim = false
        private var receiverRegistered = false

        private val drawRunner = Runnable { drawFrame() }

        private val screenReceiver = object : BroadcastReceiver() {
            override fun onReceive(context: Context?, intent: Intent?) {
                when (intent?.action) {
                    Intent.ACTION_SCREEN_OFF -> lockedPose()
                    Intent.ACTION_USER_PRESENT -> {
                        if (visible) startUnlockAnim() else pendingUnlockAnim = true
                    }
                }
            }
        }

        private fun lockedPose() {
            unlock = 0f
            unlockTarget = 0f
            pendingUnlockAnim = true
        }

        private fun startUnlockAnim() {
            unlock = 0f
            unlockTarget = 1f
            pendingUnlockAnim = false
        }

        override fun onCreate(surfaceHolder: SurfaceHolder) {
            super.onCreate(surfaceHolder)
            if (isPreview) {
                unlock = 1f
                unlockTarget = 1f
            } else {
                val filter = IntentFilter().apply {
                    addAction(Intent.ACTION_SCREEN_OFF)
                    addAction(Intent.ACTION_USER_PRESENT)
                }
                if (Build.VERSION.SDK_INT >= 33) {
                    registerReceiver(screenReceiver, filter, Context.RECEIVER_NOT_EXPORTED)
                } else {
                    registerReceiver(screenReceiver, filter)
                }
                receiverRegistered = true
            }
        }

        override fun onDestroy() {
            handler.removeCallbacks(drawRunner)
            if (receiverRegistered) {
                try {
                    unregisterReceiver(screenReceiver)
                } catch (_: Exception) {
                }
                receiverRegistered = false
            }
            super.onDestroy()
        }

        override fun onSurfaceChanged(holder: SurfaceHolder, format: Int, w: Int, h: Int) {
            super.onSurfaceChanged(holder, format, w, h)
            width = w
            height = h
        }

        override fun onSurfaceDestroyed(holder: SurfaceHolder) {
            visible = false
            handler.removeCallbacks(drawRunner)
            super.onSurfaceDestroyed(holder)
        }

        override fun onVisibilityChanged(isVisible: Boolean) {
            visible = isVisible
            if (isVisible) {
                if (!isPreview) {
                    if (keyguard.isKeyguardLocked) {
                        lockedPose()
                    } else if (pendingUnlockAnim) {
                        startUnlockAnim()
                    } else {
                        unlock = 1f
                        unlockTarget = 1f
                    }
                }
                lastFrameNs = 0L
                handler.removeCallbacks(drawRunner)
                handler.post(drawRunner)
            } else {
                handler.removeCallbacks(drawRunner)
            }
        }

        override fun onOffsetsChanged(
            xOffset: Float, yOffset: Float,
            xOffsetStep: Float, yOffsetStep: Float,
            xPixelOffset: Int, yPixelOffset: Int
        ) {
            // Nur eine Seite (oder unbekannt): Berg bleibt mittig
            this.xOffset = if (xOffsetStep <= 0f || xOffsetStep > 0.99f) 0.5f else xOffset
        }

        private fun drawFrame() {
            if (!visible) return

            val now = System.nanoTime()
            val dt = if (lastFrameNs == 0L) 0.016f
            else ((now - lastFrameNs) / 1_000_000_000f).coerceIn(0.001f, 0.1f)
            lastFrameNs = now

            // Entsperr-Animation (0 = Sperrbildschirm, 1 = entsperrt)
            val step = dt / UNLOCK_SECONDS
            unlock = if (unlock < unlockTarget) min(unlockTarget, unlock + step)
            else max(unlockTarget, unlock - step)
            val e = unlock * unlock * (3f - 2f * unlock)

            // Wischen: Vorderseite des Bergs folgt der Wischrichtung
            val target = (-(xOffset - 0.5f) * 2f * SWIPE_MAX_YAW + UNLOCK_YAW * e)
                .coerceIn(-MAX_YAW, MAX_YAW)
            yaw += (target - yaw) * (1f - exp(-dt * 6f))
            val dist = DIST_LOCKED + (DIST_UNLOCKED - DIST_LOCKED) * e

            val holder = surfaceHolder
            var canvas: Canvas? = null
            try {
                canvas = try {
                    holder.lockHardwareCanvas()
                } catch (_: Exception) {
                    holder.lockCanvas()
                }
                if (canvas != null) {
                    renderer.draw(canvas, width, height, yaw, dist, dt)
                }
            } finally {
                if (canvas != null) {
                    try {
                        holder.unlockCanvasAndPost(canvas)
                    } catch (_: Exception) {
                    }
                }
            }

            handler.removeCallbacks(drawRunner)
            if (visible) handler.postDelayed(drawRunner, 10)
        }
    }
}