package com.example.fluxmountain

import android.graphics.Bitmap
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.LinearGradient
import android.graphics.Paint
import android.graphics.RadialGradient
import android.graphics.RectF
import android.graphics.Shader
import kotlin.math.abs
import kotlin.math.cos
import kotlin.math.floor
import kotlin.math.hypot
import kotlin.math.max
import kotlin.math.min
import kotlin.math.pow
import kotlin.math.sin
import kotlin.math.sqrt

class MountainRenderer {

    companion object {
        private const val N = 72              // Zellen pro Seite (je 2 Dreiecke)
        private const val HALF = 3.0f         // halbe Kantenlänge des Geländes
        private const val BUCKETS = 1024      // Tiefensortierung

        private const val CAM_Y = 1.6f        // Kamerahöhe
        private const val TARGET_Y = 0.8f     // Blickpunkt (Höhe)

        // Dunst-/Horizontfarbe (= untere Himmelsfarbe)
        private const val FOG_R = 203f
        private const val FOG_G = 230f
        private const val FOG_B = 249f

        // Sonne (Richtung zur Sonne, normalisiert): links oben vorne
        private const val LX = -0.532f
        private const val LY = 0.726f
        private const val LZ = 0.436f

        // Beleuchtung: Umgebungslicht (bläulich) + Sonnenlicht (warm)
        private const val AMB_R = 0.30f
        private const val AMB_G = 0.36f
        private const val AMB_B = 0.50f
        private const val SUN_R = 0.80f
        private const val SUN_G = 0.74f
        private const val SUN_B = 0.62f
    }

    private class Cloud(
        var x: Float,
        val y: Float,
        val z: Float,
        val size: Float,
        val speed: Float,
        val alpha: Int,
        val parallax: Float
    )

    private val vertCount = (N + 1) * (N + 1)
    private val cellCount = N * N

    // Modellraum
    private val mx = FloatArray(vertCount)
    private val my = FloatArray(vertCount)
    private val mz = FloatArray(vertCount)

    // pro Dreieck: Normale und Grundfarbe (0..255)
    private val triNx = FloatArray(cellCount * 2)
    private val triNy = FloatArray(cellCount * 2)
    private val triNz = FloatArray(cellCount * 2)
    private val triR = FloatArray(cellCount * 2)
    private val triG = FloatArray(cellCount * 2)
    private val triB = FloatArray(cellCount * 2)

    // Bildschirmraum
    private val sx = FloatArray(vertCount)
    private val sy = FloatArray(vertCount)
    private val sd = FloatArray(vertCount)

    private val cellDepth = FloatArray(cellCount)
    private val cellBucket = IntArray(cellCount)
    private val bucketCount = IntArray(BUCKETS + 1)
    private val order = IntArray(cellCount)
    private val verts = FloatArray(cellCount * 12)
    private val colors = IntArray(cellCount * 6)

    private val terrainPaint = Paint()
    private val skyPaint = Paint()
    private val cloudPaint = Paint(Paint.FILTER_BITMAP_FLAG)
    private val cloudRect = RectF()
    private val cloudBitmap: Bitmap = makeCloudBitmap()

    private val backClouds = listOf(
        Cloud(-2.8f, 2.9f, -2.5f, 2.4f, 0.06f, 235, 0.6f),
        Cloud(1.6f, 3.5f, -3.2f, 3.0f, 0.04f, 225, 0.5f),
        Cloud(-0.6f, 1.9f, -1.8f, 1.8f, 0.05f, 240, 0.6f),
        Cloud(3.0f, 2.2f, -2.0f, 2.1f, 0.07f, 235, 0.6f),
        Cloud(-4.2f, 1.3f, -2.6f, 2.2f, 0.05f, 220, 0.6f),
        Cloud(0.9f, 2.8f, -1.2f, 1.4f, 0.035f, 240, 0.6f)
    )
    private val frontClouds = listOf(
        Cloud(-2.0f, 0.9f, 1.6f, 1.1f, 0.09f, 190, 1.3f),
        Cloud(2.2f, 1.4f, 1.2f, 0.9f, 0.07f, 175, 1.3f),
        Cloud(0.3f, 0.5f, 2.0f, 1.0f, 0.10f, 170, 1.3f),
        Cloud(-1.1f, 1.7f, 0.9f, 0.8f, 0.06f, 150, 1.3f)
    )

    private var lastW = 0
    private var lastH = 0

    init {
        terrainPaint.isAntiAlias = false
        val step = 2f * HALF / N
        for (j in 0..N) {
            for (i in 0..N) {
                val k = j * (N + 1) + i
                val x = -HALF + i * step
                val z = -HALF + j * step
                mx[k] = x
                mz[k] = z
                my[k] = height(x, z)
            }
        }
        for (j in 0 until N) {
            for (i in 0 until N) {
                val c = j * N + i
                val k00 = j * (N + 1) + i
                val k10 = k00 + 1
                val k01 = k00 + N + 1
                val k11 = k01 + 1
                setupTriangle(c * 2, k00, k01, k10)
                setupTriangle(c * 2 + 1, k10, k01, k11)
            }
        }
    }

    // ---------- Gelände ----------

    private fun hash(ix: Int, iz: Int): Float {
        var h = ix * 374761393 + iz * 668265263 + 1274126177
        h = (h xor (h ushr 13)) * 1274126177
        h = h xor (h ushr 16)
        return (h and 0xFFFF) / 65535f
    }

    private fun smooth(t: Float) = t * t * (3f - 2f * t)

    private fun lerp(a: Float, b: Float, t: Float) = a + (b - a) * t

    private fun vnoise(x: Float, z: Float): Float {
        val ix = floor(x).toInt()
        val iz = floor(z).toInt()
        val fx = smooth(x - ix)
        val fz = smooth(z - iz)
        val a = hash(ix, iz)
        val b = hash(ix + 1, iz)
        val c = hash(ix, iz + 1)
        val d = hash(ix + 1, iz + 1)
        return lerp(lerp(a, b, fx), lerp(c, d, fx), fz)
    }

    private fun fbm(x: Float, z: Float, octaves: Int): Float {
        var sum = 0f
        var amp = 0.5f
        var freq = 1f
        var norm = 0f
        for (o in 0 until octaves) {
            sum += amp * vnoise(x * freq + o * 17.3f, z * freq - o * 9.1f)
            norm += amp
            amp *= 0.5f
            freq *= 2f
        }
        return sum / norm
    }

    private fun ridged(x: Float, z: Float, octaves: Int): Float {
        var sum = 0f
        var amp = 0.5f
        var freq = 1f
        var norm = 0f
        for (o in 0 until octaves) {
            val n = vnoise(x * freq + o * 13.7f, z * freq - o * 5.3f)
            val r = 1f - abs(2f * n - 1f)
            sum += amp * r * r
            norm += amp
            amp *= 0.5f
            freq *= 2f
        }
        return sum / norm
    }

    private fun height(x: Float, z: Float): Float {
        val r1 = hypot(x, z)
        val c1 = max(0f, 1f - r1 / 1.9f).pow(1.25f)
        val r2 = hypot(x + 0.95f, z - 0.25f)
        val c2 = max(0f, 1f - r2 / 1.15f).pow(1.3f) * 0.55f
        val base = max(c1, c2)
        val rid = ridged(x * 1.6f + 3.1f, z * 1.6f + 7.7f, 5)
        val det = fbm(x * 3.2f, z * 3.2f, 4)
        var h = 2.1f * base * (0.72f + 0.55f * rid)
        h += 0.10f * (det - 0.5f) * base
        h += 0.08f * fbm(x * 0.9f, z * 0.9f, 3)
        return max(h, 0f)
    }

    private fun smoothstep(e0: Float, e1: Float, x: Float): Float {
        val t = ((x - e0) / (e1 - e0)).coerceIn(0f, 1f)
        return t * t * (3f - 2f * t)
    }

    private fun setupTriangle(t: Int, a: Int, b: Int, c: Int) {
        val e1x = mx[b] - mx[a]
        val e1y = my[b] - my[a]
        val e1z = mz[b] - mz[a]
        val e2x = mx[c] - mx[a]
        val e2y = my[c] - my[a]
        val e2z = mz[c] - mz[a]
        var nx = e1y * e2z - e1z * e2y
        var ny = e1z * e2x - e1x * e2z
        var nz = e1x * e2y - e1y * e2x
        if (ny < 0f) {
            nx = -nx; ny = -ny; nz = -nz
        }
        val len = max(sqrt(nx * nx + ny * ny + nz * nz), 1e-6f)
        nx /= len; ny /= len; nz /= len
        triNx[t] = nx
        triNy[t] = ny
        triNz[t] = nz

        val cxm = (mx[a] + mx[b] + mx[c]) / 3f
        val cym = (my[a] + my[b] + my[c]) / 3f
        val czm = (mz[a] + mz[b] + mz[c]) / 3f
        val noise = fbm(cxm * 5f, czm * 5f, 2)
        val steep = 1f - ny

        // Wiese -> Fels
        var rockAmt = smoothstep(0.25f, 0.55f, cym + (noise - 0.5f) * 0.25f)
        rockAmt = max(rockAmt, smoothstep(0.18f, 0.40f, steep))
        val grassR = lerp(78f, 58f, noise)
        val grassG = lerp(108f, 86f, noise)
        val grassB = lerp(58f, 48f, noise)
        val rockMix = smoothstep(0.1f, 0.5f, steep) * 0.6f + (1f - noise) * 0.3f
        val rockR = lerp(128f, 98f, rockMix)
        val rockG = lerp(116f, 90f, rockMix)
        val rockB = lerp(104f, 86f, rockMix)

        // Schnee: nur oberhalb der Schneegrenze und nicht an steilen Wänden
        val snowLine = 1.15f + 0.3f * (noise - 0.5f)
        val snowAmt = smoothstep(snowLine - 0.12f, snowLine + 0.12f, cym) *
                (1f - smoothstep(0.35f, 0.60f, steep))

        var r = lerp(lerp(grassR, rockR, rockAmt), 246f, snowAmt)
        var g = lerp(lerp(grassG, rockG, rockAmt), 249f, snowAmt)
        var bl = lerp(lerp(grassB, rockB, rockAmt), 253f, snowAmt)

        // leichte Helligkeitsstreuung pro Dreieck -> Low-Poly-Look
        val jitter = 0.94f + 0.12f * hash(t, 77)
        r *= jitter; g *= jitter; bl *= jitter
        triR[t] = r
        triG[t] = g
        triB[t] = bl
    }

    // ---------- Wolken ----------

    private fun makeCloudBitmap(): Bitmap {
        val w = 384
        val h = 192
        val bm = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888)
        val c = Canvas(bm)
        val p = Paint(Paint.ANTI_ALIAS_FLAG)
        val blobs = arrayOf(
            floatArrayOf(0.18f, 0.62f, 0.30f),
            floatArrayOf(0.34f, 0.50f, 0.38f),
            floatArrayOf(0.50f, 0.42f, 0.44f),
            floatArrayOf(0.66f, 0.50f, 0.38f),
            floatArrayOf(0.82f, 0.62f, 0.30f),
            floatArrayOf(0.42f, 0.68f, 0.34f),
            floatArrayOf(0.60f, 0.70f, 0.34f)
        )
        val stops = floatArrayOf(0f, 0.55f, 1f)
        // Unterseite: leicht bläulich-grau
        val shade = intArrayOf(
            Color.argb(176, 180, 198, 220),
            Color.argb(112, 180, 198, 220),
            Color.argb(0, 180, 198, 220)
        )
        for (b in blobs) {
            val bx = b[0] * w
            val by = (b[1] + 0.08f) * h
            val r = b[2] * h
            p.shader = RadialGradient(bx, by, r, shade, stops, Shader.TileMode.CLAMP)
            c.drawCircle(bx, by, r, p)
        }
        // Oberseite: weiß
        val white = intArrayOf(
            Color.argb(242, 255, 255, 255),
            Color.argb(184, 255, 255, 255),
            Color.argb(0, 255, 255, 255)
        )
        for (b in blobs) {
            val bx = b[0] * w
            val by = b[1] * h
            val r = b[2] * h
            p.shader = RadialGradient(bx, by, r, white, stops, Shader.TileMode.CLAMP)
            c.drawCircle(bx, by, r, p)
        }
        return bm
    }

    private fun updateClouds(dt: Float) {
        for (c in backClouds) {
            c.x += c.speed * dt
            if (c.x > 5.5f) c.x = -5.5f
        }
        for (c in frontClouds) {
            c.x += c.speed * dt
            if (c.x > 5.5f) c.x = -5.5f
        }
    }

    private fun drawClouds(
        canvas: Canvas, list: List<Cloud>, f: Float, cx: Float, cy: Float,
        camDist: Float, fy: Float, fz: Float, uy: Float, uz: Float, shift: Float
    ) {
        for (c in list) {
            val dy = c.y - CAM_Y
            val dz = c.z - camDist
            val depth = dy * fy + dz * fz
            if (depth < 0.5f) continue
            val v = dy * uy + dz * uz
            val wx = c.x + shift * c.parallax
            val px = cx + f * wx / depth
            val py = cy - f * v / depth
            val cw = c.size * f / depth
            val ch = cw * 0.5f
            if (px + cw * 0.5f < 0f || px - cw * 0.5f > lastW) continue
            if (py + ch * 0.5f < 0f || py - ch * 0.5f > lastH) continue
            cloudPaint.alpha = c.alpha
            cloudRect.set(px - cw * 0.5f, py - ch * 0.5f, px + cw * 0.5f, py + ch * 0.5f)
            canvas.drawBitmap(cloudBitmap, null, cloudRect, cloudPaint)
        }
    }

    // ---------- Zeichnen ----------

    fun draw(canvas: Canvas, w: Int, h: Int, yawDeg: Float, camDist: Float, dt: Float) {
        if (w <= 0 || h <= 0) return
        if (w != lastW || h != lastH) {
            lastW = w
            lastH = h
            skyPaint.shader = LinearGradient(
                0f, 0f, 0f, h.toFloat(),
                intArrayOf(
                    Color.rgb(36, 110, 200),
                    Color.rgb(110, 170, 235),
                    Color.rgb(203, 230, 249),
                    Color.rgb(203, 230, 249)
                ),
                floatArrayOf(0f, 0.30f, 0.45f, 1f),
                Shader.TileMode.CLAMP
            )
        }

        val f = min(w.toFloat(), h * 0.45f) * 1.7f
        val cx = w * 0.5f
        val cy = h * 0.52f

        // Kamerabasis: Blick nach vorne-unten, "oben" senkrecht dazu
        val dyT = TARGET_Y - CAM_Y
        val len = sqrt(dyT * dyT + camDist * camDist)
        val fy = dyT / len
        val fz = -camDist / len
        val uy = -fz
        val uz = fy

        canvas.drawRect(0f, 0f, w.toFloat(), h.toFloat(), skyPaint)

        updateClouds(dt)
        val shift = -yawDeg * 0.03f
        drawClouds(canvas, backClouds, f, cx, cy, camDist, fy, fz, uy, uz, shift)
        drawTerrain(canvas, f, cx, cy, camDist, fy, fz, uy, uz, yawDeg)
        drawClouds(canvas, frontClouds, f, cx, cy, camDist, fy, fz, uy, uz, shift)
    }

    private fun drawTerrain(
        canvas: Canvas, f: Float, cx: Float, cy: Float, camDist: Float,
        fy: Float, fz: Float, uy: Float, uz: Float, yawDeg: Float
    ) {
        val rad = Math.toRadians(yawDeg.toDouble())
        val cs = cos(rad).toFloat()
        val sn = sin(rad).toFloat()

        // 1) Alle Eckpunkte drehen und projizieren
        for (k in 0 until vertCount) {
            val x = mx[k]
            val z = mz[k]
            val wx = x * cs + z * sn
            val wz = -x * sn + z * cs
            val dy = my[k] - CAM_Y
            val dz = wz - camDist
            val depth = dy * fy + dz * fz
            val v = dy * uy + dz * uz
            val inv = f / max(depth, 0.05f)
            sx[k] = cx + wx * inv
            sy[k] = cy - v * inv
            sd[k] = depth
        }

        // 2) Zellen nach Tiefe sortieren (Maler-Algorithmus, Bucket-Sort, fern zuerst)
        var dmin = Float.MAX_VALUE
        var dmax = -Float.MAX_VALUE
        for (c in 0 until cellCount) {
            val j = c / N
            val i = c - j * N
            val k00 = j * (N + 1) + i
            val d = (sd[k00] + sd[k00 + N + 2]) * 0.5f
            cellDepth[c] = d
            if (d < dmin) dmin = d
            if (d > dmax) dmax = d
        }
        val scale = (BUCKETS - 1) / max(dmax - dmin, 0.001f)
        java.util.Arrays.fill(bucketCount, 0)
        for (c in 0 until cellCount) {
            val b = (BUCKETS - 1) - ((cellDepth[c] - dmin) * scale).toInt()
            cellBucket[c] = b
            bucketCount[b + 1]++
        }
        for (b in 0 until BUCKETS) bucketCount[b + 1] += bucketCount[b]
        for (c in 0 until cellCount) {
            order[bucketCount[cellBucket[c]]++] = c
        }

        // 3) Dreiecke einfärben und in die Vertex-Arrays schreiben
        var cells = 0
        for (n in 0 until cellCount) {
            val c = order[n]
            val j = c / N
            val i = c - j * N
            val k00 = j * (N + 1) + i
            val k10 = k00 + 1
            val k01 = k00 + N + 1
            val k11 = k01 + 1
            if (sd[k00] < 0.6f || sd[k10] < 0.6f || sd[k01] < 0.6f || sd[k11] < 0.6f) continue
            val fog = smoothstep(camDist + 0.9f, camDist + 2.7f, cellDepth[c])
            emit(cells * 2, k00, k01, k10, c * 2, fog, cs, sn)
            emit(cells * 2 + 1, k10, k01, k11, c * 2 + 1, fog, cs, sn)
            cells++
        }
        if (cells > 0) {
            canvas.drawVertices(
                Canvas.VertexMode.TRIANGLES, cells * 12, verts, 0,
                null, 0, colors, 0, null, 0, 0, terrainPaint
            )
        }
    }

    private fun emit(slot: Int, a: Int, b: Int, c: Int, t: Int, fog: Float, cs: Float, sn: Float) {
        // Normale in Weltraum drehen, damit das Licht fest im Raum bleibt
        val nx = triNx[t] * cs + triNz[t] * sn
        val nz = -triNx[t] * sn + triNz[t] * cs
        val d = max(0f, nx * LX + triNy[t] * LY + nz * LZ)

        var r = triR[t] * (AMB_R + SUN_R * d)
        var g = triG[t] * (AMB_G + SUN_G * d)
        var bl = triB[t] * (AMB_B + SUN_B * d)

        r += (FOG_R - r) * fog
        g += (FOG_G - g) * fog
        bl += (FOG_B - bl) * fog

        val col = Color.rgb(min(255, r.toInt()), min(255, g.toInt()), min(255, bl.toInt()))

        val vi = slot * 6
        verts[vi] = sx[a]
        verts[vi + 1] = sy[a]
        verts[vi + 2] = sx[b]
        verts[vi + 3] = sy[b]
        verts[vi + 4] = sx[c]
        verts[vi + 5] = sy[c]

        val ci = slot * 3
        colors[ci] = col
        colors[ci + 1] = col
        colors[ci + 2] = col
    }
}