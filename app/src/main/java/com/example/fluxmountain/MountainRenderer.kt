package com.example.fluxmountain

import android.graphics.Bitmap
import android.graphics.BitmapShader
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.LinearGradient
import android.graphics.Paint
import android.graphics.Path
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

class MountainRenderer(source: Bitmap?) {

    companion object {
        private const val N = 96              // Zellen pro Seite (je 2 Dreiecke); bei Ruckeln auf 72 senken
        private const val HALF = 3.0f         // halbe Kantenlänge des Geländes
        private const val BUCKETS = 1024      // Tiefensortierung

        private const val CAM_Y = 1.6f        // Kamerahöhe
        private const val TARGET_Y = 0.8f     // Blickpunkt (Höhe)

        // Gipfel (Hauptberg)
        private const val PEAK_HEIGHT = 2.25f // Höhe des Gipfels
        private const val PEAK_RADIUS = 2.0f  // Radius des Fußes
        private const val PEAK_ROT = 0.45f    // Drehung der vier Kanten (Bogenmaß)

        // Dunst-/Horizontfarbe (= Farbe der Ferne)
        private const val FOG_R = 196f
        private const val FOG_G = 218f
        private const val FOG_B = 244f

        // Sonne (Richtung zur Sonne, normalisiert): links oben vorne
        private const val LX = -0.650f
        private const val LY = 0.551f
        private const val LZ = 0.521f

        // Beleuchtung: Umgebungslicht (kräftig blau, für blaue Schatten) + Sonnenlicht (warm)
        private const val AMB_R = 0.34f
        private const val AMB_G = 0.42f
        private const val AMB_B = 0.66f
        private const val SUN_R = 0.80f
        private const val SUN_G = 0.74f
        private const val SUN_B = 0.60f

        // Himmel und Ferne (Anteile der Bildhöhe)
        private const val HORIZON = 0.43f     // Höhe der fernen Bergkette
        private const val SCREEN_CENTER = 0.60f // senkrechte Bildmitte der Kamera (größer = Berg weiter unten)

        // Wolken (im Video gibt es keine): false schaltet sie ab
        private const val CLOUDS_ENABLED = true

        // Textur
        private const val TEX_WORLD = 0.9f    // Weltgröße einer Kachel (kleiner = feinere Struktur)
        private const val TEX_SKEW = 0.5f     // Schrägstellung mit der Höhe
        private const val TEX_STRENGTH = 0.7f // Stärke der Textur (0 = keine, 1 = voll)
        private const val TEX_MIN = 0.45f     // dunkelster Wert der Textur
        private const val TEX_MAX_SIZE = 512  // größere PNGs werden verkleinert
        private const val FLAT_FOG = 0.45f    // ab diesem Dunstanteil ohne Textur
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
    private val vedge = FloatArray(vertCount) // 0 = Mitte, 1 = Geländerand (geht in Dunst über)

    // pro Eckpunkt: Normale, Grundfarbe (0..255) und Texturkoordinaten
    private val vnx = FloatArray(vertCount)
    private val vny = FloatArray(vertCount)
    private val vnz = FloatArray(vertCount)
    private val vr = FloatArray(vertCount)
    private val vg = FloatArray(vertCount)
    private val vb = FloatArray(vertCount)
    private val vu = FloatArray(vertCount)
    private val vv = FloatArray(vertCount)

    // pro Eckpunkt und Bild: fertige Farben (flach bzw. für die Textur)
    private val vcFlat = IntArray(vertCount)
    private val vcTex = IntArray(vertCount)

    // Bildschirmraum
    private val sx = FloatArray(vertCount)
    private val sy = FloatArray(vertCount)
    private val sd = FloatArray(vertCount)

    private val cellDepth = FloatArray(cellCount)
    private val cellBucket = IntArray(cellCount)
    private val bucketCount = IntArray(BUCKETS + 1)
    private val order = IntArray(cellCount)

    // Ausgabe: ferne, flach eingefärbte Zellen
    private val verts = FloatArray(cellCount * 12)
    private val colors = IntArray(cellCount * 6)

    // Ausgabe: nahe, texturierte Zellen
    private val tVerts = FloatArray(cellCount * 12)
    private val tColors = IntArray(cellCount * 6)
    private val tUV = FloatArray(cellCount * 12)

    private val terrainPaint = Paint()
    private val texPaint = Paint()
    private val skyPaint = Paint()
    private val ridgePaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val ridgePath = Path()
    private val cloudPaint = Paint(Paint.FILTER_BITMAP_FLAG)
    private val cloudRect = RectF()
    private val cloudBitmap: Bitmap = makeCloudBitmap()

    // Mittelwerte der aufbereiteten Textur (müssen vor "tex" deklariert sein)
    private var meanR = 1f
    private var meanG = 1f
    private var meanB = 1f

    private val tex: Bitmap? = if (source != null) prepareTexture(source) else null
    private val texW = (tex?.width ?: 1).toFloat()
    private val texH = (tex?.height ?: 1).toFloat()
    private val hasTexture = tex != null

    // gleicht die Abdunklung durch die Textur im Licht wieder aus
    private val lightGain = if (hasTexture) 3f / (meanR + meanG + meanB) else 1f

    private val backClouds = listOf(
        Cloud(-2.8f, 2.9f, -2.5f, 2.2f, 0.05f, 150, 0.6f),
        Cloud(1.8f, 3.5f, -3.2f, 2.8f, 0.035f, 140, 0.5f),
        Cloud(-0.4f, 2.1f, -1.8f, 1.6f, 0.04f, 130, 0.6f)
    )
    private val frontClouds = listOf(
        Cloud(-2.2f, 1.7f, 1.0f, 1.0f, 0.08f, 120, 1.3f),
        Cloud(2.0f, 2.3f, 0.6f, 0.9f, 0.06f, 100, 1.3f)
    )

    private var lastW = 0
    private var lastH = 0

    init {
        terrainPaint.isAntiAlias = false
        if (tex != null) {
            texPaint.isAntiAlias = false
            texPaint.isFilterBitmap = true
            texPaint.shader = BitmapShader(tex, Shader.TileMode.REPEAT, Shader.TileMode.REPEAT)
        }

        // Höhenfeld
        val step = 2f * HALF / N
        for (j in 0..N) {
            for (i in 0..N) {
                val k = j * (N + 1) + i
                val x = -HALF + i * step
                val z = -HALF + j * step
                mx[k] = x
                mz[k] = z
                my[k] = height(x, z)
                vedge[k] = smoothstep(2.2f, 2.95f, max(abs(x), abs(z)))
            }
        }

        // Normale und Material pro Eckpunkt (Normale aus dem Höhenverlauf der Nachbarn)
        for (j in 0..N) {
            for (i in 0..N) {
                val iL = max(i - 1, 0)
                val iR = min(i + 1, N)
                val jD = max(j - 1, 0)
                val jU = min(j + 1, N)
                val dhx = (my[j * (N + 1) + iR] - my[j * (N + 1) + iL]) / ((iR - iL) * step)
                val dhz = (my[jU * (N + 1) + i] - my[jD * (N + 1) + i]) / ((jU - jD) * step)
                setupVertex(j * (N + 1) + i, -dhx, 1f, -dhz)
            }
        }
    }

    // ---------- Textur ----------

    /**
     * Macht aus dem PNG eine reine Struktur-Textur: Werte nur zwischen TEX_MIN und 1,
     * relativ zum Mittelwert des Bildes. Merkt sich den neuen Mittelwert je Farbkanal.
     */
    private fun prepareTexture(src: Bitmap): Bitmap {
        var bmp = src
        val maxSide = max(src.width, src.height)
        if (maxSide > TEX_MAX_SIZE) {
            val s = TEX_MAX_SIZE.toFloat() / maxSide
            bmp = Bitmap.createScaledBitmap(
                src,
                max(1, (src.width * s).toInt()),
                max(1, (src.height * s).toInt()),
                true
            )
        }
        val w = bmp.width
        val h = bmp.height
        val px = IntArray(w * h)
        bmp.getPixels(px, 0, w, 0, 0, w, h)
        val n = px.size

        var sr = 0.0
        var sg = 0.0
        var sb = 0.0
        for (p in px) {
            sr += Color.red(p)
            sg += Color.green(p)
            sb += Color.blue(p)
        }
        val mr = max(1.0, sr / n).toFloat()
        val mg = max(1.0, sg / n).toFloat()
        val mb = max(1.0, sb / n).toFloat()

        var tr = 0.0
        var tg = 0.0
        var tb = 0.0
        val out = IntArray(n)
        for (i in 0 until n) {
            val p = px[i]
            val r = (1f + (Color.red(p) / mr - 1f) * TEX_STRENGTH).coerceIn(TEX_MIN, 1f)
            val g = (1f + (Color.green(p) / mg - 1f) * TEX_STRENGTH).coerceIn(TEX_MIN, 1f)
            val b = (1f + (Color.blue(p) / mb - 1f) * TEX_STRENGTH).coerceIn(TEX_MIN, 1f)
            tr += r
            tg += g
            tb += b
            out[i] = Color.rgb((r * 255f).toInt(), (g * 255f).toInt(), (b * 255f).toInt())
        }
        meanR = (tr / n).toFloat()
        meanG = (tg / n).toFloat()
        meanB = (tb / n).toFloat()

        val res = Bitmap.createBitmap(out, w, h, Bitmap.Config.ARGB_8888)
        res.setHasMipMap(true)
        return res
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

    private fun smoothstep(e0: Float, e1: Float, x: Float): Float {
        val t = ((x - e0) / (e1 - e0)).coerceIn(0f, 1f)
        return t * t * (3f - 2f * t)
    }

    /**
     * Ein spitzer Horn-Gipfel mit vier Graten: Der Abstand wird mit einem Exponenten kleiner 2
     * gemessen, dadurch entstehen Kanten entlang der Achsen. Die Flanken sind oben steil
     * und laufen unten flach aus. Ridged-Noise gibt den Wänden Rippen.
     */
    private fun horn(x: Float, z: Float, cx: Float, cz: Float, rot: Float, hgt: Float, rad: Float): Float {
        val cr = cos(rot)
        val sr = sin(rot)
        val dx = x - cx
        val dz = z - cz
        val u = dx * cr - dz * sr
        val w = dx * sr + dz * cr
        val d = (abs(u).pow(1.15f) + abs(w).pow(1.15f)).pow(1f / 1.15f)
        val t = max(0f, 1f - d / rad)
        if (t <= 0f) return 0f
        val ribs = ridged(u * 2.3f + 5f, w * 2.3f + 9f, 5)
        return hgt * t.pow(1.5f) * (0.78f + 0.34f * ribs)
    }

    private fun height(x: Float, z: Float): Float {
        val hr = hypot(x, z)
        val edge = max(abs(x), abs(z))
        val mask = 1f - smoothstep(2.3f, 3.0f, edge)

        val main = horn(x, z, 0f, 0f, PEAK_ROT, PEAK_HEIGHT, PEAK_RADIUS)
        val second = horn(x, z, 2.0f, -1.3f, 0.9f, 1.35f, 1.25f)
        val base = max(main, second)

        // Umgebende Felshügel (außerhalb des Gipfelfußes), bilden auch die dunkle Wand vorne
        val hills = 0.75f * ridged(x * 0.85f + 20f, z * 0.85f + 4f, 4) * smoothstep(1.2f, 2.3f, hr)

        // feine Rauheit im Fels
        val detail = 0.07f * (fbm(x * 5f, z * 5f, 3) - 0.5f) * smoothstep(0.1f, 0.6f, base)

        return max(base + hills + detail, 0f) * mask
    }

    /** Normale, Material (Fels/Schnee/Gletscher) und Texturkoordinate eines Eckpunkts. */
    private fun setupVertex(k: Int, nxIn: Float, nyIn: Float, nzIn: Float) {
        val len = max(sqrt(nxIn * nxIn + nyIn * nyIn + nzIn * nzIn), 1e-6f)
        val nx = nxIn / len
        val ny = nyIn / len
        val nz = nzIn / len
        vnx[k] = nx
        vny[k] = ny
        vnz[k] = nz

        val x = mx[k]
        val y = my[k]
        val z = mz[k]

        // Durchgehende Textur-Abbildung: von oben, mit der Höhe leicht verschoben
        vu[k] = (x + TEX_SKEW * y) / TEX_WORLD * texW
        vv[k] = (z + TEX_SKEW * y) / TEX_WORLD * texH

        val noise = fbm(x * 4f, z * 4f, 2)
        val steep = 1f - ny

        // Felsfarbe mit senkrechten Streifen (wie die Felsrippen im Video)
        val streak = fbm(x * 7f + z * 5f, y * 1.8f, 3)
        val rt = smoothstep(0.25f, 0.75f, streak)
        val low = 0.75f + 0.25f * smoothstep(0f, 0.7f, y)
        val rockR = lerp(96f, 182f, rt) * low
        val rockG = lerp(100f, 184f, rt) * low
        val rockB = lerp(114f, 182f, rt) * low

        // Schnee/Gletscher: auf flachen und mäßig geneigten Flächen, nicht auf den steilen Wänden
        val snowAmt = 1f - smoothstep(0.12f, 0.30f, steep + (noise - 0.5f) * 0.22f)

        vr[k] = lerp(rockR, 244f, snowAmt)
        vg[k] = lerp(rockG, 247f, snowAmt)
        vb[k] = lerp(rockB, 252f, snowAmt)
    }

    // ---------- Himmel und ferne Berge ----------

    private fun drawRidge(
        canvas: Canvas, w: Int, h: Int, baseY: Float, amp: Float, freq: Float, seed: Float,
        shift: Float, r: Int, g: Int, b: Int
    ) {
        ridgePath.rewind()
        ridgePath.moveTo(0f, h.toFloat())
        val steps = 90
        for (i in 0..steps) {
            val px = w * i / steps.toFloat()
            val n = ridged(px / w * freq + shift + seed, seed * 1.7f, 4)
            ridgePath.lineTo(px, baseY - amp * n * 2.2f)
        }
        ridgePath.lineTo(w.toFloat(), h.toFloat())
        ridgePath.close()
        ridgePaint.color = Color.rgb(r, g, b)
        canvas.drawPath(ridgePath, ridgePaint)
    }

    /** Zweiter, ferner Schneegipfel: links hell (Sonne), rechts im blauen Schatten. */
    private fun drawFarPeak(canvas: Canvas, px: Float, top: Float, base: Float, wd: Float) {
        ridgePath.rewind()
        ridgePath.moveTo(px - wd, base)
        ridgePath.lineTo(px, top)
        ridgePath.lineTo(px + wd * 0.12f, base)
        ridgePath.close()
        ridgePaint.color = Color.rgb(236, 241, 250)
        canvas.drawPath(ridgePath, ridgePaint)

        ridgePath.rewind()
        ridgePath.moveTo(px, top)
        ridgePath.lineTo(px + wd * 1.25f, base)
        ridgePath.lineTo(px + wd * 0.12f, base)
        ridgePath.close()
        ridgePaint.color = Color.rgb(150, 168, 206)
        canvas.drawPath(ridgePath, ridgePaint)
    }

    private fun drawBackdrop(canvas: Canvas, w: Int, h: Int, yawDeg: Float) {
        val hf = h.toFloat()
        val wf = w.toFloat()
        val shift = -yawDeg * 0.012f

        // Ferne rosa-violette Kette
        drawRidge(canvas, w, h, hf * (HORIZON - 0.035f), hf * 0.045f, 3.0f, 3.1f, shift * 0.4f, 206, 190, 216)
        // Mittlere bläuliche Kette
        drawRidge(canvas, w, h, hf * (HORIZON + 0.01f), hf * 0.055f, 2.4f, 7.7f, shift * 0.7f, 188, 200, 228)
        // Fernes Schneehorn rechts
        drawFarPeak(canvas, wf * 0.80f - yawDeg * wf * 0.004f, hf * (HORIZON - 0.10f), hf * (HORIZON + 0.09f), wf * 0.14f)
        // Nahe Dunstschicht (Farbe = Dunst, damit das Gelände nahtlos hineinläuft)
        drawRidge(canvas, w, h, hf * (HORIZON + 0.075f), hf * 0.03f, 2.0f, 12.3f, shift, FOG_R.toInt(), FOG_G.toInt(), FOG_B.toInt())
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
                    Color.rgb(66, 116, 206),
                    Color.rgb(98, 148, 224),
                    Color.rgb(176, 206, 242),
                    Color.rgb(FOG_R.toInt(), FOG_G.toInt(), FOG_B.toInt())
                ),
                floatArrayOf(0f, 0.22f, HORIZON, HORIZON + 0.07f),
                Shader.TileMode.CLAMP
            )
        }

        val f = min(w.toFloat(), h * 0.45f) * 1.7f
        val cx = w * 0.5f
        val cy = h * SCREEN_CENTER

        // Kamerabasis: Blick nach vorne-unten, "oben" senkrecht dazu
        val dyT = TARGET_Y - CAM_Y
        val len = sqrt(dyT * dyT + camDist * camDist)
        val fy = dyT / len
        val fz = -camDist / len
        val uy = -fz
        val uz = fy

        canvas.drawRect(0f, 0f, w.toFloat(), h.toFloat(), skyPaint)
        drawBackdrop(canvas, w, h, yawDeg)

        val shift = -yawDeg * 0.03f
        if (CLOUDS_ENABLED) {
            updateClouds(dt)
            drawClouds(canvas, backClouds, f, cx, cy, camDist, fy, fz, uy, uz, shift)
        }
        drawTerrain(canvas, f, cx, cy, camDist, fy, fz, uy, uz, yawDeg)
        if (CLOUDS_ENABLED) {
            drawClouds(canvas, frontClouds, f, cx, cy, camDist, fy, fz, uy, uz, shift)
        }
    }

    private fun depthFog(depth: Float, camDist: Float): Float =
        smoothstep(camDist + 1.4f, camDist + 3.6f, depth)

    private fun drawTerrain(
        canvas: Canvas, f: Float, cx: Float, cy: Float, camDist: Float,
        fy: Float, fz: Float, uy: Float, uz: Float, yawDeg: Float
    ) {
        val rad = Math.toRadians(yawDeg.toDouble())
        val cs = cos(rad).toFloat()
        val sn = sin(rad).toFloat()

        // 1) Alle Eckpunkte drehen, projizieren und beleuchten
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

            val fog = max(depthFog(depth, camDist), vedge[k])
            vertexColors(k, fog, cs, sn)
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

        // 3) Zellen in die Arrays schreiben: ferne flach (zuerst), nahe mit Textur (danach)
        var flatCells = 0
        var texCells = 0
        for (n in 0 until cellCount) {
            val c = order[n]
            val j = c / N
            val i = c - j * N
            val k00 = j * (N + 1) + i
            val k10 = k00 + 1
            val k01 = k00 + N + 1
            val k11 = k01 + 1
            if (sd[k00] < 0.6f || sd[k10] < 0.6f || sd[k01] < 0.6f || sd[k11] < 0.6f) continue
            val fog = max(depthFog(cellDepth[c], camDist), max(vedge[k00], vedge[k11]))
            if (hasTexture && fog < FLAT_FOG) {
                emitTextured(texCells * 2, k00, k01, k10)
                emitTextured(texCells * 2 + 1, k10, k01, k11)
                texCells++
            } else {
                emitFlat(flatCells * 2, k00, k01, k10)
                emitFlat(flatCells * 2 + 1, k10, k01, k11)
                flatCells++
            }
        }

        if (flatCells > 0) {
            canvas.drawVertices(
                Canvas.VertexMode.TRIANGLES, flatCells * 12, verts, 0,
                null, 0, colors, 0, null, 0, 0, terrainPaint
            )
        }
        if (texCells > 0) {
            canvas.drawVertices(
                Canvas.VertexMode.TRIANGLES, texCells * 12, tVerts, 0,
                tUV, 0, tColors, 0, null, 0, 0, texPaint
            )
        }
    }

    /**
     * Beleuchtete Eckpunktfarbe samt Dunst, einmal für flache Zellen (vcFlat)
     * und einmal für Zellen, die später mit der Textur multipliziert werden (vcTex).
     */
    private fun vertexColors(k: Int, fog: Float, cs: Float, sn: Float) {
        // Normale in Weltraum drehen, damit das Licht fest im Raum bleibt
        val nx = vnx[k] * cs + vnz[k] * sn
        val nz = -vnx[k] * sn + vnz[k] * cs
        val d = max(0f, nx * LX + vny[k] * LY + nz * LZ)

        val r = min(255f, vr[k] * (AMB_R + SUN_R * d) * lightGain)
        val g = min(255f, vg[k] * (AMB_G + SUN_G * d) * lightGain)
        val b = min(255f, vb[k] * (AMB_B + SUN_B * d) * lightGain)

        // Flach: gleiche mittlere Helligkeit wie die Textur, voller Dunst = exakt Dunstfarbe
        vcFlat[k] = Color.rgb(
            min(255, lerp(r * meanR, FOG_R, fog).toInt()),
            min(255, lerp(g * meanG, FOG_G, fog).toInt()),
            min(255, lerp(b * meanB, FOG_B, fog).toInt())
        )

        // Textur: Dunstfarbe vorab aufhellen, weil die Textur um ihren Mittelwert abdunkelt
        vcTex[k] = Color.rgb(
            min(255, lerp(r, min(255f, FOG_R / meanR), fog).toInt()),
            min(255, lerp(g, min(255f, FOG_G / meanG), fog).toInt()),
            min(255, lerp(b, min(255f, FOG_B / meanB), fog).toInt())
        )
    }

    private fun emitFlat(slot: Int, a: Int, b: Int, c: Int) {
        val vi = slot * 6
        verts[vi] = sx[a]
        verts[vi + 1] = sy[a]
        verts[vi + 2] = sx[b]
        verts[vi + 3] = sy[b]
        verts[vi + 4] = sx[c]
        verts[vi + 5] = sy[c]

        val ci = slot * 3
        colors[ci] = vcFlat[a]
        colors[ci + 1] = vcFlat[b]
        colors[ci + 2] = vcFlat[c]
    }

    private fun emitTextured(slot: Int, a: Int, b: Int, c: Int) {
        val vi = slot * 6
        tVerts[vi] = sx[a]
        tVerts[vi + 1] = sy[a]
        tVerts[vi + 2] = sx[b]
        tVerts[vi + 3] = sy[b]
        tVerts[vi + 4] = sx[c]
        tVerts[vi + 5] = sy[c]

        tUV[vi] = vu[a]
        tUV[vi + 1] = vv[a]
        tUV[vi + 2] = vu[b]
        tUV[vi + 3] = vv[b]
        tUV[vi + 4] = vu[c]
        tUV[vi + 5] = vv[c]

        val ci = slot * 3
        tColors[ci] = vcTex[a]
        tColors[ci + 1] = vcTex[b]
        tColors[ci + 2] = vcTex[c]
    }
}