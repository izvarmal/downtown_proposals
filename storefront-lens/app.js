/* ============================================================================
   Storefront Lens — app.js
   All application logic. Organized into commented modules:
     0. Shared utilities (image loading, canvas, color math, clustering, edges)
     1. State & localStorage persistence
     2. Theme + tab navigation
     3. Storefront Score (scoring engine + heat-map)
     4. One Big Decision Generator (rule engine + before/after composites)
     5. Sign Simulator
     6. Budget Blueprint
     7. Street Context Scanner
     8. Night / Seasonal Renderer
     9. Init / wiring
   No external requests are made anywhere in this file.
   ============================================================================ */
"use strict";

/* ============================================================================
   0. SHARED UTILITIES
   ============================================================================ */

const MAX_DIM = 640; // working resolution for pixel analysis (perf vs. accuracy tradeoff)

/** Read a File into an HTMLImageElement via a data: URL (no network involved). */
function loadImageFile(file) {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onload = (e) => {
      const img = new Image();
      img.onload = () => resolve(img);
      img.onerror = () => reject(new Error("Could not decode image"));
      img.src = e.target.result;
    };
    reader.onerror = () => reject(new Error("Could not read file"));
    reader.readAsDataURL(file);
  });
}

/** Draw an image onto a new canvas, downscaled to maxDim on its longest side. */
function drawToCanvas(img, maxDim = MAX_DIM) {
  const scale = Math.min(1, maxDim / Math.max(img.width, img.height));
  const w = Math.max(1, Math.round(img.width * scale));
  const h = Math.max(1, Math.round(img.height * scale));
  const canvas = document.createElement("canvas");
  canvas.width = w;
  canvas.height = h;
  const ctx = canvas.getContext("2d", { willReadFrequently: true });
  ctx.drawImage(img, 0, 0, w, h);
  return canvas;
}

function cloneCanvas(source) {
  const c = document.createElement("canvas");
  c.width = source.width;
  c.height = source.height;
  c.getContext("2d").drawImage(source, 0, 0);
  return c;
}

/* ---- Color math ---- */

function relLuminance(r, g, b) {
  const lin = [r, g, b].map((c) => {
    c /= 255;
    return c <= 0.03928 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4);
  });
  return 0.2126 * lin[0] + 0.7152 * lin[1] + 0.0722 * lin[2];
}

function contrastRatio(rgb1, rgb2) {
  const L1 = relLuminance(rgb1[0], rgb1[1], rgb1[2]);
  const L2 = relLuminance(rgb2[0], rgb2[1], rgb2[2]);
  const lighter = Math.max(L1, L2);
  const darker = Math.min(L1, L2);
  return (lighter + 0.05) / (darker + 0.05);
}

function rgbToHex(r, g, b) {
  return "#" + [r, g, b].map((x) => Math.max(0, Math.min(255, Math.round(x))).toString(16).padStart(2, "0")).join("");
}

function hexToRgb(hex) {
  const m = hex.replace("#", "");
  const n = parseInt(m.length === 3 ? m.split("").map((c) => c + c).join("") : m, 16);
  return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
}

function rgbToHsl(r, g, b) {
  r /= 255; g /= 255; b /= 255;
  const max = Math.max(r, g, b), min = Math.min(r, g, b);
  let h, s;
  const l = (max + min) / 2;
  if (max === min) { h = 0; s = 0; }
  else {
    const d = max - min;
    s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
    switch (max) {
      case r: h = (g - b) / d + (g < b ? 6 : 0); break;
      case g: h = (b - r) / d + 2; break;
      default: h = (r - g) / d + 4;
    }
    h *= 60;
  }
  return [h, s, l];
}

function hslToRgb(h, s, l) {
  h = ((h % 360) + 360) % 360;
  const c = (1 - Math.abs(2 * l - 1)) * s;
  const x = c * (1 - Math.abs(((h / 60) % 2) - 1));
  const m = l - c / 2;
  let [r, g, b] = [0, 0, 0];
  if (h < 60) [r, g, b] = [c, x, 0];
  else if (h < 120) [r, g, b] = [x, c, 0];
  else if (h < 180) [r, g, b] = [0, c, x];
  else if (h < 240) [r, g, b] = [0, x, c];
  else if (h < 300) [r, g, b] = [x, 0, c];
  else [r, g, b] = [c, 0, x];
  return [(r + m) * 255, (g + m) * 255, (b + m) * 255];
}

function colorDistSq(a, b) {
  const dr = a[0] - b[0], dg = a[1] - b[1], db = a[2] - b[2];
  return dr * dr + dg * dg + db * db;
}

function lerp(a, b, t) { return a + (b - a) * t; }
function lerpColor(c1, c2, t) { return [lerp(c1[0], c2[0], t), lerp(c1[1], c2[1], t), lerp(c1[2], c2[2], t)]; }
function clamp(v, lo, hi) { return Math.max(lo, Math.min(hi, v)); }

/**
 * k-means-lite: a deliberately simple, deterministic k-means clustering over
 * a sampled set of [r,g,b] pixels. Deterministic seeding (evenly-spaced
 * samples rather than random) keeps results stable across runs on the same
 * image, which matters for a diagnostic tool. Tune `k` and `iterations`
 * below if palettes look too coarse or too slow.
 */
function kMeansLite(pixels, k = 5, iterations = 6) {
  if (pixels.length === 0) return [];
  k = Math.min(k, pixels.length);
  const step = Math.max(1, Math.floor(pixels.length / k));
  let centroids = [];
  for (let i = 0; i < k; i++) centroids.push(pixels[Math.min(i * step, pixels.length - 1)].slice());

  let assignments = new Array(pixels.length).fill(0);
  for (let iter = 0; iter < iterations; iter++) {
    for (let i = 0; i < pixels.length; i++) {
      let best = 0, bestDist = Infinity;
      for (let c = 0; c < centroids.length; c++) {
        const d = colorDistSq(pixels[i], centroids[c]);
        if (d < bestDist) { bestDist = d; best = c; }
      }
      assignments[i] = best;
    }
    const sums = Array.from({ length: centroids.length }, () => [0, 0, 0, 0]);
    for (let i = 0; i < pixels.length; i++) {
      const c = assignments[i];
      sums[c][0] += pixels[i][0]; sums[c][1] += pixels[i][1]; sums[c][2] += pixels[i][2]; sums[c][3]++;
    }
    for (let c = 0; c < centroids.length; c++) {
      if (sums[c][3] > 0) centroids[c] = [sums[c][0] / sums[c][3], sums[c][1] / sums[c][3], sums[c][2] / sums[c][3]];
    }
  }
  const counts = new Array(centroids.length).fill(0);
  assignments.forEach((a) => counts[a]++);
  return centroids
    .map((c, i) => ({ rgb: c.map((v) => Math.round(v)), count: counts[i], pct: counts[i] / pixels.length }))
    .filter((c) => c.count > 0)
    .sort((a, b) => b.count - a.count);
}

/** Sample every Nth pixel from a canvas into an array of [r,g,b] (skips near-transparent). */
function samplePixels(canvas, stride = 4) {
  const ctx = canvas.getContext("2d", { willReadFrequently: true });
  const { data, width, height } = ctx.getImageData(0, 0, canvas.width, canvas.height);
  const pixels = [];
  for (let y = 0; y < height; y += stride) {
    for (let x = 0; x < width; x += stride) {
      const i = (y * width + x) * 4;
      if (data[i + 3] < 16) continue;
      pixels.push([data[i], data[i + 1], data[i + 2]]);
    }
  }
  return pixels;
}

/** Grayscale luminance buffer for a canvas. */
function toGrayscale(canvas) {
  const ctx = canvas.getContext("2d", { willReadFrequently: true });
  const { data, width, height } = ctx.getImageData(0, 0, canvas.width, canvas.height);
  const gray = new Float32Array(width * height);
  for (let p = 0, i = 0; p < data.length; p += 4, i++) {
    gray[i] = 0.299 * data[p] + 0.587 * data[p + 1] + 0.114 * data[p + 2];
  }
  return { gray, width, height };
}

/** Sobel gradient magnitude — a standard, cheap edge-density estimator. */
function sobelMagnitude(gray, width, height) {
  const mag = new Float32Array(width * height);
  const gx = [-1, 0, 1, -2, 0, 2, -1, 0, 1];
  const gy = [-1, -2, -1, 0, 0, 0, 1, 2, 1];
  for (let y = 1; y < height - 1; y++) {
    for (let x = 1; x < width - 1; x++) {
      let sx = 0, sy = 0, k = 0;
      for (let dy = -1; dy <= 1; dy++) {
        for (let dx = -1; dx <= 1; dx++, k++) {
          const v = gray[(y + dy) * width + (x + dx)];
          sx += v * gx[k];
          sy += v * gy[k];
        }
      }
      mag[y * width + x] = Math.sqrt(sx * sx + sy * sy);
    }
  }
  return mag;
}

function downloadDataUrl(dataUrl, filename) {
  const a = document.createElement("a");
  a.href = dataUrl;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  a.remove();
}

function downloadText(text, filename) {
  const blob = new Blob([text], { type: "text/plain" });
  const url = URL.createObjectURL(blob);
  downloadDataUrl(url, filename);
  setTimeout(() => URL.revokeObjectURL(url), 2000);
}

function escapeHtml(s) {
  return String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
}

/* ============================================================================
   1. STATE & LOCALSTORAGE PERSISTENCE
   ============================================================================ */

const LS_KEY = "storefrontLens.v1";

/**
 * Central in-memory application state. Canvas/Image objects are NOT
 * serializable, so only a small, lossy subset (thumbnails + numbers) is
 * mirrored to localStorage by saveStateToStorage().
 */
const state = {
  pro: false,
  theme: "light",
  images: { facade: null, sign: null, entrance: null }, // { img, canvas, dataUrl }
  score: null, // { overall, legibility, clutter, coherence, palette, heatmapBlocks, sourceKey }
  decisions: null, // { answers, moves: [...] }
  signSim: { bgCanvas: null, x: 0.5, y: 0.3 },
  street: { palette: [], flags: [] },
  night: { sourceCanvas: null },
};

function saveStateToStorage() {
  try {
    const payload = {
      pro: state.pro,
      theme: state.theme,
      score: state.score
        ? {
            overall: state.score.overall,
            legibility: state.score.legibility,
            clutter: state.score.clutter,
            coherence: state.score.coherence,
            palette: state.score.palette,
          }
        : null,
      decisionAnswers: state.decisions ? state.decisions.answers : null,
      facadeThumb: state.images.facade ? shrinkForStorage(state.images.facade.canvas) : null,
    };
    localStorage.setItem(LS_KEY, JSON.stringify(payload));
  } catch (err) {
    // localStorage can throw (quota, private mode) — persistence is a nice-to-have, never fatal.
    console.warn("Storefront Lens: could not save to localStorage", err);
  }
}

function shrinkForStorage(canvas, maxDim = 240) {
  const c = document.createElement("canvas");
  const scale = Math.min(1, maxDim / Math.max(canvas.width, canvas.height));
  c.width = Math.round(canvas.width * scale);
  c.height = Math.round(canvas.height * scale);
  c.getContext("2d").drawImage(canvas, 0, 0, c.width, c.height);
  return c.toDataURL("image/jpeg", 0.7);
}

function loadStateFromStorage() {
  try {
    const raw = localStorage.getItem(LS_KEY);
    if (!raw) return;
    const payload = JSON.parse(raw);
    state.pro = !!payload.pro;
    state.theme = payload.theme === "dark" ? "dark" : "light";
    if (payload.score) {
      renderRestoredScoreSummary(payload.score, payload.facadeThumb);
    }
  } catch (err) {
    console.warn("Storefront Lens: could not read localStorage", err);
  }
}

function renderRestoredScoreSummary(score, thumb) {
  const status = document.getElementById("analyzeStatus");
  if (!status) return;
  status.textContent = `Last session: overall score ${score.overall}/100 (upload photos again to re-analyze).`;
}

function resetStorage() {
  localStorage.removeItem(LS_KEY);
  location.reload();
}

/* ============================================================================
   2. THEME + TAB NAVIGATION
   ============================================================================ */

function applyTheme(theme) {
  state.theme = theme;
  if (theme === "dark") {
    document.documentElement.setAttribute("data-theme", "dark");
    document.getElementById("themeToggleLabel").textContent = "☀️ Light mode";
    document.getElementById("themeToggle").setAttribute("aria-pressed", "true");
  } else {
    document.documentElement.removeAttribute("data-theme");
    document.getElementById("themeToggleLabel").textContent = "🌙 Dark mode";
    document.getElementById("themeToggle").setAttribute("aria-pressed", "false");
  }
}

function initTabs() {
  const tabs = Array.from(document.querySelectorAll(".tab"));
  const panels = tabs.map((t) => document.getElementById(t.dataset.panel));

  function selectTab(index) {
    tabs.forEach((t, i) => {
      const active = i === index;
      t.setAttribute("aria-selected", active ? "true" : "false");
      t.tabIndex = active ? 0 : -1;
      panels[i].hidden = !active;
    });
    tabs[index].focus();
  }

  tabs.forEach((tab, i) => {
    tab.addEventListener("click", () => {
      tabs.forEach((t, j) => {
        t.setAttribute("aria-selected", j === i ? "true" : "false");
        t.tabIndex = j === i ? 0 : -1;
        panels[j].hidden = j !== i;
      });
    });
    tab.addEventListener("keydown", (e) => {
      if (e.key === "ArrowRight") { e.preventDefault(); selectTab((i + 1) % tabs.length); }
      else if (e.key === "ArrowLeft") { e.preventDefault(); selectTab((i - 1 + tabs.length) % tabs.length); }
      else if (e.key === "Home") { e.preventDefault(); selectTab(0); }
      else if (e.key === "End") { e.preventDefault(); selectTab(tabs.length - 1); }
    });
  });
}

function goToTab(panelId) {
  const tab = document.querySelector(`.tab[data-panel="${panelId}"]`);
  if (tab) tab.click();
}

/* ============================================================================
   3. STOREFRONT SCORE
   ============================================================================
   Heuristics implemented here (all pure pixel math, no ML models):
     - Dominant color extraction : kMeansLite() over sampled pixels
     - Legibility                : contrast ratio between "text-like" high-
                                    edge-density regions and their local
                                    background
     - Visual clutter            : mean edge density + fraction of "busy"
                                    grid blocks (Sobel-based)
     - Color coherence           : circular variance of dominant hues, with
                                    a penalty for too many competing colors
     - 3-second heat-map         : edge density weighted by a horizontal
                                    Gaussian around the vertical center-line
                                    and a vertical Gaussian around the
                                    typical sign/eye-level band
   Every tunable constant is called out in a comment so the heuristics can be
   adjusted later without re-deriving the math.
   ============================================================================ */

const SCORE_GRID_COLS = 20;
const SCORE_GRID_ROWS = 16;

/** Analyze a single canvas and return its sub-scores + palette + raw sobel data (for heat-map reuse). */
function analyzeImageMetrics(canvas) {
  const { gray, width, height } = toGrayscale(canvas);
  const mag = sobelMagnitude(gray, width, height);

  const blocks = computeGridBlocks(canvas, gray, mag, width, height);
  const legibility = computeLegibility(canvas, blocks, width, height);
  const clutter = computeClutter(blocks);

  const pixels = samplePixels(canvas, 6);
  const palette = kMeansLite(pixels, 6, 5)
    .map((c) => ({ ...c, hex: rgbToHex(...c.rgb), hsl: rgbToHsl(...c.rgb) }))
    .filter((c) => c.pct >= 0.02);
  const coherence = computeCoherence(palette);

  return { legibility, clutter, coherence, palette, sobel: { mag, width, height } };
}

/** Split the image into a grid and compute per-block edge density + luminance range — reused by legibility, clutter and the heat-map. */
function computeGridBlocks(canvas, gray, mag, width, height) {
  const bw = width / SCORE_GRID_COLS;
  const bh = height / SCORE_GRID_ROWS;
  const blocks = [];
  for (let by = 0; by < SCORE_GRID_ROWS; by++) {
    for (let bx = 0; bx < SCORE_GRID_COLS; bx++) {
      const x0 = Math.floor(bx * bw), x1 = Math.max(x0 + 1, Math.floor((bx + 1) * bw));
      const y0 = Math.floor(by * bh), y1 = Math.max(y0 + 1, Math.floor((by + 1) * bh));
      let sumMag = 0, count = 0, lo = 255, hi = 0;
      for (let y = y0; y < y1 && y < height; y++) {
        for (let x = x0; x < x1 && x < width; x++) {
          const idx = y * width + x;
          sumMag += mag[idx];
          const v = gray[idx];
          if (v < lo) lo = v;
          if (v > hi) hi = v;
          count++;
        }
      }
      blocks.push({
        bx, by, x0, y0, x1, y1,
        edgeDensity: count ? sumMag / count : 0,
        lumRange: hi - lo,
      });
    }
  }
  return blocks;
}

/**
 * Legibility: find grid blocks that look "text-like" (high edge density AND
 * a wide local luminance range — i.e. a crisp light/dark boundary, the
 * signature of lettering against a background), then measure the WCAG-style
 * contrast ratio between the darkest and lightest quartile of pixels in
 * those blocks. Falls back to a global dark/light contrast if no strong
 * text-like region is found (e.g. a bare wall with no sign yet).
 */
function computeLegibility(canvas, blocks, width, height) {
  const sorted = blocks.slice().sort((a, b) => b.edgeDensity - a.edgeDensity);
  const edgeThreshold = sorted[Math.floor(sorted.length * 0.25)]?.edgeDensity ?? 0;
  const candidates = blocks.filter((b) => b.edgeDensity > 8 && b.edgeDensity >= edgeThreshold && b.lumRange > 40);
  const ctx = canvas.getContext("2d", { willReadFrequently: true });

  const ratios = [];
  const topCandidates = candidates.sort((a, b) => b.edgeDensity - a.edgeDensity).slice(0, 24);
  for (const block of topCandidates) {
    const w = block.x1 - block.x0, h = block.y1 - block.y0;
    if (w <= 0 || h <= 0) continue;
    const { data } = ctx.getImageData(block.x0, block.y0, w, h);
    const lums = [];
    for (let i = 0; i < data.length; i += 4) lums.push({ l: relLuminance(data[i], data[i + 1], data[i + 2]), r: data[i], g: data[i + 1], b: data[i + 2] });
    lums.sort((a, b) => a.l - b.l);
    const q = Math.max(1, Math.floor(lums.length * 0.25));
    const darkAvg = averageRgb(lums.slice(0, q));
    const lightAvg = averageRgb(lums.slice(-q));
    ratios.push(contrastRatio(darkAvg, lightAvg));
  }

  let avgRatio;
  if (ratios.length > 0) {
    avgRatio = ratios.reduce((a, b) => a + b, 0) / ratios.length;
  } else {
    // Fallback: global 5th/95th percentile luminance contrast across the whole image.
    const pixels = samplePixels(canvas, 5).map((p) => ({ l: relLuminance(...p), rgb: p }));
    pixels.sort((a, b) => a.l - b.l);
    const q = Math.max(1, Math.floor(pixels.length * 0.1));
    const darkAvg = averageRgbFromPixels(pixels.slice(0, q).map((p) => p.rgb));
    const lightAvg = averageRgbFromPixels(pixels.slice(-q).map((p) => p.rgb));
    avgRatio = contrastRatio(darkAvg, lightAvg) * 0.75; // discount: no confirmed text region found
  }

  // Map contrast ratio (typically 1..21) to a 0-100 score. WCAG AA (4.5) ~ 65, AAA (7) ~ 85.
  const score = clamp(((avgRatio - 1) / (12 - 1)) * 100, 0, 100);
  return Math.round(score);
}

function averageRgb(lumEntries) {
  const sum = lumEntries.reduce((acc, e) => [acc[0] + e.r, acc[1] + e.g, acc[2] + e.b], [0, 0, 0]);
  return sum.map((v) => v / lumEntries.length);
}
function averageRgbFromPixels(pixelArr) {
  const sum = pixelArr.reduce((acc, p) => [acc[0] + p[0], acc[1] + p[1], acc[2] + p[2]], [0, 0, 0]);
  return sum.map((v) => v / pixelArr.length);
}

/**
 * Clutter (reported as "visual clarity", higher = calmer / less cluttered):
 * combines mean edge density across the image with the fraction of grid
 * blocks that are "busy" (edge density above an empirical threshold). A
 * storefront with one clean sign and clear glass scores high; one covered
 * in decals, cables and mixed signage scores low.
 */
function computeClutter(blocks) {
  const densities = blocks.map((b) => b.edgeDensity);
  const meanDensity = densities.reduce((a, b) => a + b, 0) / densities.length;
  const normalizedMean = clamp(meanDensity / 40, 0, 1); // 40 ~= empirically busy block on 0-640px working images
  const busyThreshold = 30;
  const busyFraction = densities.filter((d) => d > busyThreshold).length / densities.length;

  const clutterRaw = 0.55 * normalizedMean + 0.45 * busyFraction;
  const clarityScore = 100 - clamp(clutterRaw * 100, 0, 100);
  return Math.round(clarityScore);
}

/**
 * Color coherence: circular variance of the hues of visually-significant
 * (pct >= 4%) and reasonably saturated (sat > 0.15) dominant colors. Tightly
 * clustered hues (or a near-neutral palette) score high; a scattershot of
 * unrelated saturated hues scores low. A penalty is applied for palettes
 * with more than four significant competing colors.
 */
function computeCoherence(palette) {
  const significant = palette.filter((c) => c.pct >= 0.04);
  const colorful = significant.filter((c) => c.hsl[1] > 0.15);

  let baseScore;
  if (colorful.length < 2) {
    baseScore = 88; // neutral / near-monochrome palettes are inherently coherent
  } else {
    let sx = 0, sy = 0, wSum = 0;
    for (const c of colorful) {
      const rad = (c.hsl[0] * Math.PI) / 180;
      sx += Math.cos(rad) * c.pct;
      sy += Math.sin(rad) * c.pct;
      wSum += c.pct;
    }
    const R = wSum > 0 ? Math.sqrt(sx * sx + sy * sy) / wSum : 0;
    baseScore = R * 100;
  }

  const complexityPenalty = Math.max(0, significant.length - 4) * 8;
  return Math.round(clamp(baseScore - complexityPenalty, 0, 100));
}

/**
 * "3-second" heat-map: edge density per grid block weighted by a horizontal
 * Gaussian centered on the image's vertical mid-line (people scan toward
 * the center first) and a vertical Gaussian centered ~38% down from the top
 * (typical sign / eye-level band). Tune `sigmaX` / `sigmaY` / `centerY`
 * below to shift where the simulated attention lands.
 */
function computeHeatmapBlocks(sobel) {
  const { mag, width, height } = sobel;
  const cols = SCORE_GRID_COLS, rows = SCORE_GRID_ROWS;
  const bw = width / cols, bh = height / rows;
  const sigmaX = 0.22, sigmaY = 0.28, centerY = 0.38;
  const raw = [];
  let maxIntensity = 0;

  for (let by = 0; by < rows; by++) {
    for (let bx = 0; bx < cols; bx++) {
      const x0 = Math.floor(bx * bw), x1 = Math.max(x0 + 1, Math.floor((bx + 1) * bw));
      const y0 = Math.floor(by * bh), y1 = Math.max(y0 + 1, Math.floor((by + 1) * bh));
      let sum = 0, count = 0;
      for (let y = y0; y < y1 && y < height; y++) {
        for (let x = x0; x < x1 && x < width; x++) { sum += mag[y * width + x]; count++; }
      }
      const edgeDensity = count ? sum / count : 0;
      const cx = (bx + 0.5) / cols;
      const cy = (by + 0.5) / rows;
      const centerWeight = Math.exp(-((cx - 0.5) ** 2) / (2 * sigmaX * sigmaX));
      const verticalWeight = Math.exp(-((cy - centerY) ** 2) / (2 * sigmaY * sigmaY));
      const intensity = edgeDensity * centerWeight * verticalWeight;
      raw.push({ fx0: bx / cols, fy0: by / rows, fx1: (bx + 1) / cols, fy1: (by + 1) / rows, intensity });
      if (intensity > maxIntensity) maxIntensity = intensity;
    }
  }
  if (maxIntensity > 0) raw.forEach((b) => (b.intensity /= maxIntensity));
  return raw;
}

/** Paint the heat-map onto any canvas context at any target size (blocks are stored as fractional coordinates). */
function drawHeatmapOverlay(ctx, targetW, targetH, blocks) {
  const yellow = [255, 221, 51];
  const red = [217, 37, 37];
  for (const b of blocks) {
    if (b.intensity < 0.14) continue;
    const t = clamp(b.intensity, 0, 1);
    let color, alpha;
    if (t < 0.5) {
      color = yellow;
      alpha = (t / 0.5) * 0.32;
    } else {
      const tt = (t - 0.5) / 0.5;
      color = lerpColor(yellow, red, tt);
      alpha = 0.32 + tt * 0.38;
    }
    ctx.fillStyle = `rgba(${color[0] | 0}, ${color[1] | 0}, ${color[2] | 0}, ${alpha.toFixed(3)})`;
    ctx.fillRect(b.fx0 * targetW, b.fy0 * targetH, (b.fx1 - b.fx0) * targetW + 1, (b.fy1 - b.fy0) * targetH + 1);
  }
}

function primaryScoreImageKey() {
  if (state.images.facade) return "facade";
  if (state.images.sign) return "sign";
  if (state.images.entrance) return "entrance";
  return null;
}

function updateAnalyzeButtonState() {
  const btn = document.getElementById("btnAnalyze");
  btn.disabled = !primaryScoreImageKey();
}

async function handleScoreFileInput(key, file) {
  if (!file) return;
  const previewEl = document.getElementById(`preview-${key}`);
  previewEl.textContent = "Loading…";
  try {
    const img = await loadImageFile(file);
    const canvas = drawToCanvas(img);
    state.images[key] = { img, canvas, dataUrl: canvas.toDataURL("image/jpeg", 0.85) };
    previewEl.innerHTML = "";
    const thumb = document.createElement("img");
    thumb.src = state.images[key].dataUrl;
    thumb.alt = `${key} preview`;
    previewEl.appendChild(thumb);
  } catch (err) {
    previewEl.textContent = "Could not load that image — try a different file.";
    console.error(err);
  }
  updateAnalyzeButtonState();
}

function weightedAverage(entries) {
  // entries: [[value, weight], ...]
  const wSum = entries.reduce((a, [, w]) => a + w, 0);
  if (wSum === 0) return 0;
  return entries.reduce((a, [v, w]) => a + v * w, 0) / wSum;
}

async function analyzeStorefront() {
  const status = document.getElementById("analyzeStatus");
  const btn = document.getElementById("btnAnalyze");
  const primaryKey = primaryScoreImageKey();
  if (!primaryKey) return;

  btn.disabled = true;
  status.textContent = "Analyzing pixels…";
  await new Promise((r) => setTimeout(r, 10)); // let the status text paint before heavy sync work

  const weights = { facade: 1.0, sign: 0.6, entrance: 0.5 };
  const perImage = [];
  for (const key of ["facade", "sign", "entrance"]) {
    if (state.images[key]) {
      const metrics = analyzeImageMetrics(state.images[key].canvas);
      perImage.push({ key, metrics, weight: weights[key] });
    }
  }

  const legibility = Math.round(weightedAverage(perImage.map((p) => [p.metrics.legibility, p.weight])));
  const clutter = Math.round(weightedAverage(perImage.map((p) => [p.metrics.clutter, p.weight])));
  const coherence = Math.round(weightedAverage(perImage.map((p) => [p.metrics.coherence, p.weight])));
  const overall = Math.round(legibility * 0.4 + clutter * 0.3 + coherence * 0.3);

  const primaryMetrics = perImage.find((p) => p.key === primaryKey).metrics;
  const heatmapBlocks = computeHeatmapBlocks(primaryMetrics.sobel);

  state.score = {
    overall, legibility, clutter, coherence,
    palette: primaryMetrics.palette,
    heatmapBlocks,
    sourceKey: primaryKey,
  };

  renderScoreResults();
  saveStateToStorage();
  status.textContent = `Done — analyzed ${perImage.length} photo${perImage.length > 1 ? "s" : ""}.`;
  btn.disabled = false;
}

function scoreLabel(score) {
  if (score >= 80) return "Strong";
  if (score >= 60) return "Solid";
  if (score >= 40) return "Needs work";
  return "Weak";
}

function renderScoreResults() {
  const s = state.score;
  const primaryCanvas = state.images[s.sourceKey].canvas;

  const canvasOriginal = document.getElementById("canvasOriginal");
  canvasOriginal.width = primaryCanvas.width;
  canvasOriginal.height = primaryCanvas.height;
  canvasOriginal.getContext("2d").drawImage(primaryCanvas, 0, 0);

  const canvasHeatmap = document.getElementById("canvasHeatmap");
  canvasHeatmap.width = primaryCanvas.width;
  canvasHeatmap.height = primaryCanvas.height;
  const hctx = canvasHeatmap.getContext("2d");
  hctx.drawImage(primaryCanvas, 0, 0);
  drawHeatmapOverlay(hctx, canvasHeatmap.width, canvasHeatmap.height, s.heatmapBlocks);
  if (!state.pro) drawWatermark(hctx, canvasHeatmap.width, canvasHeatmap.height);

  document.getElementById("scoreResults").hidden = false;
  document.getElementById("scoreExportRow").hidden = false;

  document.getElementById("overallScoreValue").textContent = s.overall;
  document.getElementById("scoreRing").style.setProperty("--pct", s.overall);

  const list = document.getElementById("subscoreList");
  const rows = [
    ["Legibility", s.legibility],
    ["Visual clarity", s.clutter],
    ["Color coherence", s.coherence],
  ];
  list.innerHTML = rows
    .map(
      ([label, value]) => `
      <li>
        <span>${label}</span>
        <span class="meter" role="img" aria-label="${label} score ${value} out of 100, ${scoreLabel(value)}">
          <span style="width:${value}%"></span>
        </span>
        <span>${value}</span>
      </li>`
    )
    .join("");

  const paletteEl = document.getElementById("palettePreview");
  paletteEl.innerHTML = s.palette
    .slice(0, 6)
    .map(
      (c) => `
      <span class="swatch">
        <span class="swatch-color" style="background:${c.hex}"></span>
        ${c.hex}<br>${Math.round(c.pct * 100)}%
      </span>`
    )
    .join("");
}

function drawWatermark(ctx, w, h) {
  ctx.save();
  ctx.font = `${Math.max(11, Math.round(w * 0.022))}px sans-serif`;
  ctx.fillStyle = "rgba(255,255,255,0.75)";
  ctx.strokeStyle = "rgba(0,0,0,0.35)";
  ctx.lineWidth = 3;
  const text = "Storefront Lens";
  const pad = 8;
  const metrics = ctx.measureText(text);
  const x = w - metrics.width - pad;
  const y = h - pad;
  ctx.strokeText(text, x, y);
  ctx.fillText(text, x, y);
  ctx.restore();
}

function buildScoreSummaryText() {
  const s = state.score;
  const lines = [
    "STOREFRONT LENS — Score Summary",
    `Generated: ${new Date().toLocaleString()}`,
    "",
    `Overall Score: ${s.overall}/100 (${scoreLabel(s.overall)})`,
    `  Legibility:      ${s.legibility}/100`,
    `  Visual clarity:  ${s.clutter}/100`,
    `  Color coherence: ${s.coherence}/100`,
    "",
    "Dominant colors:",
    ...s.palette.slice(0, 6).map((c) => `  ${c.hex}  —  ${Math.round(c.pct * 100)}% of frame`),
    "",
    "Heat-map note: highlighted zones show where a first-time passer-by's",
    "eye is most likely to land in the first three seconds (center-weighted,",
    "upper-middle band).",
  ];
  return lines.join("\n");
}

/* ============================================================================
   4. ONE BIG DECISION GENERATOR
   ============================================================================
   A small rule-based engine, not a model: each of six candidate "moves" is
   grouped into one of three categories (sign / color / declutter). Every
   category contributes exactly one winner — the candidate with the highest
   rule score — so the generator always returns exactly three moves, one per
   problem area, ranked by score. Scores blend the Storefront Score
   sub-scores (when available) with the questionnaire answers; with no prior
   Score, sensible neutral defaults keep the tool fully usable standalone.
   ============================================================================ */

const MOVE_CATALOG = {
  "simplify-sign": {
    title: "Simplify the sign hierarchy",
    category: "sign",
    zone: { x: 0.06, y: 0.04, w: 0.88, h: 0.22 },
    why: (a) => `Too many words or competing type styles fight for attention. One bold word, read in under a second, works harder for a ${a.category}.`,
    drawBefore: (ctx, w, h, zone, pal) => {
      drawZoneHighlight(ctx, w, h, zone, "rgba(217,37,37,0.28)", "#d92525");
      drawCallout(ctx, w, h, zone.x + zone.w * 0.5, zone.y + zone.h, zone.x + zone.w * 0.5, Math.min(0.92, zone.y + zone.h + 0.28), "Cluttered / hard to scan", "#d92525");
    },
    drawAfter: (ctx, w, h, zone, pal) => {
      const bg = pal[0], fg = pickReadableTextColor(bg);
      const bx = zone.x * w, by = zone.y * h, bw = zone.w * w, bh = zone.h * h;
      ctx.fillStyle = hexOrRgb(bg);
      roundRect(ctx, bx, by, bw, bh, Math.min(14, bh * 0.2));
      ctx.fill();
      ctx.fillStyle = fg;
      ctx.font = `700 ${Math.round(bh * 0.42)}px "Arial", sans-serif`;
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText("ONE BOLD WORD", bx + bw / 2, by + bh / 2);
      captionBelow(ctx, w, h, zone, "One word, high contrast, legible from the street");
    },
  },
  "increase-contrast": {
    title: "Increase sign contrast",
    category: "sign",
    zone: { x: 0.06, y: 0.04, w: 0.88, h: 0.22 },
    why: () => "Your lettering blends into its background. Passers-by need a strong light/dark split to read a sign while moving.",
    drawBefore: (ctx, w, h, zone) => {
      drawZoneHighlight(ctx, w, h, zone, "rgba(217,37,37,0.22)", "#d92525");
      captionBelow(ctx, w, h, zone, `Low contrast — hard to read at a glance`);
    },
    drawAfter: (ctx, w, h, zone, pal) => {
      const bx = zone.x * w, by = zone.y * h, bw = zone.w * w, bh = zone.h * h;
      ctx.fillStyle = "#161616";
      roundRect(ctx, bx, by, bw, bh, Math.min(14, bh * 0.2));
      ctx.fill();
      ctx.fillStyle = "#ffffff";
      ctx.font = `700 ${Math.round(bh * 0.4)}px "Arial", sans-serif`;
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText("HIGH CONTRAST", bx + bw / 2, by + bh / 2);
      captionBelow(ctx, w, h, zone, "Dark panel + light lettering, 12:1+ contrast");
    },
  },
  "unify-color": {
    title: "Unify the color story",
    category: "color",
    zone: { x: 0, y: 0, w: 1, h: 1 },
    why: (a) => `A single, deliberate palette reads as "${a.brandWords[0] || "intentional"}" from across the street. Right now too many unrelated colors compete.`,
    drawBefore: (ctx, w, h, zone, pal) => {
      const clashY = h * 0.86;
      pal.slice(0, 4).forEach((c, i) => {
        ctx.fillStyle = hexOrRgb(c);
        ctx.fillRect(w * 0.06 + i * 34, clashY, 26, 26);
        ctx.strokeStyle = "#d92525";
        ctx.lineWidth = 2;
        ctx.beginPath();
        ctx.moveTo(w * 0.06 + i * 34, clashY);
        ctx.lineTo(w * 0.06 + i * 34 + 26, clashY + 26);
        ctx.moveTo(w * 0.06 + i * 34 + 26, clashY);
        ctx.lineTo(w * 0.06 + i * 34, clashY + 26);
        ctx.stroke();
      });
      captionBelow(ctx, w, h, { x: 0, y: 0.86, w: 1, h: 0.14 }, "Competing, unrelated colors");
    },
    drawAfter: (ctx, w, h, zone, pal) => {
      const [a, b] = [pal[0], pal[1] || pal[0]];
      ctx.save();
      ctx.globalAlpha = 0.22;
      ctx.fillStyle = hexOrRgb(a);
      ctx.fillRect(0, 0, w, h);
      ctx.restore();
      const swY = h * 0.86;
      [a, b].forEach((c, i) => {
        ctx.fillStyle = hexOrRgb(c);
        ctx.fillRect(w * 0.06 + i * 34, swY, 26, 26);
        ctx.strokeStyle = "#ffffff";
        ctx.lineWidth = 2;
        ctx.strokeRect(w * 0.06 + i * 34, swY, 26, 26);
      });
      captionBelow(ctx, w, h, { x: 0, y: 0.86, w: 1, h: 0.14 }, "One consistent two-color story");
    },
  },
  "add-accent-color": {
    title: "Introduce one confident accent color",
    category: "color",
    zone: { x: 0, y: 0.62, w: 1, h: 0.1 },
    why: (a) => `Your palette is coherent but quiet — a single accent (door, awning edge, trim) gives ${a.brandWords[0] || "your brand"} a focal point without adding clutter.`,
    drawBefore: (ctx, w, h, zone) => {
      captionBelow(ctx, w, h, zone, "Palette is safe, but has no focal point");
    },
    drawAfter: (ctx, w, h, zone, pal) => {
      const accent = pal[Math.min(2, pal.length - 1)] || pal[0];
      ctx.fillStyle = hexOrRgb(accent);
      ctx.fillRect(zone.x * w, zone.y * h, zone.w * w, zone.h * h);
      captionBelow(ctx, w, h, zone, `Accent stripe in ${accent} draws the eye`);
    },
  },
  "clear-entrance": {
    title: "Clear the entrance clutter",
    category: "declutter",
    zone: { x: 0.1, y: 0.68, w: 0.8, h: 0.3 },
    why: () => "Stacked boxes, signage or debris near the door make people hesitate before entering. A clear, obvious path in is worth more than any single decoration.",
    drawBefore: (ctx, w, h, zone) => {
      drawZoneHighlight(ctx, w, h, zone, "rgba(217,37,37,0.25)", "#d92525");
      // scribble = illustrative "clutter" marks, not photorealistic
      ctx.strokeStyle = "#d92525";
      ctx.lineWidth = 2;
      const bx = zone.x * w, by = zone.y * h, bw = zone.w * w, bh = zone.h * h;
      for (let i = 0; i < 5; i++) {
        ctx.beginPath();
        ctx.moveTo(bx + Math.random() * bw, by + Math.random() * bh);
        ctx.lineTo(bx + Math.random() * bw, by + Math.random() * bh);
        ctx.stroke();
      }
      captionBelow(ctx, w, h, zone, "Clutter blocks the sightline to the door");
    },
    drawAfter: (ctx, w, h, zone, pal) => {
      const bx = zone.x * w, by = zone.y * h, bw = zone.w * w, bh = zone.h * h;
      ctx.fillStyle = "rgba(255,255,255,0.88)";
      ctx.fillRect(bx, by, bw, bh);
      // simple geometric door
      const doorW = bw * 0.28, doorH = bh * 0.8;
      const doorX = bx + bw / 2 - doorW / 2, doorY = by + bh - doorH;
      ctx.fillStyle = hexOrRgb(pal[0]);
      ctx.fillRect(doorX, doorY, doorW, doorH);
      // simple potted plant (circle + triangle)
      const potX = doorX - doorW * 0.55, potY = doorY + doorH * 0.72;
      ctx.fillStyle = "#7a5230";
      ctx.fillRect(potX - 8, potY, 16, 14);
      ctx.fillStyle = "#3f7d4a";
      ctx.beginPath();
      ctx.moveTo(potX, potY);
      ctx.lineTo(potX - 14, potY - 26);
      ctx.lineTo(potX + 14, potY - 26);
      ctx.closePath();
      ctx.fill();
      captionBelow(ctx, w, h, zone, "Clear sightline: door + one simple accent");
    },
  },
  "reduce-window-clutter": {
    title: "Reduce window sign clutter",
    category: "declutter",
    zone: { x: 0.08, y: 0.32, w: 0.84, h: 0.32 },
    why: () => "Every extra taped-up flyer or decal is one more thing competing for a 3-second glance. Two or three signs, well-spaced, outperform ten.",
    drawBefore: (ctx, w, h, zone) => {
      drawZoneHighlight(ctx, w, h, zone, "rgba(217,37,37,0.22)", "#d92525");
      const bx = zone.x * w, by = zone.y * h, bw = zone.w * w, bh = zone.h * h;
      ctx.strokeStyle = "#d92525";
      ctx.lineWidth = 1.5;
      for (let i = 0; i < 6; i++) {
        const rx = bx + (i % 3) * (bw / 3) + bw * 0.03;
        const ry = by + Math.floor(i / 3) * (bh / 2) + bh * 0.05;
        ctx.strokeRect(rx, ry, bw / 3 - bw * 0.06, bh / 2 - bh * 0.1);
      }
      captionBelow(ctx, w, h, zone, "Too many competing window signs");
    },
    drawAfter: (ctx, w, h, zone, pal) => {
      const bx = zone.x * w, by = zone.y * h, bw = zone.w * w, bh = zone.h * h;
      ctx.fillStyle = "rgba(255,255,255,0.5)";
      ctx.fillRect(bx, by, bw, bh);
      const signW = bw * 0.28, signH = bh * 0.34;
      [0.22, 0.72].forEach((fx, i) => {
        const sx = bx + bw * fx - signW / 2, sy = by + bh * 0.5 - signH / 2;
        ctx.fillStyle = hexOrRgb(pal[i] || pal[0]);
        roundRect(ctx, sx, sy, signW, signH, 6);
        ctx.fill();
      });
      captionBelow(ctx, w, h, zone, "Two clean, evenly-spaced signs max");
    },
  },
};

const MOVE_CATEGORIES = { sign: ["simplify-sign", "increase-contrast"], color: ["unify-color", "add-accent-color"], declutter: ["clear-entrance", "reduce-window-clutter"] };

function scoreMovesForContext(ctx) {
  const { legibility, clutter, coherence, answers } = ctx;
  const bonus = (id) => (answers.frustration === id ? 34 : 0);
  return {
    "simplify-sign": 20 + (100 - legibility) * 0.9 + bonus("cluttered-sign"),
    "increase-contrast": 8 + (100 - legibility) * 1.15 + bonus("cluttered-sign") * 0.35,
    "unify-color": 20 + (100 - coherence) * 0.9 + bonus("inconsistent-colors") + bonus("blends-in") * 0.5,
    "add-accent-color": 10 + (100 - coherence) * 0.35 + (coherence > 65 ? 22 : 0) + bonus("blends-in"),
    "clear-entrance": 20 + (100 - clutter) * 0.9 + bonus("messy-entrance"),
    "reduce-window-clutter": 8 + (100 - clutter) * 1.1 + bonus("too-much-signage"),
  };
}

function generateMoves(answers) {
  const s = state.score;
  const ctx = {
    legibility: s ? s.legibility : 60,
    clutter: s ? s.clutter : 60,
    coherence: s ? s.coherence : 60,
    answers,
  };
  const scores = scoreMovesForContext(ctx);
  const moves = Object.entries(MOVE_CATEGORIES).map(([category, candidates]) => {
    const winnerId = candidates.reduce((best, id) => (scores[id] > scores[best] ? id : best), candidates[0]);
    return { id: winnerId, category, score: scores[winnerId], ...MOVE_CATALOG[winnerId] };
  });
  moves.sort((a, b) => b.score - a.score);
  return moves;
}

function pickPaletteForDecisions() {
  if (state.score && state.score.palette.length >= 2) return state.score.palette.slice(0, 5).map((c) => c.hex);
  return ["#2b3a42", "#e3d9c2", "#b5502f", "#3f7d4a", "#f4b400"];
}

function getDecisionSourceCanvas() {
  const key = primaryScoreImageKey();
  if (key) return state.images[key].canvas;
  return generatePlaceholderStorefrontCanvas();
}

/** A plain geometric storefront illustration, used only when the user hasn't uploaded a photo yet — keeps this tool fully usable standalone. */
function generatePlaceholderStorefrontCanvas() {
  const w = 640, h = 480;
  const c = document.createElement("canvas");
  c.width = w; c.height = h;
  const ctx = c.getContext("2d");
  ctx.fillStyle = "#cfd6da";
  ctx.fillRect(0, 0, w, h);
  ctx.fillStyle = "#9aa5ab";
  ctx.fillRect(0, h * 0.78, w, h * 0.22);
  ctx.fillStyle = "#e7ded0";
  ctx.fillRect(w * 0.08, h * 0.32, w * 0.84, h * 0.42);
  ctx.strokeStyle = "#7c848a";
  ctx.lineWidth = 3;
  ctx.strokeRect(w * 0.08, h * 0.32, w * 0.84, h * 0.42);
  ctx.fillStyle = "#88979c";
  ctx.fillRect(w * 0.42, h * 0.58, w * 0.16, h * 0.2);
  return c;
}

/* ---- generic illustrative drawing helpers (fractional coords 0..1) ---- */

function drawZoneHighlight(ctx, w, h, zone, fillStyle, strokeStyle) {
  const x = zone.x * w, y = zone.y * h, bw = zone.w * w, bh = zone.h * h;
  ctx.save();
  ctx.fillStyle = fillStyle;
  ctx.fillRect(x, y, bw, bh);
  ctx.strokeStyle = strokeStyle;
  ctx.lineWidth = 3;
  ctx.setLineDash([8, 6]);
  ctx.strokeRect(x, y, bw, bh);
  ctx.restore();
}

function drawCallout(ctx, w, h, fx0, fy0, fx1, fy1, text, color) {
  const x0 = fx0 * w, y0 = fy0 * h, x1 = fx1 * w, y1 = fy1 * h;
  ctx.save();
  ctx.strokeStyle = color;
  ctx.fillStyle = color;
  ctx.lineWidth = 2.5;
  ctx.beginPath();
  ctx.moveTo(x0, y0);
  ctx.lineTo(x1, y1);
  ctx.stroke();
  const angle = Math.atan2(y1 - y0, x1 - x0);
  ctx.beginPath();
  ctx.moveTo(x1, y1);
  ctx.lineTo(x1 - 9 * Math.cos(angle - 0.4), y1 - 9 * Math.sin(angle - 0.4));
  ctx.lineTo(x1 - 9 * Math.cos(angle + 0.4), y1 - 9 * Math.sin(angle + 0.4));
  ctx.closePath();
  ctx.fill();

  ctx.font = `600 ${Math.max(12, Math.round(w * 0.028))}px "Arial", sans-serif`;
  const padding = 6;
  const textW = ctx.measureText(text).width;
  const bubbleX = clamp(x1 - textW / 2 - padding, 4, w - textW - padding * 2 - 4);
  const bubbleY = Math.min(y1 + 6, h - 26);
  ctx.fillStyle = "rgba(0,0,0,0.72)";
  roundRect(ctx, bubbleX, bubbleY, textW + padding * 2, 22, 5);
  ctx.fill();
  ctx.fillStyle = "#ffffff";
  ctx.textAlign = "left";
  ctx.textBaseline = "middle";
  ctx.fillText(text, bubbleX + padding, bubbleY + 11);
  ctx.restore();
}

function captionBelow(ctx, w, h, zone, text) {
  ctx.save();
  ctx.font = `600 ${Math.max(11, Math.round(w * 0.026))}px "Arial", sans-serif`;
  const padding = 6;
  const textW = Math.min(w - 16, ctx.measureText(text).width);
  const x = clamp(zone.x * w, 4, w - textW - padding * 2 - 4);
  const y = clamp((zone.y + zone.h) * h + 6, 4, h - 24);
  ctx.fillStyle = "rgba(0,0,0,0.72)";
  roundRect(ctx, x, y, textW + padding * 2, 22, 5);
  ctx.fill();
  ctx.fillStyle = "#ffffff";
  ctx.textAlign = "left";
  ctx.textBaseline = "middle";
  ctx.fillText(text, x + padding, y + 11);
  ctx.restore();
}

function roundRect(ctx, x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r);
  ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r);
  ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}

function hexOrRgb(v) { return v && v.startsWith("#") ? v : rgbToHex(...(v || [128, 128, 128])); }

function pickReadableTextColor(bgHex) {
  const rgb = hexToRgb(bgHex);
  return relLuminance(...rgb) > 0.42 ? "#161616" : "#ffffff";
}

function buildMoveCanvasPair(move, sourceCanvas, palette) {
  const before = cloneCanvas(sourceCanvas);
  const after = cloneCanvas(sourceCanvas);
  const bctx = before.getContext("2d");
  const actx = after.getContext("2d");
  move.drawBefore(bctx, before.width, before.height, move.zone, palette);
  move.drawAfter(actx, after.width, after.height, move.zone, palette);
  return { before, after };
}

function renderDecisionResults(moves, answers) {
  const container = document.getElementById("decisionResults");
  const sourceCanvas = getDecisionSourceCanvas();
  const palette = pickPaletteForDecisions();
  container.innerHTML = "";
  container.hidden = false;

  moves.forEach((move, i) => {
    const { before, after } = buildMoveCanvasPair(move, sourceCanvas, palette);
    const card = document.createElement("div");
    card.className = "move-card";
    card.innerHTML = `
      <h3><span class="move-rank">${i + 1}</span> ${escapeHtml(move.title)}</h3>
      <p class="move-why">${escapeHtml(move.why(answers))}</p>
      <div class="before-after">
        <figure class="canvas-figure"><figcaption>Before</figcaption></figure>
        <figure class="canvas-figure"><figcaption>After (illustrative)</figcaption></figure>
      </div>
    `;
    const figs = card.querySelectorAll(".before-after figure");
    figs[0].appendChild(before);
    figs[1].appendChild(after);
    container.appendChild(card);
  });

  state.decisions = { answers, moves };
  saveStateToStorage();
}

function handleDecisionFormSubmit(e) {
  e.preventDefault();
  const category = document.getElementById("bizCategory").value;
  const rawWords = document.getElementById("brandWords").value;
  const brandWords = rawWords.split(",").map((w) => w.trim()).filter(Boolean).slice(0, 5);
  const frustration = document.getElementById("frustration").value;

  if (brandWords.length < 3) {
    alert("Please enter at least three brand words, separated by commas.");
    return;
  }

  const answers = { category, brandWords, frustration };
  const moves = generateMoves(answers);
  renderDecisionResults(moves, answers);
}

/* ============================================================================
   5. SIGN SIMULATOR
   ============================================================================ */

function getSignParams() {
  return {
    text: document.getElementById("signText").value || "",
    font: document.getElementById("signFont").value,
    size: parseInt(document.getElementById("signSize").value, 10) || 48,
    color: document.getElementById("signColor").value,
    material: document.getElementById("signMaterial").value,
  };
}

function measureSign(ctx, params) {
  ctx.font = `700 ${params.size}px ${params.font}`;
  const text = params.text || " ";
  const m = ctx.measureText(text);
  const width = Math.max(10, m.width);
  const ascent = m.actualBoundingBoxAscent || params.size * 0.8;
  const descent = m.actualBoundingBoxDescent || params.size * 0.25;
  return { width, height: ascent + descent, ascent, descent };
}

/** amt in [-1, 1]: positive shades toward white (highlight), negative toward black (shadow). */
function shadeColor(rgb, amt) {
  const target = amt > 0 ? [255, 255, 255] : [0, 0, 0];
  const f = Math.abs(amt);
  return rgbToHex(lerp(rgb[0], target[0], f), lerp(rgb[1], target[1], f), lerp(rgb[2], target[2], f));
}

/** Renders the sign text at (x, y) center point using one of three material simulations. */
function drawSignGlyph(ctx, x, y, params, box) {
  ctx.save();
  ctx.font = `700 ${params.size}px ${params.font}`;
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  const rgb = hexToRgb(params.color);

  if (params.material === "flat") {
    ctx.fillStyle = params.color;
    ctx.fillText(params.text, x, y);
  } else if (params.material === "outlined") {
    ctx.lineWidth = Math.max(2, params.size * 0.09);
    ctx.strokeStyle = shadeColor(rgb, -0.55);
    ctx.lineJoin = "round";
    ctx.strokeText(params.text, x, y);
    ctx.fillStyle = params.color;
    ctx.fillText(params.text, x, y);
  } else {
    // faux-bevel: vertical gradient (light top -> base -> dark bottom) plus a soft
    // drop shadow and a thin highlight stroke to fake dimensional channel letters.
    const grad = ctx.createLinearGradient(x, y - box.height / 2, x, y + box.height / 2);
    grad.addColorStop(0, shadeColor(rgb, 0.5));
    grad.addColorStop(0.55, params.color);
    grad.addColorStop(1, shadeColor(rgb, -0.5));
    ctx.shadowColor = "rgba(0,0,0,0.55)";
    ctx.shadowBlur = Math.max(2, params.size * 0.07);
    ctx.shadowOffsetY = Math.max(1, params.size * 0.06);
    ctx.fillStyle = grad;
    ctx.fillText(params.text, x, y);
    ctx.shadowColor = "transparent";
    ctx.strokeStyle = shadeColor(rgb, 0.65);
    ctx.lineWidth = Math.max(1, params.size * 0.02);
    ctx.strokeText(params.text, x, y - box.height * 0.015);
  }
  ctx.restore();
}

function renderSignCanvas() {
  const canvas = document.getElementById("canvasSign");
  const bg = state.signSim.bgCanvas;
  if (!bg) return;
  canvas.width = bg.width;
  canvas.height = bg.height;
  const ctx = canvas.getContext("2d");
  ctx.drawImage(bg, 0, 0);
  const params = getSignParams();
  const box = measureSign(ctx, params);
  const x = state.signSim.x * canvas.width;
  const y = state.signSim.y * canvas.height;
  drawSignGlyph(ctx, x, y, params, box);
}

function syncSignPositionInputs() {
  const xPct = Math.round(state.signSim.x * 100);
  const yPct = Math.round(state.signSim.y * 100);
  document.getElementById("signX").value = xPct;
  document.getElementById("signXVal").textContent = xPct;
  document.getElementById("signY").value = yPct;
  document.getElementById("signYVal").textContent = yPct;
}

function canvasPointFromEvent(canvas, e) {
  const rect = canvas.getBoundingClientRect();
  const scaleX = canvas.width / rect.width;
  const scaleY = canvas.height / rect.height;
  return { x: (e.clientX - rect.left) * scaleX, y: (e.clientY - rect.top) * scaleY };
}

function initSignDragging() {
  const canvas = document.getElementById("canvasSign");
  let dragging = false;

  const moveTo = (e) => {
    if (!state.signSim.bgCanvas) return;
    const p = canvasPointFromEvent(canvas, e);
    state.signSim.x = clamp(p.x / canvas.width, 0, 1);
    state.signSim.y = clamp(p.y / canvas.height, 0, 1);
    syncSignPositionInputs();
    renderSignCanvas();
  };

  canvas.addEventListener("pointerdown", (e) => {
    if (!state.signSim.bgCanvas) return;
    dragging = true;
    canvas.setPointerCapture(e.pointerId);
    moveTo(e);
  });
  canvas.addEventListener("pointermove", (e) => { if (dragging) moveTo(e); });
  canvas.addEventListener("pointerup", () => { dragging = false; });
  canvas.addEventListener("pointercancel", () => { dragging = false; });

  canvas.addEventListener("keydown", (e) => {
    if (!state.signSim.bgCanvas) return;
    const step = e.shiftKey ? 0.05 : 0.01;
    let handled = true;
    if (e.key === "ArrowLeft") state.signSim.x = clamp(state.signSim.x - step, 0, 1);
    else if (e.key === "ArrowRight") state.signSim.x = clamp(state.signSim.x + step, 0, 1);
    else if (e.key === "ArrowUp") state.signSim.y = clamp(state.signSim.y - step, 0, 1);
    else if (e.key === "ArrowDown") state.signSim.y = clamp(state.signSim.y + step, 0, 1);
    else handled = false;
    if (handled) {
      e.preventDefault();
      syncSignPositionInputs();
      renderSignCanvas();
    }
  });
}

async function handleSignPhotoUpload(file) {
  if (!file) return;
  try {
    const img = await loadImageFile(file);
    state.signSim.bgCanvas = drawToCanvas(img, 900);
    renderSignCanvas();
  } catch (err) {
    console.error(err);
    alert("Could not load that image — try a different file.");
  }
}

function useFacadeForSign() {
  if (!state.images.facade) {
    alert("Upload a façade photo in Storefront Score first, or upload a photo directly here.");
    return;
  }
  state.signSim.bgCanvas = cloneCanvas(state.images.facade.canvas);
  renderSignCanvas();
}

function exportSignAlone() {
  const params = getSignParams();
  const measCanvas = document.createElement("canvas");
  const mctx = measCanvas.getContext("2d");
  const box = measureSign(mctx, params);
  const pad = Math.max(14, params.size * 0.35);
  const w = Math.ceil(box.width + pad * 2);
  const h = Math.ceil(box.height + pad * 2);
  const c = document.createElement("canvas");
  c.width = w;
  c.height = h;
  const ctx = c.getContext("2d");
  drawSignGlyph(ctx, w / 2, h / 2, params, box);
  downloadDataUrl(c.toDataURL("image/png"), "storefront-lens-sign.png");
}

function exportSignPhoto() {
  if (!state.signSim.bgCanvas) {
    alert("Upload a storefront photo first.");
    return;
  }
  const canvas = document.getElementById("canvasSign");
  const exportCanvas = cloneCanvas(canvas);
  if (!state.pro) drawWatermark(exportCanvas.getContext("2d"), exportCanvas.width, exportCanvas.height);
  downloadDataUrl(exportCanvas.toDataURL("image/png"), "storefront-lens-sign-mockup.png");
}

/* ============================================================================
   6. BUDGET BLUEPRINT
   ============================================================================
   Pulls together whatever the user has already produced (Score, Moves, Sign
   Simulator choices) into a single printable brief. Every number here is a
   heuristic estimate for planning conversations, not a quote — the brief
   says so explicitly.
   ============================================================================ */

const MATERIAL_DESCRIPTIONS = {
  flat: "Flat painted or matte-vinyl lettering — economical, clean, strongest in direct daylight.",
  outlined: "Outlined / channel-letter style lettering — can be halo-lit at night, mid-range cost.",
  bevel: "Dimensional faux-bevel / built-out lettering — most premium look, strongest depth and night presence.",
};

function estimateDimensionGuidance() {
  const key = primaryScoreImageKey();
  if (!key) {
    return "Aim for a primary sign spanning roughly 60–70% of the façade width and 15–20% of the façade height, centered over the entrance.";
  }
  const canvas = state.images[key].canvas;
  const aspect = (canvas.width / canvas.height).toFixed(2);
  return `Based on your uploaded photo (approx. ${aspect}:1 width-to-height), aim for a primary sign spanning 60–70% of the façade width and 15–20% of the façade height, centered over the entrance.`;
}

function buildBudgetTiers(palette, signParams) {
  const hex = (i) => (palette[i] ? palette[i] : palette[0] || "#333333");
  return [
    {
      name: "$500 — Quick wins",
      items: [
        [`Exterior touch-up paint in ${hex(0)} on trim/door`, "$60–120 (DIY, paint + supplies)"],
        ["Remove old window decals/flyers, deep-clean glass", "$0–40"],
        ["Weatherproof door mat + one potted planter", "$40–90"],
        ["Battery or plug-in LED puck lights to backlight the existing sign at night", "$30–80"],
        ["Re-adhere or replace loose/faded sign lettering", "$50–150"],
      ],
    },
    {
      name: "$2,000 — Solid upgrade",
      items: [
        [`Professional single-color façade or trim repaint in ${hex(0)}`, "$800–1,400"],
        [
          signParams ? `Printed vinyl banner or panel sign reading "${signParams.text}"` : "New printed vinyl banner or panel sign",
          "$250–600",
        ],
        ["Awning cleaning or minor repair", "$150–400"],
        ["Exterior accent lighting, 2–3 fixtures", "$200–500"],
        [`Redesigned window signage in ${hex(2) || hex(0)}, max 2–3 panels`, "$150–350"],
      ],
    },
    {
      name: "$10,000+ — Full transformation",
      items: [
        [
          signParams && signParams.material === "bevel"
            ? "Custom fabricated dimensional / channel-letter sign, faux-bevel profile"
            : "Custom fabricated sign (channel letters or dimensional panel)",
          "$3,000–8,000",
        ],
        ["Full façade repaint with prep & primer, multi-color scheme", "$2,500–5,000"],
        ["New retractable or fixed awning, color-matched to palette", "$1,800–4,000"],
        ["Entrance hardscape refresh (steps, planters, paving)", "$1,500–4,000"],
        ["Professional exterior lighting design & installation", "$1,200–3,000"],
      ],
    },
  ];
}

function generateBlueprint() {
  const moves = state.decisions
    ? state.decisions.moves
    : generateMoves({ category: "your storefront", brandWords: ["clean", "confident", "welcoming"], frustration: "blends-in" });
  const palette = pickPaletteForDecisions();
  const signParams = state.signSim.bgCanvas ? getSignParams() : null;
  const tiers = buildBudgetTiers(palette, signParams);

  const out = document.getElementById("blueprintOutput");
  out.hidden = false;
  out.innerHTML = `
    <h1>Storefront Budget Blueprint</h1>
    <p>Generated ${escapeHtml(new Date().toLocaleDateString())}${state.score ? ` &middot; Storefront Score: <strong>${state.score.overall}/100</strong>` : ""}</p>

    <h2>Prioritized moves</h2>
    <ol>
      ${moves.map((m) => `<li><strong>${escapeHtml(m.title)}</strong> — ${escapeHtml(m.why(state.decisions ? state.decisions.answers : { category: "your business", brandWords: [] }))}</li>`).join("")}
    </ol>

    <h2>Exact colors</h2>
    <div class="blueprint-swatches">
      ${palette
        .slice(0, 5)
        .map((hex) => `<span class="swatch"><span class="swatch-color" style="background:${hex}"></span>${hex}</span>`)
        .join("")}
    </div>

    <h2>Recommended materials</h2>
    <ul>
      <li>Primary sign: ${escapeHtml(signParams ? MATERIAL_DESCRIPTIONS[signParams.material] : "See Sign Simulator to choose flat, outlined, or faux-bevel lettering.")}</li>
      <li>Trim / accent paint: exterior-grade satin or semi-gloss in ${escapeHtml(palette[0] || "#333333")}</li>
      <li>Entrance: weather-rated matting and low-maintenance planters</li>
    </ul>

    <h2>Rough dimensions &amp; proportions</h2>
    <p>${escapeHtml(estimateDimensionGuidance())}</p>

    <h2>Budget tiers</h2>
    <div class="blueprint-tiers">
      ${tiers
        .map(
          (tier) => `
        <div class="tier-card">
          <h3>${escapeHtml(tier.name)}</h3>
          <table>
            ${tier.items.map(([item, cost]) => `<tr><td>${escapeHtml(item)}</td><td>${escapeHtml(cost)}</td></tr>`).join("")}
          </table>
        </div>`
        )
        .join("")}
    </div>

    <h2>How to brief a local painter / sign maker / contractor</h2>
    <ul class="checklist">
      <li>Bring or send this brief — it already has your exact hex colors, so nobody has to guess.</li>
      <li>Get at least three written quotes before committing to anyone.</li>
      <li>Ask each contractor to confirm material, install method, expected lifespan, and warranty.</li>
      <li>Check whether your municipality or business district requires a sign permit — many do.</li>
      <li>Get a firm start date and completion window in writing.</li>
      <li>For paint: specify the exact sheen (matte / satin / gloss) and confirm it's an exterior-grade product.</li>
      <li>For signage: confirm both daytime AND nighttime visibility — ask to see a lit mockup or a past job at night.</li>
      <li>Budget a 10–15% contingency above your chosen tier for surprises.</li>
    </ul>

    <p class="hint">Estimates are planning ranges based on typical small-storefront projects, not formal quotes.</p>
  `;

  document.getElementById("btnPrintBlueprint").hidden = false;
}

/* ============================================================================
   7. STREET CONTEXT SCANNER
   ============================================================================
   Reuses kMeansLite() across all uploaded neighbor photos pooled together to
   get a single "what's common on this block" palette, then flags any color
   in the user's own palette that sits within a perceptual distance
   threshold of a neighbor color, and suggests a safer alternative — either
   an untaken color already in the user's own palette, or, failing that, a
   hue-shifted variation of the flagged color.
   ============================================================================ */

const STREET_MATCH_THRESHOLD = 42; // weighted RGB distance below this = "already used nearby"

function weightedColorDist(a, b) {
  const dr = a[0] - b[0], dg = a[1] - b[1], db = a[2] - b[2];
  return Math.sqrt(0.3 * dr * dr + 0.59 * dg * dg + 0.11 * db * db);
}

async function handleStreetFileInput(index, file) {
  if (!file) return;
  try {
    const img = await loadImageFile(file);
    state.street.images = state.street.images || [];
    state.street.images[index] = drawToCanvas(img, 480);
  } catch (err) {
    console.error(err);
    alert("Could not load that image — try a different file.");
  }
  updateStreetScanButtonState();
}

function updateStreetScanButtonState() {
  const btn = document.getElementById("btnScanStreet");
  btn.disabled = !(state.street.images || []).some(Boolean);
}

function getUserPaletteForStreet() {
  if (state.score && state.score.palette.length) return state.score.palette.map((c) => ({ hex: c.hex, rgb: c.rgb }));
  const key = primaryScoreImageKey();
  if (key) {
    const pixels = samplePixels(state.images[key].canvas, 6);
    return kMeansLite(pixels, 6, 5)
      .filter((c) => c.pct >= 0.03)
      .map((c) => ({ hex: rgbToHex(...c.rgb), rgb: c.rgb }));
  }
  return [];
}

function scanStreet() {
  const status = document.getElementById("streetStatus");
  const images = (state.street.images || []).filter(Boolean);
  if (images.length === 0) return;
  status.textContent = "Scanning block…";

  let allPixels = [];
  images.forEach((canvas) => { allPixels = allPixels.concat(samplePixels(canvas, 8)); });
  const neighborPalette = kMeansLite(allPixels, 8, 5)
    .filter((c) => c.pct >= 0.02)
    .map((c) => ({ hex: rgbToHex(...c.rgb), rgb: c.rgb, pct: c.pct }));

  const userPalette = getUserPaletteForStreet();
  if (userPalette.length === 0) {
    status.textContent = "Run Storefront Score (or upload a façade photo there) first, so there's a palette to compare against.";
    document.getElementById("streetResults").hidden = true;
    return;
  }

  const flags = userPalette.map((uc) => {
    let minDist = Infinity, closest = null;
    neighborPalette.forEach((nc) => {
      const d = weightedColorDist(uc.rgb, nc.rgb);
      if (d < minDist) { minDist = d; closest = nc; }
    });
    return { color: uc, taken: minDist < STREET_MATCH_THRESHOLD, minDist, closestNeighbor: closest };
  });

  const untaken = flags.filter((f) => !f.taken).map((f) => f.color);
  flags.forEach((f) => {
    if (!f.taken) { f.suggestion = null; return; }
    let best = null, bestScore = -Infinity;
    untaken.forEach((c) => {
      const minD = Math.min(...neighborPalette.map((nc) => weightedColorDist(c.rgb, nc.rgb)));
      if (minD > bestScore) { bestScore = minD; best = c; }
    });
    if (best) {
      f.suggestion = { hex: best.hex, note: "from your own palette" };
    } else {
      const hsl = rgbToHsl(...f.color.rgb);
      const shifted = hslToRgb((hsl[0] + 40) % 360, Math.max(hsl[1], 0.4), clamp(hsl[2], 0.25, 0.75));
      f.suggestion = { hex: rgbToHex(...shifted), note: "hue-shifted variation" };
    }
  });

  state.street.palette = neighborPalette;
  state.street.flags = flags;
  renderStreetResults(neighborPalette, flags);
  status.textContent = `Scanned ${images.length} neighboring photo${images.length > 1 ? "s" : ""}.`;
}

function renderStreetResults(neighborPalette, flags) {
  const out = document.getElementById("streetResults");
  out.hidden = false;
  out.innerHTML = `
    <div>
      <h3>Colors already common on this block</h3>
      <div class="palette-row">
        ${neighborPalette
          .slice(0, 8)
          .map((c) => `<span class="swatch"><span class="swatch-color" style="background:${c.hex}"></span>${c.hex}<br>${Math.round(c.pct * 100)}%</span>`)
          .join("")}
      </div>
    </div>
    <div>
      <h3>Your palette vs. the block</h3>
      <ul class="flag-list">
        ${flags
          .map(
            (f) => `
          <li class="flag-item ${f.taken ? "taken" : "safe"}">
            <span class="swatch-color" style="background:${f.color.hex};width:28px;height:28px;flex-shrink:0"></span>
            <span>${f.color.hex}</span>
            <span class="arrow">${f.taken ? "⚠ already common nearby" : "✓ distinct on this block"}</span>
            ${
              f.taken && f.suggestion
                ? `<span class="arrow">→ try <span class="swatch-color" style="background:${f.suggestion.hex};width:22px;height:22px;display:inline-block;vertical-align:middle;border-radius:4px"></span> ${f.suggestion.hex} (${f.suggestion.note})</span>`
                : ""
            }
          </li>`
          )
          .join("")}
      </ul>
    </div>
  `;
}

/* ============================================================================
   8. NIGHT / SEASONAL RENDERER
   ============================================================================
   Purely deterministic Canvas filters — no generative model involved.
   Each preset combines: a CSS-filter brightness/contrast/saturation pass,
   an "overlay" blended color-temperature tint, a radial vignette, and (for
   evening/night presets) a soft additive glow centered on the sign position
   from the Sign Simulator, if one has been placed on this photo.
   ============================================================================ */

const NIGHT_PRESETS = {
  "dusk-summer": { label: "Dusk, summer", brightness: 0.85, contrast: 1.05, saturate: 1.05, tint: [255, 140, 60, 0.16], vignette: 0.35, glow: 0.5 },
  "7pm-november": { label: "7 PM, November", brightness: 0.55, contrast: 1.1, saturate: 0.9, tint: [40, 60, 110, 0.28], vignette: 0.5, glow: 0.7 },
  "overcast": { label: "Overcast day", brightness: 0.92, contrast: 0.88, saturate: 0.75, tint: [190, 200, 210, 0.12], vignette: 0.15, glow: 0 },
  "bright-noon": { label: "Bright noon", brightness: 1.12, contrast: 1.08, saturate: 1.1, tint: [255, 255, 240, 0.06], vignette: 0.05, glow: 0 },
  "golden-hour": { label: "Golden hour", brightness: 1.0, contrast: 1.05, saturate: 1.15, tint: [255, 170, 80, 0.22], vignette: 0.25, glow: 0.3 },
  "deep-night": { label: "Deep night", brightness: 0.32, contrast: 1.15, saturate: 0.7, tint: [20, 30, 70, 0.4], vignette: 0.65, glow: 0.9 },
};

function renderNightPreview() {
  const src = state.night.sourceCanvas;
  if (!src) return;
  const preset = NIGHT_PRESETS[document.getElementById("nightPreset").value];

  const orig = document.getElementById("canvasNightOriginal");
  orig.width = src.width;
  orig.height = src.height;
  orig.getContext("2d").drawImage(src, 0, 0);

  const sim = document.getElementById("canvasNightSim");
  sim.width = src.width;
  sim.height = src.height;
  const ctx = sim.getContext("2d");

  ctx.filter = `brightness(${preset.brightness}) contrast(${preset.contrast}) saturate(${preset.saturate})`;
  ctx.drawImage(src, 0, 0);
  ctx.filter = "none";

  ctx.save();
  ctx.globalCompositeOperation = "overlay";
  ctx.fillStyle = `rgba(${preset.tint[0]}, ${preset.tint[1]}, ${preset.tint[2]}, ${preset.tint[3]})`;
  ctx.fillRect(0, 0, sim.width, sim.height);
  ctx.restore();

  if (preset.vignette > 0) {
    const grad = ctx.createRadialGradient(
      sim.width / 2, sim.height / 2, Math.min(sim.width, sim.height) * 0.25,
      sim.width / 2, sim.height / 2, Math.max(sim.width, sim.height) * 0.72
    );
    grad.addColorStop(0, "rgba(0,0,0,0)");
    grad.addColorStop(1, `rgba(0,0,0,${preset.vignette})`);
    ctx.fillStyle = grad;
    ctx.fillRect(0, 0, sim.width, sim.height);
  }

  if (preset.glow > 0) {
    const usingSignPosition = state.signSim.bgCanvas && state.signSim.bgCanvas.width === src.width && state.signSim.bgCanvas.height === src.height;
    const gx = usingSignPosition ? state.signSim.x * sim.width : sim.width * 0.5;
    const gy = usingSignPosition ? state.signSim.y * sim.height : sim.height * 0.18;
    const r = Math.max(sim.width, sim.height) * 0.2;
    ctx.save();
    ctx.globalCompositeOperation = "screen";
    const glowGrad = ctx.createRadialGradient(gx, gy, 0, gx, gy, r);
    glowGrad.addColorStop(0, `rgba(255,225,150,${0.55 * preset.glow})`);
    glowGrad.addColorStop(1, "rgba(255,225,150,0)");
    ctx.fillStyle = glowGrad;
    ctx.fillRect(0, 0, sim.width, sim.height);
    ctx.restore();
  }

  if (!state.pro) drawWatermark(ctx, sim.width, sim.height);
}

async function handleNightPhotoUpload(file) {
  if (!file) return;
  try {
    const img = await loadImageFile(file);
    state.night.sourceCanvas = drawToCanvas(img, 900);
    renderNightPreview();
  } catch (err) {
    console.error(err);
    alert("Could not load that image — try a different file.");
  }
}

function useFacadeForNight() {
  if (!state.images.facade) {
    alert("Upload a façade photo in Storefront Score first, or upload a photo directly here.");
    return;
  }
  state.night.sourceCanvas = cloneCanvas(state.images.facade.canvas);
  renderNightPreview();
}

function exportNight() {
  if (!state.night.sourceCanvas) {
    alert("Upload a storefront photo first.");
    return;
  }
  const sim = document.getElementById("canvasNightSim");
  downloadDataUrl(sim.toDataURL("image/png"), "storefront-lens-night.png");
}

/* ============================================================================
   9. INIT / WIRING
   ============================================================================ */

function wireDropzone(dropzoneId, inputId, key) {
  const zone = document.getElementById(dropzoneId);
  const input = document.getElementById(inputId);
  input.addEventListener("change", () => handleScoreFileInput(key, input.files[0]));
  ["dragenter", "dragover"].forEach((evt) =>
    zone.addEventListener(evt, (e) => { e.preventDefault(); zone.classList.add("dragover"); })
  );
  ["dragleave", "drop"].forEach((evt) =>
    zone.addEventListener(evt, (e) => { e.preventDefault(); zone.classList.remove("dragover"); })
  );
  zone.addEventListener("drop", (e) => {
    const file = e.dataTransfer.files && e.dataTransfer.files[0];
    if (file) handleScoreFileInput(key, file);
  });
}

function refreshAllCanvasesForProToggle() {
  if (state.score) renderScoreResults();
  if (state.signSim.bgCanvas) renderSignCanvas();
  if (state.night.sourceCanvas) renderNightPreview();
  document.getElementById("watermarkNote").hidden = state.pro;
}

function initApp() {
  loadStateFromStorage();
  applyTheme(state.theme);
  document.getElementById("proToggle").checked = state.pro;
  document.getElementById("watermarkNote").hidden = state.pro;
  initTabs();

  // ---- Storefront Score ----
  wireDropzone("dropzone-facade", "fileFacade", "facade");
  wireDropzone("dropzone-sign", "fileSign", "sign");
  wireDropzone("dropzone-entrance", "fileEntrance", "entrance");
  document.getElementById("btnAnalyze").addEventListener("click", analyzeStorefront);

  document.getElementById("btnDownloadAnnotated").addEventListener("click", () => {
    if (!state.score) return;
    downloadDataUrl(document.getElementById("canvasHeatmap").toDataURL("image/png"), "storefront-lens-heatmap.png");
  });
  document.getElementById("btnDownloadSummary").addEventListener("click", () => {
    if (!state.score) return;
    downloadText(buildScoreSummaryText(), "storefront-lens-summary.txt");
  });
  document.getElementById("btnShareDataUrl").addEventListener("click", () => {
    if (!state.score) return;
    const dataUrl = document.getElementById("canvasHeatmap").toDataURL("image/png");
    const box = document.getElementById("shareUrlOutput");
    box.hidden = false;
    box.value = dataUrl;
    box.focus();
    box.select();
  });

  // ---- Decision Generator ----
  document.getElementById("decisionForm").addEventListener("submit", handleDecisionFormSubmit);

  // ---- Sign Simulator ----
  document.getElementById("fileSignPhoto").addEventListener("change", (e) => handleSignPhotoUpload(e.target.files[0]));
  document.getElementById("btnUseFacadeForSign").addEventListener("click", useFacadeForSign);
  document.getElementById("signText").addEventListener("input", renderSignCanvas);
  document.getElementById("signFont").addEventListener("change", renderSignCanvas);
  document.getElementById("signColor").addEventListener("input", renderSignCanvas);
  document.getElementById("signMaterial").addEventListener("change", renderSignCanvas);
  document.getElementById("signSize").addEventListener("input", (e) => {
    document.getElementById("signSizeVal").textContent = e.target.value;
    renderSignCanvas();
  });
  document.getElementById("signX").addEventListener("input", (e) => {
    state.signSim.x = clamp(parseInt(e.target.value, 10) / 100, 0, 1);
    document.getElementById("signXVal").textContent = e.target.value;
    renderSignCanvas();
  });
  document.getElementById("signY").addEventListener("input", (e) => {
    state.signSim.y = clamp(parseInt(e.target.value, 10) / 100, 0, 1);
    document.getElementById("signYVal").textContent = e.target.value;
    renderSignCanvas();
  });
  initSignDragging();
  document.getElementById("btnExportSignAlone").addEventListener("click", exportSignAlone);
  document.getElementById("btnExportSignPhoto").addEventListener("click", exportSignPhoto);

  // ---- Budget Blueprint ----
  document.getElementById("btnGenerateBlueprint").addEventListener("click", generateBlueprint);
  document.getElementById("btnPrintBlueprint").addEventListener("click", () => window.print());

  // ---- Street Context Scanner ----
  [1, 2, 3, 4].forEach((n) => {
    document.getElementById(`streetFile${n}`).addEventListener("change", (e) => handleStreetFileInput(n - 1, e.target.files[0]));
  });
  document.getElementById("btnScanStreet").addEventListener("click", scanStreet);

  // ---- Night / Seasonal Renderer ----
  document.getElementById("fileNightPhoto").addEventListener("change", (e) => handleNightPhotoUpload(e.target.files[0]));
  document.getElementById("btnUseFacadeForNight").addEventListener("click", useFacadeForNight);
  document.getElementById("nightPreset").addEventListener("change", renderNightPreview);
  document.getElementById("btnExportNight").addEventListener("click", exportNight);

  // ---- Header / footer ----
  document.getElementById("themeToggle").addEventListener("click", () => {
    applyTheme(state.theme === "dark" ? "light" : "dark");
    saveStateToStorage();
  });
  document.getElementById("proToggle").addEventListener("change", (e) => {
    state.pro = e.target.checked;
    refreshAllCanvasesForProToggle();
    saveStateToStorage();
  });
  document.getElementById("btnResetData").addEventListener("click", () => {
    if (confirm("Clear your saved Storefront Lens session from this browser?")) resetStorage();
  });

  updateAnalyzeButtonState();
  updateStreetScanButtonState();
}

document.addEventListener("DOMContentLoaded", initApp);
