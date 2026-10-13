const canvas = document.getElementById("canvas");
const ctx = canvas.getContext("2d");
let canvasDpr = 1;
const fontFileInput = document.getElementById("fontFileInput");
const fontDropZone = document.getElementById("fontDropZone");
const fontDropLabel = document.getElementById("fontDropLabel");
const fontClearBtn = document.getElementById("fontClearBtn");
const scribbleTextRow = document.getElementById("scribbleTextRow");
const scribbleTextInput = document.getElementById("scribbleTextInput");
const rescribbleBtn = document.getElementById("rescribbleBtn");

let loadedOpentypeFont = null;
let loadedFontLabel = "";

// --- Glyph skeletonization: rasterize a glyph outline, thin it down to its 1px centerline,
// and trace that centerline into polylines. The pen then draws along those polylines using
// the exact same freehand-stroke renderer as hand-drawn strokes, so a dropped font reads as
// "the pen traced this letter's strokes" rather than a hatch-filled silhouette.

function skelIdx(x, y, width) {
  return y * width + x;
}

function skelGet(mask, width, height, x, y) {
  if (x < 0 || y < 0 || x >= width || y >= height) return 0;
  return mask[skelIdx(x, y, width)];
}

function zhangSuenPass(width, height, mask, step) {
  const toRemove = [];

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      if (!skelGet(mask, width, height, x, y)) continue;

      const P2 = skelGet(mask, width, height, x, y - 1);
      const P3 = skelGet(mask, width, height, x + 1, y - 1);
      const P4 = skelGet(mask, width, height, x + 1, y);
      const P5 = skelGet(mask, width, height, x + 1, y + 1);
      const P6 = skelGet(mask, width, height, x, y + 1);
      const P7 = skelGet(mask, width, height, x - 1, y + 1);
      const P8 = skelGet(mask, width, height, x - 1, y);
      const P9 = skelGet(mask, width, height, x - 1, y - 1);

      const neighbors = [P2, P3, P4, P5, P6, P7, P8, P9];
      const B = neighbors.reduce((sum, v) => sum + v, 0);
      if (B < 2 || B > 6) continue;

      let A = 0;
      for (let i = 0; i < 8; i++) {
        if (neighbors[i] === 0 && neighbors[(i + 1) % 8] === 1) A++;
      }
      if (A !== 1) continue;

      if (step === 1) {
        if (P2 * P4 * P6 !== 0) continue;
        if (P4 * P6 * P8 !== 0) continue;
      } else {
        if (P2 * P4 * P8 !== 0) continue;
        if (P2 * P6 * P8 !== 0) continue;
      }

      toRemove.push(skelIdx(x, y, width));
    }
  }

  toRemove.forEach((i) => (mask[i] = 0));
  return toRemove.length > 0;
}

// Zhang-Suen thinning. Mutates `mask` (Uint8Array, 1 = foreground) down to a 1px skeleton.
function zhangSuenThin(width, height, mask) {
  let changed = true;
  while (changed) {
    changed = false;
    changed = zhangSuenPass(width, height, mask, 1) || changed;
    changed = zhangSuenPass(width, height, mask, 2) || changed;
  }
  return mask;
}

// Morphological dilate/erode with a square structuring element, used to smooth pixel-grid
// staircase noise on curved boundaries before thinning (which otherwise reads that noise as
// spurious little branches).
function skelDilate(width, height, mask, radius) {
  const out = new Uint8Array(width * height);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let found = 0;
      for (let dy = -radius; dy <= radius && !found; dy++) {
        for (let dx = -radius; dx <= radius; dx++) {
          if (skelGet(mask, width, height, x + dx, y + dy)) {
            found = 1;
            break;
          }
        }
      }
      out[skelIdx(x, y, width)] = found;
    }
  }
  return out;
}

function skelErode(width, height, mask, radius) {
  const out = new Uint8Array(width * height);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let all = 1;
      for (let dy = -radius; dy <= radius && all; dy++) {
        for (let dx = -radius; dx <= radius; dx++) {
          if (!skelGet(mask, width, height, x + dx, y + dy)) {
            all = 0;
            break;
          }
        }
      }
      out[skelIdx(x, y, width)] = all;
    }
  }
  return out;
}

function morphologyClose(width, height, mask, radius) {
  return skelErode(width, height, skelDilate(width, height, mask, radius), radius);
}

// The topological degree of a skeleton pixel: the number of separate connected runs of
// foreground among its 8 neighbors (1 = endpoint, 2 = mid-strand, 3+ = junction). A raw
// neighbor COUNT over-reports degree at diagonal staircase bends (two neighbors that are
// adjacent to each other read as "extra" branches even though they're one continuous strand),
// so this run-counting version is what endpoint/junction classification uses.
function crossingNumber(mask, width, height, x, y) {
  const P2 = skelGet(mask, width, height, x, y - 1);
  const P3 = skelGet(mask, width, height, x + 1, y - 1);
  const P4 = skelGet(mask, width, height, x + 1, y);
  const P5 = skelGet(mask, width, height, x + 1, y + 1);
  const P6 = skelGet(mask, width, height, x, y + 1);
  const P7 = skelGet(mask, width, height, x - 1, y + 1);
  const P8 = skelGet(mask, width, height, x - 1, y);
  const P9 = skelGet(mask, width, height, x - 1, y - 1);
  const seq = [P2, P3, P4, P5, P6, P7, P8, P9];

  let A = 0;
  for (let i = 0; i < 8; i++) {
    if (seq[i] === 0 && seq[(i + 1) % 8] === 1) A++;
  }
  return A;
}

// Orthogonal neighbors always count. A diagonal neighbor only counts if it isn't already
// reachable through a shared orthogonal "bridge" pixel — otherwise a single topological
// connection produces two raw graph edges (one direct diagonal, one via the bridge), and
// whichever edge a walk leaves unconsumed spawns a spurious extra micro-branch.
function dedupedNeighbors(mask, width, height, x, y) {
  const N = skelGet(mask, width, height, x, y - 1);
  const S = skelGet(mask, width, height, x, y + 1);
  const E = skelGet(mask, width, height, x + 1, y);
  const W = skelGet(mask, width, height, x - 1, y);
  const NE = skelGet(mask, width, height, x + 1, y - 1);
  const NW = skelGet(mask, width, height, x - 1, y - 1);
  const SE = skelGet(mask, width, height, x + 1, y + 1);
  const SW = skelGet(mask, width, height, x - 1, y + 1);

  const list = [];
  if (N) list.push([x, y - 1]);
  if (S) list.push([x, y + 1]);
  if (E) list.push([x + 1, y]);
  if (W) list.push([x - 1, y]);
  if (NE && !(N && E)) list.push([x + 1, y - 1]);
  if (NW && !(N && W)) list.push([x - 1, y - 1]);
  if (SE && !(S && E)) list.push([x + 1, y + 1]);
  if (SW && !(S && W)) list.push([x - 1, y + 1]);
  return list;
}

// Removes short endpoint branches (spurs shorter than minLen pixels) from a thinned skeleton.
// Serif nubs and thinning artifacts typically show up as these short dead-end spurs.
function pruneSpurs(width, height, mask, minLen, rounds = 3) {
  for (let round = 0; round < rounds; round++) {
    let prunedAny = false;

    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        if (!skelGet(mask, width, height, x, y)) continue;
        if (crossingNumber(mask, width, height, x, y) !== 1) continue;

        // Walk from this endpoint until a junction/another endpoint, or minLen steps.
        const chain = [[x, y]];
        let prevX = x;
        let prevY = y;
        let curX = x;
        let curY = y;
        let steps = 0;
        let stoppedAtJunction = false;

        while (steps < minLen) {
          if (crossingNumber(mask, width, height, curX, curY) >= 3) {
            stoppedAtJunction = true;
            break;
          }

          const candidates = dedupedNeighbors(mask, width, height, curX, curY).filter(
            ([nx, ny]) => !(nx === prevX && ny === prevY),
          );
          if (candidates.length === 0) break; // isolated short segment, both ends are endpoints

          prevX = curX;
          prevY = curY;
          [curX, curY] = candidates[0];
          chain.push([curX, curY]);
          steps++;
        }

        if (stoppedAtJunction && chain.length <= minLen) {
          // Remove the spur but keep the junction pixel itself.
          chain.slice(0, -1).forEach(([px, py]) => (mask[skelIdx(px, py, width)] = 0));
          prunedAny = true;
        }
      }
    }

    if (!prunedAny) break;
  }
}

// Decomposes the skeleton pixel graph into ordered polylines (open chains and closed loops).
function traceSkeleton(width, height, mask) {
  const visitedEdges = new Set();
  const edgeKey = (ax, ay, bx, by) => {
    const a = skelIdx(ax, ay, width);
    const b = skelIdx(bx, by, width);
    return a < b ? `${a}_${b}` : `${b}_${a}`;
  };

  const neighborsOf = (x, y) => dedupedNeighbors(mask, width, height, x, y);

  const points = [];
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      if (skelGet(mask, width, height, x, y)) points.push([x, y]);
    }
  }

  const unvisitedEdgeExists = (x, y) =>
    neighborsOf(x, y).some(([nx, ny]) => !visitedEdges.has(edgeKey(x, y, nx, ny)));

  const walkFrom = (startX, startY, firstX, firstY) => {
    const path = [[startX, startY]];
    let prevX = startX;
    let prevY = startY;
    let curX = firstX;
    let curY = firstY;

    visitedEdges.add(edgeKey(prevX, prevY, curX, curY));
    path.push([curX, curY]);

    while (true) {
      // A pass-through pixel has crossing number 2 regardless of how many raw 8-neighbors it
      // has (redundant diagonal neighbors can inflate the raw count at staircase bends); only
      // a true endpoint (1) or junction (3+) should end the branch.
      if (crossingNumber(mask, width, height, curX, curY) !== 2) break;

      const unvisitedNeighbors = neighborsOf(curX, curY).filter(
        ([nx, ny]) => !(nx === prevX && ny === prevY) && !visitedEdges.has(edgeKey(curX, curY, nx, ny)),
      );
      if (unvisitedNeighbors.length === 0) break;

      const [nx, ny] = unvisitedNeighbors[0];
      visitedEdges.add(edgeKey(curX, curY, nx, ny));
      path.push([nx, ny]);
      prevX = curX;
      prevY = curY;
      curX = nx;
      curY = ny;
    }

    return path;
  };

  const polylines = [];

  // Pass 1: start from endpoints (degree 1) so open chains read naturally end-to-end.
  for (const [x, y] of points) {
    if (crossingNumber(mask, width, height, x, y) !== 1) continue;
    if (!unvisitedEdgeExists(x, y)) continue;
    const [nx, ny] = neighborsOf(x, y).find(([a, b]) => !visitedEdges.has(edgeKey(x, y, a, b)));
    polylines.push(walkFrom(x, y, nx, ny));
  }

  // Pass 2: anything left (closed loops, junction-to-junction edges) walked from wherever an
  // unvisited edge remains.
  for (const [x, y] of points) {
    while (unvisitedEdgeExists(x, y)) {
      const [nx, ny] = neighborsOf(x, y).find(([a, b]) => !visitedEdges.has(edgeKey(x, y, a, b)));
      polylines.push(walkFrom(x, y, nx, ny));
    }
  }

  return polylines.map((chain) => chain.map(([x, y]) => ({ x, y })));
}

function perpendicularDistance(point, a, b) {
  const dx = b.x - a.x;
  const dy = b.y - a.y;
  const lenSq = dx * dx + dy * dy;
  if (lenSq === 0) return Math.hypot(point.x - a.x, point.y - a.y);
  const t = ((point.x - a.x) * dx + (point.y - a.y) * dy) / lenSq;
  const projX = a.x + t * dx;
  const projY = a.y + t * dy;
  return Math.hypot(point.x - projX, point.y - projY);
}

function douglasPeucker(points, epsilon) {
  if (points.length < 3) return points.slice();

  let maxDist = 0;
  let index = 0;
  const first = points[0];
  const last = points[points.length - 1];

  for (let i = 1; i < points.length - 1; i++) {
    const d = perpendicularDistance(points[i], first, last);
    if (d > maxDist) {
      maxDist = d;
      index = i;
    }
  }

  if (maxDist > epsilon) {
    const left = douglasPeucker(points.slice(0, index + 1), epsilon);
    const right = douglasPeucker(points.slice(index), epsilon);
    return left.slice(0, -1).concat(right);
  }

  return [first, last];
}

function chaikinSmooth(points, iterations) {
  let pts = points;
  for (let iter = 0; iter < iterations; iter++) {
    if (pts.length < 3) break;
    const next = [pts[0]];
    for (let i = 0; i < pts.length - 1; i++) {
      const p0 = pts[i];
      const p1 = pts[i + 1];
      next.push({ x: p0.x * 0.75 + p1.x * 0.25, y: p0.y * 0.75 + p1.y * 0.25 });
      next.push({ x: p0.x * 0.25 + p1.x * 0.75, y: p0.y * 0.25 + p1.y * 0.75 });
    }
    next.push(pts[pts.length - 1]);
    pts = next;
  }
  return pts;
}

function polylineLength(points) {
  let len = 0;
  for (let i = 1; i < points.length; i++) {
    len += Math.hypot(points[i].x - points[i - 1].x, points[i].y - points[i - 1].y);
  }
  return len;
}

function pointsClose(a, b, tolerance) {
  return Math.hypot(a.x - b.x, a.y - b.y) <= tolerance;
}

// Welds short junction-to-junction bridges into whichever touching neighbor polyline is
// longest, instead of just dropping them — pruneSpurs only trims dead-end spurs (one end at a
// true endpoint), so a short bridge between two junctions survives tracing untouched otherwise,
// and rendering it alone (too short for the oscillation to complete a real swing) reads as a
// jarring flat sliver next to its fully-feathered neighbors. Not a full topological fix (a true
// 3-way branch point with two short arms can only absorb one of them into the through-path —
// there's no way to represent a fork as a single linear point sequence), but it resolves the
// common case of a single short connector between two longer pieces.
function mergeShortPolylines(polylines, minLength, tolerance = 1.5) {
  const list = polylines.map((p) => p.slice());

  let mergedSomething = true;
  while (mergedSomething) {
    mergedSomething = false;

    for (let i = 0; i < list.length; i++) {
      if (polylineLength(list[i]) >= minLength) continue;

      const a = list[i][0];
      const b = list[i][list[i].length - 1];

      let bestJ = -1;
      let bestLen = -1;
      let bestOrientation = null;

      for (let j = 0; j < list.length; j++) {
        if (j === i) continue;
        const candidate = list[j];
        const p0 = candidate[0];
        const p1 = candidate[candidate.length - 1];
        const len = polylineLength(candidate);

        let orientation = null;
        if (pointsClose(b, p0, tolerance)) orientation = "b-to-p0";
        else if (pointsClose(b, p1, tolerance)) orientation = "b-to-p1";
        else if (pointsClose(a, p0, tolerance)) orientation = "a-to-p0";
        else if (pointsClose(a, p1, tolerance)) orientation = "a-to-p1";

        if (orientation && len > bestLen) {
          bestLen = len;
          bestJ = j;
          bestOrientation = orientation;
        }
      }

      if (bestJ === -1) continue;

      const short = list[i];
      const target = list[bestJ];
      let merged;
      if (bestOrientation === "b-to-p0") {
        merged = short.concat(target.slice(1));
      } else if (bestOrientation === "b-to-p1") {
        merged = target.concat(short.slice(0, short.length - 1).reverse());
      } else if (bestOrientation === "a-to-p0") {
        merged = short.slice().reverse().concat(target.slice(1));
      } else {
        merged = target.concat(short.slice(1));
      }

      list[bestJ] = merged;
      list.splice(i, 1);
      mergedSomething = true;
      break;
    }
  }

  return list;
}

// Rasterizes a glyph path, skeletonizes it, and returns one freehand-style stroke per
// skeleton branch — each stroke plays through the exact same oscillating-pen renderer used
// for hand-drawn strokes, so the letter reads as pen-traced rather than hatch-filled.
function createFontScribbleStrokes(text, font, settings) {
  if (!text) return [];

  const trialSize = 300;
  const trialWidth = font.getAdvanceWidth(text, trialSize);
  if (!trialWidth || !isFinite(trialWidth)) return [];

  const trialAscent = (font.ascender / font.unitsPerEm) * trialSize;
  const trialDescent = (font.descender / font.unitsPerEm) * trialSize;
  const trialHeight = trialAscent - trialDescent;

  // Size and center against the currently visible region of the infinite canvas (not the raw
  // canvas element), so a dropped font lands wherever the user is currently looking.
  const visibleWidth = canvas.clientWidth / viewScale;
  const visibleHeight = canvas.clientHeight / viewScale;
  const visibleCenterX = (canvas.clientWidth / 2 - viewOffsetX) / viewScale;
  const visibleCenterY = (canvas.clientHeight / 2 - viewOffsetY) / viewScale;

  const targetWidth = visibleWidth * 0.74;
  const targetHeight = visibleHeight * 0.56;
  const scale = Math.min(targetWidth / trialWidth, targetHeight / trialHeight, 1.6);
  const fontSize = Math.max(24, trialSize * scale);

  const width = font.getAdvanceWidth(text, fontSize);
  const ascent = (font.ascender / font.unitsPerEm) * fontSize;
  const descent = (font.descender / font.unitsPerEm) * fontSize;

  const x = visibleCenterX - width / 2;
  const y = visibleCenterY + (ascent + descent) / 2;

  const path = font.getPath(text, x, y, fontSize);
  const bbox = path.getBoundingBox();
  if (!isFinite(bbox.x1) || !isFinite(bbox.y1)) return [];

  const pad = 6;
  const offsetX = bbox.x1 - pad;
  const offsetY = bbox.y1 - pad;
  const rasterWidth = Math.ceil(bbox.x2 - bbox.x1) + pad * 2;
  const rasterHeight = Math.ceil(bbox.y2 - bbox.y1) + pad * 2;
  if (rasterWidth <= 0 || rasterHeight <= 0) return [];

  const rasterCanvas = document.createElement("canvas");
  rasterCanvas.width = rasterWidth;
  rasterCanvas.height = rasterHeight;
  const rasterCtx = rasterCanvas.getContext("2d");
  rasterCtx.translate(-offsetX, -offsetY);
  rasterCtx.fillStyle = "#000000";
  rasterCtx.fill(new Path2D(path.toPathData(3)));

  const imageData = rasterCtx.getImageData(0, 0, rasterWidth, rasterHeight).data;
  let mask = new Uint8Array(rasterWidth * rasterHeight);
  for (let i = 0; i < mask.length; i++) {
    mask[i] = imageData[i * 4 + 3] > 127 ? 1 : 0;
  }

  mask = morphologyClose(rasterWidth, rasterHeight, mask, 1);
  zhangSuenThin(rasterWidth, rasterHeight, mask);
  const pruneLen = Math.max(6, fontSize * 0.05);
  pruneSpurs(rasterWidth, rasterHeight, mask, pruneLen);

  const rawPolylines = traceSkeleton(rasterWidth, rasterHeight, mask);
  const strokesOut = [];
  // Junction-to-junction bridges are too short to be dead-end "spurs" (pruneSpurs only trims
  // those), so a few short crumbs typically survive tracing anyway. They're too short for the
  // oscillation to complete even one real swing, so they render as flat jarring slivers next to
  // the fully-feathered strokes around them. Weld them into whichever touching neighbor is
  // longest instead of dropping them outright, so the letter reads as continuous strokes rather
  // than gaining a gap where the bridge used to be.
  const minStrokeLength = Math.max(16, fontSize * 0.06);
  const mergedPolylines = mergeShortPolylines(rawPolylines, minStrokeLength);
  // Post-merge, only truly isolated crumbs (no touching neighbor to weld into) remain short —
  // keep this filter small so genuine tiny features (the dot on "i"/"j") survive.
  const minSurvivingLength = Math.max(4, fontSize * 0.015);

  mergedPolylines.forEach((rawPoints) => {
    if (rawPoints.length < 3) return;

    const simplified = douglasPeucker(rawPoints, 1.2);
    if (polylineLength(simplified) < minSurvivingLength) return;

    const smoothed = chaikinSmooth(simplified, 2);
    const mapped = smoothed.map((p) => ({ x: p.x + offsetX, y: p.y + offsetY }));

    const points = [];
    for (let i = 1; i < mapped.length; i++) {
      points.push({ x1: mapped[i - 1].x, y1: mapped[i - 1].y, x2: mapped[i].x, y2: mapped[i].y });
    }
    if (points.length === 0) return;

    strokesOut.push({ type: "freehand", points, settings: { ...settings } });
  });

  return strokesOut;
}

function scribbleLoadedFont() {
  if (!loadedOpentypeFont) return;

  const text = (scribbleTextInput?.value || "Scribble").trim() || "Scribble";
  const settings = currentPenSettings();

  const newStrokes = createFontScribbleStrokes(text, loadedOpentypeFont, settings);
  if (newStrokes.length === 0) return;

  const batchId = ++strokeBatchCounter;
  newStrokes.forEach((stroke) => (stroke.batchId = batchId));

  strokes.push(...newStrokes);
  redoStack = [];
  redrawCanvas();
}

async function loadFontFile(file) {
  if (!file) return;

  const isFontFile = /\.(ttf|otf|woff|woff2)$/i.test(file.name);
  if (!isFontFile) {
    alert("Please drop a valid font file (.ttf, .otf, .woff, .woff2).");
    return;
  }

  const fontLabel = file.name.replace(/\.[^/.]+$/, "") || "CustomFont";

  try {
    const buffer = await file.arrayBuffer();
    loadedOpentypeFont = opentype.parse(buffer);
  } catch (error) {
    console.error("Font parse failed:", error);
    loadedOpentypeFont = null;
    alert(
      "This font couldn't be read as outlines. Font collections (.ttc) and .woff2 aren't supported yet — please try a single .ttf, .otf, or .woff file.",
    );
    return;
  }

  loadedFontLabel = fontLabel;
  if (fontDropLabel) fontDropLabel.textContent = fontLabel;
  if (scribbleTextRow) scribbleTextRow.hidden = false;

  scribbleLoadedFont();
}

function clearLoadedFont() {
  loadedOpentypeFont = null;
  loadedFontLabel = "";
  if (fontDropLabel) fontDropLabel.textContent = "Drop font file";
  if (scribbleTextRow) scribbleTextRow.hidden = true;
  if (fontFileInput) fontFileInput.value = "";
}

if (fontDropZone && fontFileInput) {
  fontDropZone.addEventListener("click", () => fontFileInput.click());
  fontFileInput.addEventListener("change", async (event) => {
    const file = event.target.files[0];
    await loadFontFile(file);
    fontFileInput.value = "";
  });

  fontClearBtn?.addEventListener("click", (event) => {
    event.stopPropagation();
    clearLoadedFont();
  });

  rescribbleBtn?.addEventListener("click", () => scribbleLoadedFont());
  scribbleTextInput?.addEventListener("keydown", (event) => {
    if (event.key === "Enter") {
      event.preventDefault();
      scribbleLoadedFont();
    }
  });
  scribbleTextInput?.addEventListener("click", (event) => event.stopPropagation());

  ["dragenter", "dragover"].forEach((eventName) => {
    fontDropZone.addEventListener(eventName, (event) => {
      event.preventDefault();
      fontDropZone.classList.add("dragging");
    });
  });

  ["dragleave", "drop"].forEach((eventName) => {
    fontDropZone.addEventListener(eventName, (event) => {
      event.preventDefault();
      fontDropZone.classList.remove("dragging");
    });
  });

  fontDropZone.addEventListener("drop", async (event) => {
    const file = event.dataTransfer?.files?.[0];
    await loadFontFile(file);
  });
}

// ============================================================================
// Pen settings state
// ============================================================================

let isDrawing = false;
let lastX = 0;
let lastY = 0;
let totalDistance = 0;

let lineWidth = 1;
let armLength = 40;
let angleRange = 60;
let speed = 0.5;
let baseAngle = 45;
let strokeStyle = "solid"; // "solid" | "dashed" | "dotted"
let widthProfile = 0; // 0 (uniform) .. 1 (full taper to a point by the stroke's end)
let drawMode = "arc"; // "zig" | "arc" | "solid" — how the oscillation path itself is rendered
// Independent boolean, not part of the Zig/Arc/Solid group: only affects Solid's broad-nib edge
// direction (the default is the correct calligraphy orientation — thin where travel runs along
// the nib edge, thick across it — Invert swaps to the edge-along-baseAngle orientation instead).
let invertNib = false;

// Canvas paper/ink color defaults follow the effective dark/light mode — black paper with
// white ink in dark mode, white paper with black ink in light mode (matches the app chrome,
// which follows the same mode via CSS). "Effective" mode is the explicit Light/Dark override
// if the user picked one in the Mode section, otherwise the OS/browser preference.
const prefersDarkQuery = window.matchMedia("(prefers-color-scheme: dark)");

let themeOverride = null; // null = follow system; "light" | "dark" once the user picks a Mode button

function effectiveDarkMode() {
  return themeOverride ? themeOverride === "dark" : prefersDarkQuery.matches;
}

// The Stroke panel's picker edits either the ink (foreground) or the paper (background) — each
// keeps its own HSVA so switching the target doesn't clobber whichever color isn't showing.
let colorTarget = "foreground"; // "foreground" | "background"
const foregroundState = { hue: 0, saturation: 0, value: effectiveDarkMode() ? 1 : 0, alpha: 1 };
const backgroundState = { hue: 0, saturation: 0, value: effectiveDarkMode() ? 0 : 1, alpha: 1 };

function activeColorState() {
  return colorTarget === "background" ? backgroundState : foregroundState;
}

function rgbaFromState(state) {
  const [r, g, b] = hsvToRgb(state.hue, state.saturation, state.value);
  return `rgba(${r}, ${g}, ${b}, ${state.alpha})`;
}

let currentColor = effectiveDarkMode() ? "rgba(255, 255, 255, 1)" : "rgba(0, 0, 0, 1)";
let backgroundColor = effectiveDarkMode() ? "rgba(0, 0, 0, 1)" : "rgba(255, 255, 255, 1)";

// Resets ink/paper to the default black/white pair for whichever mode is now effective — this
// intentionally overwrites a manually-picked ink/paper color, the same way it already did before
// Foreground/Background became separately editable, since toggling Mode is choosing a whole
// canvas preset, not just a UI-chrome skin. Updates currentColor/backgroundColor directly (not
// just via updateColorFromHsva, which only writes the color for whichever target is active) so
// both flip together regardless of which one the picker happens to be showing.
function applyEffectiveThemeToCanvasColors() {
  const dark = effectiveDarkMode();
  foregroundState.hue = 0;
  foregroundState.saturation = 0;
  foregroundState.value = dark ? 1 : 0;
  foregroundState.alpha = 1;
  backgroundState.hue = 0;
  backgroundState.saturation = 0;
  backgroundState.value = dark ? 0 : 1;
  backgroundState.alpha = 1;
  currentColor = rgbaFromState(foregroundState);
  backgroundColor = rgbaFromState(backgroundState);
  updateColorFromHsva();
  redrawCanvas();
}

prefersDarkQuery.addEventListener("change", () => {
  if (themeOverride !== null) return; // an explicit Mode toggle outranks the OS preference
  applyEffectiveThemeToCanvasColors();
});

// The angle dial labels a pick by how far it leans from horizontal, but the pen's own oscillation
// math measures baseAngle from the complementary axis — so "30°" was rendering the shape "60°"
// should, and vice versa (0°/90° and 30°/60° swap; 45°/-45° are their own mirror). Reflecting once
// here, when a stroke's settings are captured, fixes the mismatch without touching how the dial
// itself displays or picks angles.
function servoBaseAngle(angle) {
  return angle >= 0 ? 90 - angle : -90 - angle;
}

function currentPenSettings() {
  return {
    lineWidth,
    armLength,
    angleRange,
    speed,
    baseAngle: servoBaseAngle(baseAngle),
    style: strokeStyle,
    widthProfile,
    color: currentColor,
    drawMode,
    invertNib,
  };
}

// Arm-pivot offset per pen angle. Not pure trig — hand-tuned to feel right, so only extend
// this table by eye rather than regenerating it from a formula.
const angleOffsets = {
  90: { x: 0, y: -60 },
  60: { x: -30, y: -52 },
  45: { x: -30, y: -50 },
  30: { x: -52, y: -30 },
  0: { x: -60, y: 0 },
  "-30": { x: -52, y: 30 },
  "-45": { x: -25, y: 50 },
  "-60": { x: -30, y: 52 },
};
const knownAngleOffsetKeys = Object.keys(angleOffsets)
  .map(Number)
  .sort((a, b) => a - b);

// Typing a custom angle (e.g. 56°) won't hit one of the 8 hand-tuned entries above, so this
// linearly interpolates between the two nearest known angles instead of jumping to {0,0} —
// matches exactly at the 8 anchor points and blends smoothly in between.
function getAngleOffset(angle) {
  const keys = knownAngleOffsetKeys;
  if (angle <= keys[0]) return angleOffsets[keys[0]];
  if (angle >= keys[keys.length - 1]) return angleOffsets[keys[keys.length - 1]];

  for (let i = 0; i < keys.length - 1; i++) {
    const a0 = keys[i];
    const a1 = keys[i + 1];
    if (angle >= a0 && angle <= a1) {
      const t = (angle - a0) / (a1 - a0);
      const o0 = angleOffsets[a0];
      const o1 = angleOffsets[a1];
      return { x: o0.x + (o1.x - o0.x) * t, y: o0.y + (o1.y - o0.y) * t };
    }
  }
  return { x: 0, y: 0 };
}

// The 8 selectable pen angle magnitudes, in the exact left-to-right order the fan picker
// displays them: paired by magnitude on either side of the 90° spine (nested by steepness),
// with the unpaired 0° hanging off the right end.
const anglePickerMagnitudes = [-30, -45, -60, 90, 60, 45, 30, 0];

// ============================================================================
// Multi-canvas tabs. Each tab owns its own strokes/redo stack; `strokes` and `redoStack`
// below are always aliases of the active tab's arrays, kept in sync on every switch.
// ============================================================================

function makeTab(id) {
  return { id, name: `TAB ${id}`, strokes: [], redoStack: [], viewOffsetX: 0, viewOffsetY: 0, viewScale: 1 };
}

let tabs = [makeTab(1)];
let activeTabId = 1;
let nextTabId = 2;
let editingTabId = null;
let strokeBatchCounter = 0;

let strokes = tabs[0].strokes;
let redoStack = tabs[0].redoStack;
// Infinite-canvas pan/zoom state — per tab, so switching tabs restores where you left off.
let viewOffsetX = tabs[0].viewOffsetX;
let viewOffsetY = tabs[0].viewOffsetY;
let viewScale = tabs[0].viewScale;

function getActiveTab() {
  return tabs.find((t) => t.id === activeTabId);
}

function switchToTab(id) {
  if (id === activeTabId) return;
  const outgoing = getActiveTab();
  if (outgoing) {
    outgoing.strokes = strokes;
    outgoing.redoStack = redoStack;
    outgoing.viewOffsetX = viewOffsetX;
    outgoing.viewOffsetY = viewOffsetY;
    outgoing.viewScale = viewScale;
  }

  const incoming = tabs.find((t) => t.id === id);
  if (!incoming) return;

  activeTabId = id;
  strokes = incoming.strokes;
  redoStack = incoming.redoStack;
  viewOffsetX = incoming.viewOffsetX;
  viewOffsetY = incoming.viewOffsetY;
  viewScale = incoming.viewScale;
  redrawCanvas();
  renderTabBar();
}

function addTab() {
  const id = nextTabId++;
  tabs.push(makeTab(id));
  switchToTab(id);
}

function deleteTab(id) {
  if (tabs.length <= 1) return;
  const index = tabs.findIndex((t) => t.id === id);
  if (index === -1) return;

  const wasActive = id === activeTabId;
  tabs.splice(index, 1);

  if (wasActive) {
    const next = tabs[Math.max(0, index - 1)];
    activeTabId = next.id;
    strokes = next.strokes;
    redoStack = next.redoStack;
    viewOffsetX = next.viewOffsetX;
    viewOffsetY = next.viewOffsetY;
    viewScale = next.viewScale;
    redrawCanvas();
  }
  renderTabBar();
}

function commitTabRename(id, rawValue) {
  const tab = tabs.find((t) => t.id === id);
  const trimmed = rawValue.trim();
  if (tab && trimmed) tab.name = trimmed;
  editingTabId = null;
  renderTabBar();
}

function renderTabBar() {
  const tabBar = document.getElementById("tabBar");
  if (!tabBar) return;
  tabBar.innerHTML = "";

  tabs.forEach((tab) => {
    const btn = document.createElement("button");
    btn.className = "tab-btn" + (tab.id === activeTabId ? " active" : "");
    btn.type = "button";

    if (tab.id === editingTabId) {
      const input = document.createElement("input");
      input.type = "text";
      input.className = "tab-name-input";
      input.value = tab.name;
      input.maxLength = 30;
      // Escape removes this input from the DOM (via renderTabBar), which fires a native
      // blur — without this guard, that blur would immediately re-commit the very text
      // Escape was just trying to discard.
      let resolved = false;
      input.addEventListener("click", (event) => event.stopPropagation());
      input.addEventListener("keydown", (event) => {
        if (event.key === "Enter") {
          event.preventDefault();
          resolved = true;
          commitTabRename(tab.id, input.value);
        } else if (event.key === "Escape") {
          event.preventDefault();
          resolved = true;
          editingTabId = null;
          renderTabBar();
        }
      });
      input.addEventListener("blur", () => {
        if (resolved) return;
        resolved = true;
        commitTabRename(tab.id, input.value);
      });
      btn.appendChild(input);
      tabBar.appendChild(btn);
      input.focus();
      input.select();
      return;
    }

    const name = document.createElement("span");
    name.className = "tab-name";
    name.textContent = tab.name;
    btn.appendChild(name);

    if (tabs.length > 1) {
      const closeBtn = document.createElement("button");
      closeBtn.className = "tab-close";
      closeBtn.type = "button";
      closeBtn.setAttribute("aria-label", `Close ${tab.name}`);
      closeBtn.innerHTML = `<img src="icon/cancel.svg" alt="" />`;
      closeBtn.addEventListener("click", (event) => {
        event.stopPropagation();
        deleteTab(tab.id);
      });
      btn.appendChild(closeBtn);
    }

    btn.addEventListener("click", () => switchToTab(tab.id));
    btn.addEventListener("dblclick", (event) => {
      event.stopPropagation();
      editingTabId = tab.id;
      renderTabBar();
    });
    tabBar.appendChild(btn);
  });

  const addBtn = document.createElement("button");
  addBtn.className = "tab-add-btn";
  addBtn.type = "button";
  addBtn.setAttribute("aria-label", "Add tab");
  addBtn.textContent = "+";
  addBtn.addEventListener("click", addTab);
  tabBar.appendChild(addBtn);
}

renderTabBar();

// ============================================================================
// Live settings preview (small canvas in the Pen section). Declared before the color picker
// section below, since selecting a color triggers a preview repaint immediately.
// ============================================================================

const previewCanvas = document.getElementById("previewCanvas");
const previewCtx = previewCanvas?.getContext("2d");

function verticesToStrokePoints(vertices) {
  const points = [];
  for (let i = 1; i < vertices.length; i++) {
    points.push({ x1: vertices[i - 1].x, y1: vertices[i - 1].y, x2: vertices[i].x, y2: vertices[i].y });
  }
  return points;
}

// Mirrors drawStrokeToContext's pen-tip geometry without actually drawing, so the caller can
// find out where a stroke really ends up (arm offset included) before committing it to canvas.
function computeStrokePenBounds(stroke) {
  const settings = stroke.settings;
  let minX = Infinity;
  let maxX = -Infinity;
  let minY = Infinity;
  let maxY = -Infinity;

  function include(x, y) {
    if (x < minX) minX = x;
    if (x > maxX) maxX = x;
    if (y < minY) minY = y;
    if (y > maxY) maxY = y;
  }

  if (settings.drawMode === "solid") {
    const { top, bottom } = buildNibEnvelope(stroke);
    top.forEach((p) => include(p.x, p.y));
    bottom.forEach((p) => include(p.x, p.y));
    return { minX, maxX, minY, maxY };
  }

  const offset = getAngleOffset(settings.baseAngle);
  let tempDistance = 0;

  stroke.points.forEach((point) => {
    const built = buildOscillationSamples(point.x1, point.y1, point.x2, point.y2, tempDistance, offset, settings);
    if (!built) return;
    built.samples.forEach(({ penX, penY }) => include(penX, penY));
    tempDistance += built.distance;
  });

  return { minX, maxX, minY, maxY };
}

// A straight stroke and a curved one side by side reads much better than a single horizontal
// line — it actually shows how the pen handles a corner-free line versus a continuous curve.
function renderPreview() {
  if (!previewCtx) return;
  const width = previewCanvas.clientWidth;
  const height = previewCanvas.clientHeight;
  // Fill with the real canvas's current paper color (not just clear to transparent) so the
  // preview always accurately shows ink-on-paper contrast, light or dark mode alike.
  previewCtx.fillStyle = backgroundColor;
  previewCtx.fillRect(0, 0, width, height);

  const settings = currentPenSettings();
  const marginY = height * 0.14;

  const lineX = width * 0.24;
  const verticalStroke = {
    settings,
    points: verticesToStrokePoints([
      { x: lineX, y: marginY },
      { x: lineX, y: height - marginY },
    ]),
  };

  const circleCx = width * 0.64;
  const circleCy = height / 2;
  const radius = Math.min(height - marginY * 2, width * 0.32) / 2;
  const circleSegments = 32;
  const circleVertices = [];
  for (let i = 0; i <= circleSegments; i++) {
    const angle = (i / circleSegments) * Math.PI * 2 - Math.PI / 2;
    circleVertices.push({
      x: circleCx + Math.cos(angle) * radius,
      y: circleCy + Math.sin(angle) * radius,
    });
  }
  const circleStroke = { settings, points: verticesToStrokePoints(circleVertices) };

  // The pen's per-angle arm offset (getAngleOffset) shifts the whole rendered shape by a
  // different amount at every angle — recentering on the actual rendered bounds (rather than
  // the nominal coordinates above) keeps the preview centered no matter which angle is picked.
  const lineBounds = computeStrokePenBounds(verticalStroke);
  const circleBounds = computeStrokePenBounds(circleStroke);
  const combined = {
    minX: Math.min(lineBounds.minX, circleBounds.minX),
    maxX: Math.max(lineBounds.maxX, circleBounds.maxX),
    minY: Math.min(lineBounds.minY, circleBounds.minY),
    maxY: Math.max(lineBounds.maxY, circleBounds.maxY),
  };
  const deltaX = width / 2 - (combined.minX + combined.maxX) / 2;
  const deltaY = height / 2 - (combined.minY + combined.maxY) / 2;

  previewCtx.save();
  previewCtx.translate(deltaX, deltaY);
  drawStrokeToContext(previewCtx, verticalStroke);
  drawStrokeToContext(previewCtx, circleStroke);
  previewCtx.restore();
}

// ============================================================================
// Color picker (HSV square + hue slider + alpha slider + hex/opacity inputs)
// ============================================================================

function hsvToRgb(h, s, v) {
  h = ((h % 360) + 360) % 360;
  s = Math.max(0, Math.min(1, s));
  v = Math.max(0, Math.min(1, v));
  const c = v * s;
  const x = c * (1 - Math.abs(((h / 60) % 2) - 1));
  const m = v - c;
  let r, g, b;
  if (h < 60) [r, g, b] = [c, x, 0];
  else if (h < 120) [r, g, b] = [x, c, 0];
  else if (h < 180) [r, g, b] = [0, c, x];
  else if (h < 240) [r, g, b] = [0, x, c];
  else if (h < 300) [r, g, b] = [x, 0, c];
  else [r, g, b] = [c, 0, x];
  return [Math.round((r + m) * 255), Math.round((g + m) * 255), Math.round((b + m) * 255)];
}

function rgbToHsv(r, g, b) {
  r /= 255;
  g /= 255;
  b /= 255;
  const max = Math.max(r, g, b);
  const min = Math.min(r, g, b);
  const d = max - min;
  let h = 0;
  if (d !== 0) {
    if (max === r) h = (((g - b) / d) % 6) * 60;
    else if (max === g) h = ((b - r) / d + 2) * 60;
    else h = ((r - g) / d + 4) * 60;
    if (h < 0) h += 360;
  }
  const s = max === 0 ? 0 : d / max;
  return [h, s, max];
}

function rgbToHex(r, g, b) {
  return [r, g, b].map((v) => v.toString(16).padStart(2, "0")).join("");
}

function hexToRgb(hex) {
  const clean = hex.replace(/[^0-9a-f]/gi, "").padEnd(6, "0").slice(0, 6);
  const n = parseInt(clean, 16);
  return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
}

const svPicker = document.getElementById("svPicker");
const svThumb = document.getElementById("svThumb");
const hueSlider = document.getElementById("hueSlider");
const hueThumb = document.getElementById("hueThumb");
const alphaSlider = document.getElementById("alphaSlider");
const alphaThumb = document.getElementById("alphaThumb");
const alphaSliderFill = document.getElementById("alphaSliderFill");
const hexInput = document.getElementById("hexInput");
const opacityInput = document.getElementById("opacityInput");
const rgbInputs = document.getElementById("rgbInputs");
const redInput = document.getElementById("redInput");
const greenInput = document.getElementById("greenInput");
const blueInput = document.getElementById("blueInput");
const colorFormatBtn = document.getElementById("colorFormatBtn");
const colorFormatLabel = document.getElementById("colorFormatLabel");
const colorFormatMenu = document.getElementById("colorFormatMenu");

let colorFormat = "hex";

const colorTargetForegroundBtn = document.getElementById("colorTargetForegroundBtn");
const colorTargetBackgroundBtn = document.getElementById("colorTargetBackgroundBtn");

function setColorTarget(target) {
  colorTarget = target;
  colorTargetForegroundBtn?.classList.toggle("active", target === "foreground");
  colorTargetBackgroundBtn?.classList.toggle("active", target === "background");
  updateColorFromHsva();
}

colorTargetForegroundBtn?.addEventListener("click", () => setColorTarget("foreground"));
colorTargetBackgroundBtn?.addEventListener("click", () => setColorTarget("background"));

function updateColorFromHsva() {
  const state = activeColorState();
  const [r, g, b] = hsvToRgb(state.hue, state.saturation, state.value);

  if (colorTarget === "background") {
    backgroundColor = `rgba(${r}, ${g}, ${b}, ${state.alpha})`;
  } else {
    currentColor = `rgba(${r}, ${g}, ${b}, ${state.alpha})`;
  }

  if (hexInput) hexInput.value = rgbToHex(r, g, b).toUpperCase();
  if (redInput) redInput.value = r;
  if (greenInput) greenInput.value = g;
  if (blueInput) blueInput.value = b;
  if (opacityInput) opacityInput.value = `${Math.round(state.alpha * 100)}%`;

  if (svPicker) svPicker.style.backgroundColor = `hsl(${state.hue}, 100%, 50%)`;
  if (svThumb) {
    svThumb.style.left = `${state.saturation * 100}%`;
    svThumb.style.top = `${(1 - state.value) * 100}%`;
  }
  if (hueThumb) hueThumb.style.left = `${(state.hue / 360) * 100}%`;
  if (alphaThumb) alphaThumb.style.left = `${state.alpha * 100}%`;
  if (alphaSliderFill) alphaSliderFill.style.color = `rgb(${r}, ${g}, ${b})`;

  renderPreview();
  // Ink only affects strokes drawn from here on (already-baked into past strokes), but paper is
  // the canvas's own fill — repaint immediately so picking a background color reads live.
  if (colorTarget === "background") redrawCanvas();
}

function dragWithin(element, onMove) {
  const handle = (event) => {
    const rect = element.getBoundingClientRect();
    const x = Math.max(0, Math.min(1, (event.clientX - rect.left) / rect.width));
    const y = Math.max(0, Math.min(1, (event.clientY - rect.top) / rect.height));
    onMove(x, y);
  };

  element.addEventListener("pointerdown", (event) => {
    element.setPointerCapture(event.pointerId);
    handle(event);
    const onPointerMove = (moveEvent) => handle(moveEvent);
    const onPointerUp = () => {
      element.removeEventListener("pointermove", onPointerMove);
      element.removeEventListener("pointerup", onPointerUp);
    };
    element.addEventListener("pointermove", onPointerMove);
    element.addEventListener("pointerup", onPointerUp);
  });
}

if (svPicker) {
  dragWithin(svPicker, (x, y) => {
    const state = activeColorState();
    state.saturation = x;
    state.value = 1 - y;
    updateColorFromHsva();
  });
}

if (hueSlider) {
  dragWithin(hueSlider, (x) => {
    activeColorState().hue = x * 360;
    updateColorFromHsva();
  });
}

if (alphaSlider) {
  dragWithin(alphaSlider, (x) => {
    activeColorState().alpha = x;
    updateColorFromHsva();
  });
}

hexInput?.addEventListener("change", () => {
  const [r, g, b] = hexToRgb(hexInput.value);
  const state = activeColorState();
  [state.hue, state.saturation, state.value] = rgbToHsv(r, g, b);
  updateColorFromHsva();
});

opacityInput?.addEventListener("change", () => {
  const parsed = parseFloat(opacityInput.value);
  const state = activeColorState();
  state.alpha = isFinite(parsed) ? Math.max(0, Math.min(100, parsed)) / 100 : state.alpha;
  updateColorFromHsva();
});

function clamp255(value) {
  const parsed = parseInt(value, 10);
  return isFinite(parsed) ? Math.max(0, Math.min(255, parsed)) : 0;
}

[redInput, greenInput, blueInput].forEach((input) => {
  input?.addEventListener("change", () => {
    const r = clamp255(redInput?.value);
    const g = clamp255(greenInput?.value);
    const b = clamp255(blueInput?.value);
    const state = activeColorState();
    [state.hue, state.saturation, state.value] = rgbToHsv(r, g, b);
    updateColorFromHsva();
  });
});

colorFormatBtn?.addEventListener("click", (event) => {
  event.stopPropagation();
  if (colorFormatMenu) colorFormatMenu.hidden = !colorFormatMenu.hidden;
});

document.querySelectorAll(".color-format-option").forEach((btn) => {
  btn.addEventListener("click", () => {
    colorFormat = btn.dataset.format;
    if (colorFormatLabel) colorFormatLabel.textContent = colorFormat.toUpperCase();
    if (hexInput) hexInput.hidden = colorFormat !== "hex";
    if (rgbInputs) rgbInputs.hidden = colorFormat !== "rgb";
    if (colorFormatMenu) colorFormatMenu.hidden = true;
  });
});

document.addEventListener("click", (event) => {
  if (
    colorFormatMenu &&
    !colorFormatMenu.hidden &&
    !colorFormatMenu.contains(event.target) &&
    event.target !== colorFormatBtn
  ) {
    colorFormatMenu.hidden = true;
  }
});

updateColorFromHsva();

// ============================================================================
// Weight / Style / Width Profile
// ============================================================================

const weightInput = document.getElementById("weightInput");
const styleSelect = document.getElementById("styleSelect");
const widthProfileInput = document.getElementById("widthProfileInput");
const widthProfilePreview = document.getElementById("widthProfilePreview");

weightInput?.addEventListener("input", () => {
  const parsed = parseInt(weightInput.value, 10);
  lineWidth = isFinite(parsed) ? Math.max(1, Math.min(5, parsed)) : lineWidth;
  renderPreview();
});

styleSelect?.addEventListener("change", () => {
  strokeStyle = styleSelect.value;
  renderPreview();
});

function updateWidthProfilePreview() {
  if (!widthProfilePreview) return;
  const polygon = widthProfilePreview.querySelector("polygon");
  if (!polygon) return;
  const t = widthProfile; // 0..1
  const startHalf = 7;
  const endHalf = Math.max(0.5, 7 * (1 - t));
  polygon.setAttribute(
    "points",
    `0,${10 - startHalf} 100,${10 - endHalf} 100,${10 + endHalf} 0,${10 + startHalf}`,
  );
}

widthProfileInput?.addEventListener("input", () => {
  widthProfile = parseInt(widthProfileInput.value, 10) / 100;
  updateWidthProfilePreview();
  renderPreview();
});
updateWidthProfilePreview();

// ============================================================================
// Draw mode (Zig / Arc / Solid), Pen presets (Stem Thickness), Density stepper, Angle select
// ============================================================================

// Zig/Arc/Solid are mutually exclusive (data-mode identifies them); Invert is a separate
// boolean that unions onto whichever of those is active, so it's wired independently below
// rather than joining this radio group.
document.querySelectorAll(".draw-mode-btn[data-mode]").forEach((btn) => {
  btn.addEventListener("click", () => {
    document.querySelectorAll(".draw-mode-btn[data-mode]").forEach((b) => b.classList.remove("active"));
    btn.classList.add("active");
    drawMode = btn.dataset.mode;
    renderPreview();
  });
});

document.getElementById("invertNibBtn")?.addEventListener("click", (event) => {
  invertNib = !invertNib;
  event.currentTarget.classList.toggle("active", invertNib);
  renderPreview();
});

document.querySelectorAll(".pen-preset-btn").forEach((btn) => {
  btn.addEventListener("click", () => {
    document.querySelectorAll(".pen-preset-btn").forEach((b) => b.classList.remove("active"));
    btn.classList.add("active");
    armLength = parseInt(btn.dataset.arm, 10);
    renderPreview();
  });
});

const densityInput = document.getElementById("densityInput");
const densityUpBtn = document.getElementById("densityUpBtn");
const densityDownBtn = document.getElementById("densityDownBtn");

// Manual entry (e.g. typing "0.53") keeps whatever precision the user typed instead of snapping
// to the nearest 0.1 step — only clamped to the valid range and rounded to 2 decimals to avoid
// floating-point noise. The up/down buttons still nudge by a plain 0.1 from the current value.
function setDensity(next) {
  speed = Math.round(Math.max(0.1, Math.min(1, next)) * 100) / 100;
  if (densityInput) densityInput.value = speed;
  renderPreview();
}

densityInput?.addEventListener("change", () => {
  const parsed = parseFloat(densityInput.value);
  if (isFinite(parsed)) setDensity(parsed);
});
// step="any" so typed decimals aren't rejected, which also means the browser won't apply its
// own arrow-key increment — drive Up/Down by the same 0.1 nudge as the stepper buttons.
densityInput?.addEventListener("keydown", (e) => {
  if (e.key === "ArrowUp") {
    e.preventDefault();
    setDensity(speed + 0.1);
  } else if (e.key === "ArrowDown") {
    e.preventDefault();
    setDensity(speed - 0.1);
  }
});
densityUpBtn?.addEventListener("click", () => setDensity(speed + 0.1));
densityDownBtn?.addEventListener("click", () => setDensity(speed - 0.1));

// Fan-dial angle picker: a protractor-style widget — pivot at bottom-center, a baseline
// across the box, rays fanning upward. The rays are laid out at evenly-spaced DISPLAY angles
// (not the pen's true canvas-space direction, which doesn't form a tidy symmetric fan) purely
// so the widget reads clearly; clicking a ray still sets the real pen angle it's paired with.
const SVG_NS = "http://www.w3.org/2000/svg";
const anglePickerSvg = document.getElementById("anglePickerSvg");
const angleInput = document.getElementById("angleInput");

// `fromInput` skips writing back into angleInput so typing "56" then blurring doesn't fight
// the user's cursor — the input already shows what they typed.
function setBaseAngle(angle, fromInput) {
  baseAngle = angle;
  document.querySelectorAll(".angle-ray-group").forEach((g) => {
    g.classList.toggle("active", parseInt(g.dataset.angle, 10) === angle);
  });
  if (!fromInput && angleInput) angleInput.value = angle;
  renderPreview();
}

angleInput?.addEventListener("change", () => {
  const parsed = parseFloat(angleInput.value);
  if (isFinite(parsed)) setBaseAngle(Math.max(-180, Math.min(180, parsed)), true);
});

if (anglePickerSvg) {
  const pivotX = 120;
  const pivotY = 118;
  const rayLength = 95;
  const wedgeRadius = rayLength + 8;

  // Evenly spaced "up-left to up-right" display angles (standard math convention, 90° = up).
  // 90° sits at index 3 of 8 and 0° at the last index, so these particular endpoints are the
  // ones that land both exactly where they should (90° dead vertical, 0° flat on the
  // baseline) while keeping every step the same size — don't "round" them without re-deriving.
  const displaySpan = { start: 157.5, end: 0 };
  const displayAngles = anglePickerMagnitudes.map((_, i) => {
    const t = i / (anglePickerMagnitudes.length - 1);
    return displaySpan.start + (displaySpan.end - displaySpan.start) * t;
  });

  const toPoint = (displayDeg, radius) => {
    const rad = (displayDeg * Math.PI) / 180;
    return { x: pivotX + Math.cos(rad) * radius, y: pivotY - Math.sin(rad) * radius };
  };

  const baseline = document.createElementNS(SVG_NS, "line");
  baseline.setAttribute("class", "angle-baseline");
  baseline.setAttribute("x1", 8);
  baseline.setAttribute("y1", pivotY);
  baseline.setAttribute("x2", 232);
  baseline.setAttribute("y2", pivotY);
  anglePickerSvg.appendChild(baseline);

  // Thick hit-lines running the full pivot-to-tip length would overlap each other near the
  // pivot (adjacent rays converge there), so whichever ray was drawn last would silently steal
  // clicks meant for its neighbors. Non-overlapping pie-slice wedges — split at the display-
  // angle midpoint between each ray and its neighbors — give every ray its own click zone.
  const bounds = displayAngles.map((deg, i) => {
    const prev = i > 0 ? displayAngles[i - 1] : deg - (displayAngles[i + 1] - deg);
    const next =
      i < displayAngles.length - 1 ? displayAngles[i + 1] : deg + (deg - displayAngles[i - 1]);
    return { lower: (deg + prev) / 2, upper: (deg + next) / 2 };
  });

  anglePickerMagnitudes.forEach((angle, i) => {
    const displayDeg = displayAngles[i];
    const tip = toPoint(displayDeg, rayLength);

    const group = document.createElementNS(SVG_NS, "g");
    group.setAttribute("class", "angle-ray-group");
    group.dataset.angle = angle;

    const { lower, upper } = bounds[i];
    const lowerPoint = toPoint(lower, wedgeRadius);
    const upperPoint = toPoint(upper, wedgeRadius);
    const wedge = document.createElementNS(SVG_NS, "path");
    wedge.setAttribute("class", "angle-ray-hit");
    wedge.setAttribute(
      "d",
      `M ${pivotX} ${pivotY} L ${lowerPoint.x} ${lowerPoint.y} ` +
        `A ${wedgeRadius} ${wedgeRadius} 0 0 0 ${upperPoint.x} ${upperPoint.y} Z`,
    );

    const visibleLine = document.createElementNS(SVG_NS, "line");
    visibleLine.setAttribute("class", "angle-ray");
    visibleLine.setAttribute("x1", pivotX);
    visibleLine.setAttribute("y1", pivotY);
    visibleLine.setAttribute("x2", tip.x);
    visibleLine.setAttribute("y2", tip.y);

    const labelPoint = toPoint(displayDeg, rayLength + 13);
    const label = document.createElementNS(SVG_NS, "text");
    label.setAttribute("class", "angle-ray-label");
    label.setAttribute("x", labelPoint.x);
    label.setAttribute("y", labelPoint.y);
    const dx = labelPoint.x - pivotX;
    label.setAttribute("text-anchor", dx > 8 ? "start" : dx < -8 ? "end" : "middle");
    label.textContent = `${angle}`;

    group.appendChild(wedge);
    group.appendChild(visibleLine);
    group.appendChild(label);
    group.addEventListener("click", () => setBaseAngle(angle));
    anglePickerSvg.appendChild(group);
  });

  const pivotDot = document.createElementNS(SVG_NS, "circle");
  pivotDot.setAttribute("cx", pivotX);
  pivotDot.setAttribute("cy", pivotY);
  pivotDot.setAttribute("r", 2.6);
  pivotDot.setAttribute("class", "angle-pivot");
  anglePickerSvg.appendChild(pivotDot);

  setBaseAngle(baseAngle);
}

// ============================================================================
// Sidebar footer: info modal, collapse
// ============================================================================

const infoBtn = document.getElementById("infoBtn");
const infoModalOverlay = document.getElementById("infoModalOverlay");
const infoModalCloseBtn = document.getElementById("infoModalCloseBtn");

function openInfoModal() {
  if (infoModalOverlay) infoModalOverlay.hidden = false;
}
function closeInfoModal() {
  if (infoModalOverlay) infoModalOverlay.hidden = true;
}

infoBtn?.addEventListener("click", openInfoModal);
infoModalCloseBtn?.addEventListener("click", closeInfoModal);
infoModalOverlay?.addEventListener("click", (event) => {
  if (event.target === infoModalOverlay) closeInfoModal();
});
document.addEventListener("keydown", (event) => {
  if (event.key === "Escape" && infoModalOverlay && !infoModalOverlay.hidden) closeInfoModal();
});

const sidebar = document.getElementById("sidebar");
const sidebarReopenBtn = document.getElementById("sidebarReopenBtn");
document.getElementById("collapseBtn")?.addEventListener("click", () => {
  sidebar?.classList.add("collapsed");
  if (sidebarReopenBtn) sidebarReopenBtn.hidden = false;
});
sidebarReopenBtn?.addEventListener("click", () => {
  sidebar?.classList.remove("collapsed");
  sidebarReopenBtn.hidden = true;
});

// Collapsing/reopening the sidebar resizes the canvas element (it's a flex sibling that grows
// to fill the freed space), but the canvas's pixel buffer was sized once at load — without
// this, the old buffer gets stretched to fill the new box, which is exactly the pixelation bug
// fixed earlier, just re-triggered by a layout change instead of a big monitor. Re-running the
// same DPI-aware setup keeps it crisp; redrawing afterward is safe because strokes live in
// world coordinates, so existing artwork lands back in the same place, not stretched.
const canvasResizeObserver = new ResizeObserver(() => {
  canvasDpr = setupCanvasResolution(canvas, ctx);
  redrawCanvas();
});
canvasResizeObserver.observe(canvas);

// ============================================================================
// Canvas clear (the floating × over the canvas area)
// ============================================================================

function clearCanvas() {
  strokes = [];
  redoStack = [];
  redrawCanvas();
}

document.getElementById("canvasClearBtn")?.addEventListener("click", clearCanvas);

// Keyboard shortcuts — Ctrl on Windows/Linux, Cmd (metaKey) on Mac.
document.addEventListener("keydown", (e) => {
  const mod = e.ctrlKey || e.metaKey;
  if (!mod) return;

  const key = e.key.toLowerCase();

  if (key === "z" && e.shiftKey) {
    e.preventDefault();
    redo();
  } else if (key === "z") {
    e.preventDefault();
    undo();
  } else if (key === "y") {
    e.preventDefault();
    redo();
  } else if (key === "d") {
    e.preventDefault();
    clearCanvas();
  } else if (key === "s") {
    e.preventDefault();
    saveSVG();
  } else if (key === "0") {
    e.preventDefault();
    viewOffsetX = 0;
    viewOffsetY = 0;
    viewScale = 1;
    redrawCanvas();
  }
});

// Hold Space to pan the infinite canvas by dragging, like Figma/Photoshop — but not while
// typing (e.g. renaming a tab), since Space needs to type a literal space there.
let spacePanning = false;
let isPanning = false;
let panStartClientX = 0;
let panStartClientY = 0;
let panStartOffsetX = 0;
let panStartOffsetY = 0;

document.addEventListener("keydown", (e) => {
  if (e.code !== "Space" || spacePanning) return;
  const tag = document.activeElement?.tagName;
  if (tag === "INPUT" || tag === "TEXTAREA" || tag === "SELECT") return;
  spacePanning = true;
  canvas.style.cursor = "grab";
  e.preventDefault();
});

document.addEventListener("keyup", (e) => {
  if (e.code !== "Space") return;
  spacePanning = false;
  if (!isPanning) canvas.style.cursor = "crosshair";
});

// Two-finger trackpad scroll (or a plain mouse wheel) pans; pinch-zoom or Ctrl/Cmd+scroll
// zooms toward the cursor, keeping the point under it fixed on screen.
canvas.addEventListener(
  "wheel",
  (e) => {
    e.preventDefault();
    const rect = canvas.getBoundingClientRect();
    const scaleX = canvas.clientWidth / rect.width;
    const scaleY = canvas.clientHeight / rect.height;
    const cursorX = (e.clientX - rect.left) * scaleX;
    const cursorY = (e.clientY - rect.top) * scaleY;

    if (e.ctrlKey || e.metaKey) {
      const zoomFactor = Math.exp(-e.deltaY * 0.01);
      const newScale = Math.max(0.1, Math.min(8, viewScale * zoomFactor));
      const worldX = (cursorX - viewOffsetX) / viewScale;
      const worldY = (cursorY - viewOffsetY) / viewScale;
      viewOffsetX = cursorX - worldX * newScale;
      viewOffsetY = cursorY - worldY * newScale;
      viewScale = newScale;
    } else {
      viewOffsetX -= e.deltaX;
      viewOffsetY -= e.deltaY;
    }
    redrawCanvas();
  },
  { passive: false },
);

// ============================================================================
// Drawing engine
// ============================================================================

// Fills the background in screen space (identity view) — strokes live in world space and get
// panned/zoomed, but the background always covers the full visible canvas regardless of view.
function setCanvasBackground() {
  ctx.setTransform(canvasDpr, 0, 0, canvasDpr, 0, 0);
  ctx.fillStyle = backgroundColor;
  ctx.fillRect(0, 0, canvas.clientWidth, canvas.clientHeight);
}

// Switches the context into world space (view pan/zoom on top of the fixed dpr scale) so
// subsequent draw calls can use plain world coordinates.
function applyViewTransform() {
  ctx.setTransform(
    canvasDpr * viewScale,
    0,
    0,
    canvasDpr * viewScale,
    canvasDpr * viewOffsetX,
    canvasDpr * viewOffsetY,
  );
}

function computeStrokeLength(points) {
  return points.reduce((sum, p) => sum + Math.hypot(p.x2 - p.x1, p.y2 - p.y1), 0);
}

function computeTaperedWidth(baseWidth, profile, t) {
  const factor = 1 - Math.max(0, Math.min(1, profile)) * Math.max(0, Math.min(1, t));
  return Math.max(baseWidth * factor, 0.4);
}

function dashPatternFor(style, width) {
  if (style === "dashed") return [width * 4, width * 3];
  if (style === "dotted") return [width * 0.6, width * 2.2];
  return [];
}

// Finely samples the servo-arm oscillation between two skeleton points — one sample per ~1px of
// travel — carrying both the pen-tip position (the visible mark, "arc" strokes this directly)
// and the spine/center position it swung out from (used to close a "solid" lobe). Zig and Solid
// both reprocess this exact same sample list, just differently, so all three draw modes trace
// identical peaks: only how those peaks get connected/filled differs.
function buildOscillationSamples(x1, y1, x2, y2, tempDistance, offset, settings) {
  const dx = x2 - x1;
  const dy = y2 - y1;
  const distance = Math.sqrt(dx * dx + dy * dy);
  if (distance < 0.5) return null;

  const segments = Math.max(Math.ceil(distance / 1), 1);
  const angleRangeRad = (settings.angleRange * Math.PI) / 180;
  const baseAngleRad = (settings.baseAngle * Math.PI) / 180;

  const samples = [];
  for (let i = 0; i <= segments; i++) {
    const t = i / segments;
    const centerX = x1 + dx * t + offset.x;
    const centerY = y1 + dy * t + offset.y;
    const currentDist = tempDistance + distance * t;
    const oscillation = Math.sin(currentDist * settings.speed);
    const servoAngle = baseAngleRad + (oscillation * angleRangeRad) / 2;
    const penX = centerX + Math.cos(servoAngle) * settings.armLength;
    const penY = centerY + Math.sin(servoAngle) * settings.armLength;
    samples.push({ centerX, centerY, penX, penY, oscillation, dist: currentDist });
  }
  return { samples, distance };
}

// Concatenates buildOscillationSamples across every point-pair of a whole stroke into one
// continuous sample stream (dropping each pair's duplicate leading sample, since it's the same
// point as the previous pair's trailing one). Zig needs this — extracting peaks/zero-crossings
// per point-pair independently forces a spurious extra vertex at every pair boundary (wherever
// a hand-drawn stroke's recorded mouse segments happen to fall mid-swing), breaking one clean
// zigzag into visibly jagged little kinks. Sampling the whole stroke first avoids that entirely.
function buildAllOscillationSamples(stroke) {
  const settings = stroke.settings;
  const offset = getAngleOffset(settings.baseAngle);
  let tempDistance = 0;
  const allSamples = [];

  stroke.points.forEach((point) => {
    const built = buildOscillationSamples(point.x1, point.y1, point.x2, point.y2, tempDistance, offset, settings);
    if (!built) return;
    const samples = allSamples.length > 0 ? built.samples.slice(1) : built.samples;
    allSamples.push(...samples);
    tempDistance += built.distance;
  });

  return allSamples;
}

// Zig keeps only the direction-change (peak/trough) samples — not the zero-crossings in
// between — so connecting consecutive peaks directly with a straight line traces one bold
// zigzag stroke per swing, the way the Zig icon draws it. Must run on the whole stroke's
// samples (buildAllOscillationSamples), not one point-pair at a time: extracting per point-pair
// forces the first/last sample of every pair to survive as a "kept" endpoint even when it isn't
// a real peak, since each pair is treated as its own isolated run — that's what previously
// looked like extra kinks sitting in the middle of an otherwise straight swing.
function extractZigPoints(samples) {
  const keep = [samples[0]];
  for (let i = 1; i < samples.length - 1; i++) {
    const prev = samples[i - 1].oscillation;
    const curr = samples[i].oscillation;
    const next = samples[i + 1].oscillation;
    const isExtremum = (curr - prev) * (next - curr) < 0;
    if (isExtremum) keep.push(samples[i]);
  }
  keep.push(samples[samples.length - 1]);
  return keep;
}

// Renders one point-pair's oscillation onto a canvas context for Arc, or a cheap live-preview
// approximation for Zig (see buildAllOscillationSamples for why the committed Zig render needs
// the whole stroke instead). Returns the travel distance covered, so the caller can keep
// tempDistance in sync with buildOscillationSamples' phase across the whole stroke.
function drawOscillationSegment(targetCtx, x1, y1, x2, y2, tempDistance, offset, settings, width) {
  const built = buildOscillationSamples(x1, y1, x2, y2, tempDistance, offset, settings);
  if (!built) return 0;
  const { samples, distance } = built;

  const points = settings.drawMode === "zig" ? extractZigPoints(samples) : samples;
  targetCtx.strokeStyle = settings.color;
  targetCtx.lineWidth = width;
  targetCtx.lineCap = settings.drawMode === "zig" ? "butt" : "round";
  targetCtx.lineJoin = settings.drawMode === "zig" ? "miter" : "round";
  targetCtx.setLineDash(dashPatternFor(settings.style, width));
  targetCtx.beginPath();
  points.forEach((p, i) => {
    if (i === 0) targetCtx.moveTo(p.penX, p.penY);
    else targetCtx.lineTo(p.penX, p.penY);
  });
  targetCtx.stroke();
  targetCtx.setLineDash([]);

  return distance;
}

// Draws the committed Zig stroke as one continuous zigzag across the whole path (see
// buildAllOscillationSamples), with per-segment taper/dash so Weight/Width Profile/Style still
// apply the way they do for Arc.
function drawZigStroke(targetCtx, stroke) {
  const settings = stroke.settings;
  const totalLength = computeStrokeLength(stroke.points);
  const zigPoints = extractZigPoints(buildAllOscillationSamples(stroke));
  if (zigPoints.length < 2) return;

  targetCtx.strokeStyle = settings.color;
  targetCtx.lineCap = "butt";
  targetCtx.lineJoin = "miter";

  for (let i = 1; i < zigPoints.length; i++) {
    const a = zigPoints[i - 1];
    const b = zigPoints[i];
    const tOverall = totalLength > 0 ? a.dist / totalLength : 0;
    const width = computeTaperedWidth(settings.lineWidth, settings.widthProfile ?? 0, tOverall);
    targetCtx.lineWidth = width;
    targetCtx.setLineDash(dashPatternFor(settings.style, width));
    targetCtx.beginPath();
    targetCtx.moveTo(a.penX, a.penY);
    targetCtx.lineTo(b.penX, b.penY);
    targetCtx.stroke();
  }
  targetCtx.setLineDash([]);
}

// Broad (chisel) nib model for Solid: the nib is a fixed-length segment held at a CONSTANT angle
// relative to the baseline, regardless of the stroke's direction of travel — unlike Zig/Arc's
// oscillating arm. The stroke outline is the Minkowski sum of the skeleton path with that fixed
// segment: offsetting every skeleton vertex by the same nib-angle vector traces the envelope a
// broad-nib pen leaves, naturally thin where travel runs parallel to the nib edge (a "hair
// stroke") and thick where it runs across it — exactly how a real calligraphy nib behaves.
// The nib's physical EDGE runs perpendicular to the held pen angle (a chisel tip: you tilt the
// pen to baseAngle, and the flat edge doing the marking sits 90° across that) — that's the
// default, correct calligraphy orientation. Invert skips the +90° and uses the edge running
// along baseAngle itself instead, which is backwards for real calligraphy but was the original
// (still occasionally useful) attempt, kept around as an explicit opt-in.
function nibEdgeAngleRad(settings) {
  const baseRad = (settings.baseAngle * Math.PI) / 180;
  return settings.invertNib ? baseRad : baseRad + Math.PI / 2;
}

function buildNibEnvelope(stroke) {
  const settings = stroke.settings;
  const totalLength = computeStrokeLength(stroke.points);
  const nibAngleRad = nibEdgeAngleRad(settings);
  const dirX = Math.cos(nibAngleRad);
  const dirY = Math.sin(nibAngleRad);

  const vertices = [];
  let cumulative = 0;
  stroke.points.forEach((p, i) => {
    if (i === 0) vertices.push({ x: p.x1, y: p.y1, dist: 0 });
    cumulative += Math.hypot(p.x2 - p.x1, p.y2 - p.y1);
    vertices.push({ x: p.x2, y: p.y2, dist: cumulative });
  });

  const top = [];
  const bottom = [];
  vertices.forEach((v) => {
    const tOverall = totalLength > 0 ? v.dist / totalLength : 0;
    const halfWidth = computeTaperedWidth(settings.armLength, settings.widthProfile ?? 0, tOverall) / 2;
    top.push({ x: v.x + dirX * halfWidth, y: v.y + dirY * halfWidth });
    bottom.push({ x: v.x - dirX * halfWidth, y: v.y - dirY * halfWidth });
  });

  return { top, bottom };
}

// Draws the broad-nib stroke as a chain of small per-segment quads rather than one big
// offset-envelope polygon. A single whole-stroke envelope self-intersects badly on tight curves
// (e.g. a small "o") once the nib's half-width nears the path's local curvature radius — the
// fixed offset direction pushes the inner edge past the path's own center and out the other
// side, producing a self-crossing polygon that the fill rule renders as a broken, striped mess
// (effectively a boolean subtract where it should just be solid ink) instead of a clean shape.
// Per-segment quads sidestep this entirely: each quad spans only one short hop of the path, so
// it stays simple regardless of how tightly the whole stroke curves, and consecutive quads share
// their offset corner points exactly (the offset is a constant vector, not perpendicular-to-
// tangent), so they tile together into one continuous mark with no seams or gaps — opaque
// overlapping fills just union visually, the way real overlapping ink does.
function drawBroadNibStroke(targetCtx, stroke) {
  const settings = stroke.settings;

  if (settings.invertNib) {
    // Invert: unchanged — the original whole-stroke envelope polygon.
    const { top, bottom } = buildNibEnvelope(stroke);
    if (top.length < 2) return;
    targetCtx.fillStyle = settings.color;
    targetCtx.beginPath();
    targetCtx.moveTo(top[0].x, top[0].y);
    for (let i = 1; i < top.length; i++) targetCtx.lineTo(top[i].x, top[i].y);
    for (let i = bottom.length - 1; i >= 0; i--) targetCtx.lineTo(bottom[i].x, bottom[i].y);
    targetCtx.closePath();
    targetCtx.fill();
    return;
  }

  // Solid (default): one whole-stroke envelope self-intersects badly on tight curves (e.g. a
  // small "o") once the nib's half-width nears the path's local curvature radius — the fixed
  // offset pushes the inner edge past the path's own center and out the other side, and the
  // resulting winding pattern renders as a broken, striped mess instead of a clean shape.
  // Per-segment quads, each filled separately, stay simple regardless of curvature — matching
  // buildSvgPathsForStroke's one-<path>-per-segment export. Each quad is stretched a hair past
  // its own segment (SEAM_OVERLAP) at both ends so it overlaps its neighbor instead of exactly
  // touching — two independently anti-aliased edges meeting at precisely the same line still
  // leave a faint seam (neither one is fully opaque right at the boundary), which shows up as
  // the thin white cracks between adjacent letters' strokes; the overlap paints over that gap.
  const SEAM_OVERLAP = 0.75;
  const totalLength = computeStrokeLength(stroke.points);
  const nibAngleRad = nibEdgeAngleRad(settings);
  const dirX = Math.cos(nibAngleRad);
  const dirY = Math.sin(nibAngleRad);

  targetCtx.fillStyle = settings.color;

  let tempDistance = 0;
  stroke.points.forEach((p) => {
    const segLength = Math.hypot(p.x2 - p.x1, p.y2 - p.y1);
    const tOverall = totalLength > 0 ? tempDistance / totalLength : 0;
    const halfWidth = computeTaperedWidth(settings.armLength, settings.widthProfile ?? 0, tOverall) / 2;
    const ox = dirX * halfWidth;
    const oy = dirY * halfWidth;

    const ux = segLength > 0 ? (p.x2 - p.x1) / segLength : 0;
    const uy = segLength > 0 ? (p.y2 - p.y1) / segLength : 0;
    const x1 = p.x1 - ux * SEAM_OVERLAP;
    const y1 = p.y1 - uy * SEAM_OVERLAP;
    const x2 = p.x2 + ux * SEAM_OVERLAP;
    const y2 = p.y2 + uy * SEAM_OVERLAP;

    targetCtx.beginPath();
    targetCtx.moveTo(x1 + ox, y1 + oy);
    targetCtx.lineTo(x2 + ox, y2 + oy);
    targetCtx.lineTo(x2 - ox, y2 - oy);
    targetCtx.lineTo(x1 - ox, y1 - oy);
    targetCtx.closePath();
    targetCtx.fill();
    // The along-travel overlap above closes gaps within one stroke, but where two separate
    // strokes cross near a junction (e.g. a "b"'s stem and bowl), their quads don't necessarily
    // extend toward each other — a thin outline stroke pads this quad by ~1px in every
    // direction, not just along travel, which is enough to paper over that kind of gap too.
    targetCtx.lineWidth = 2;
    targetCtx.strokeStyle = settings.color;
    targetCtx.stroke();

    tempDistance += segLength;
  });
}

// Draws one stored stroke (freehand or font-derived) onto a canvas context, honoring taper,
// dash style, and draw mode. Shared by the main canvas redraw, PNG export, and JPG export.
function drawStrokeToContext(targetCtx, stroke) {
  const settings = stroke.settings;

  if (settings.drawMode === "solid") {
    drawBroadNibStroke(targetCtx, stroke);
    return;
  }
  if (settings.drawMode === "zig") {
    drawZigStroke(targetCtx, stroke);
    return;
  }

  const totalLength = computeStrokeLength(stroke.points);
  const offset = getAngleOffset(settings.baseAngle);
  let tempDistance = 0;

  stroke.points.forEach((point) => {
    const tOverall = totalLength > 0 ? tempDistance / totalLength : 0;
    const width = computeTaperedWidth(settings.lineWidth, settings.widthProfile ?? 0, tOverall);
    tempDistance += drawOscillationSegment(
      targetCtx,
      point.x1,
      point.y1,
      point.x2,
      point.y2,
      tempDistance,
      offset,
      settings,
      width,
    );
  });
}

// Live in-progress stroke (during mousemove): flat width for responsiveness — the width
// profile taper needs the stroke's full length, which isn't known until the mouse is released.
function drawLiveSegment(x1, y1, x2, y2) {
  const settings = currentPenSettings();

  if (settings.drawMode === "solid") {
    // The nib angle is constant (unlike Zig/Arc's oscillating arm), so a single segment's
    // envelope needs no history from earlier segments — safe to draw live, one quad at a time.
    // Stretched a hair past its own segment (see drawBroadNibStroke) so it overlaps the next
    // live quad instead of exactly touching it, avoiding the same hairline-seam issue.
    const nibAngleRad = nibEdgeAngleRad(settings);
    const dirX = Math.cos(nibAngleRad);
    const dirY = Math.sin(nibAngleRad);
    const halfWidth = settings.armLength / 2;
    const segLength = Math.hypot(x2 - x1, y2 - y1);
    const ux = segLength > 0 ? (x2 - x1) / segLength : 0;
    const uy = segLength > 0 ? (y2 - y1) / segLength : 0;
    const ex1 = x1 - ux * 0.75;
    const ey1 = y1 - uy * 0.75;
    const ex2 = x2 + ux * 0.75;
    const ey2 = y2 + uy * 0.75;
    ctx.fillStyle = settings.color;
    ctx.beginPath();
    ctx.moveTo(ex1 + dirX * halfWidth, ey1 + dirY * halfWidth);
    ctx.lineTo(ex2 + dirX * halfWidth, ey2 + dirY * halfWidth);
    ctx.lineTo(ex2 - dirX * halfWidth, ey2 - dirY * halfWidth);
    ctx.lineTo(ex1 - dirX * halfWidth, ey1 - dirY * halfWidth);
    ctx.closePath();
    ctx.fill();
    totalDistance += segLength;
    return;
  }

  const offset = getAngleOffset(settings.baseAngle);
  totalDistance += drawOscillationSegment(ctx, x1, y1, x2, y2, totalDistance, offset, settings, settings.lineWidth);
}

// Converts a mouse event's screen position to world coordinates — i.e. undoes the current
// pan/zoom so strokes are always recorded in the same coordinate space regardless of view.
function screenToWorld(clientX, clientY) {
  const rect = canvas.getBoundingClientRect();
  const scaleX = canvas.clientWidth / rect.width;
  const scaleY = canvas.clientHeight / rect.height;
  const screenX = (clientX - rect.left) * scaleX;
  const screenY = (clientY - rect.top) * scaleY;
  return { x: (screenX - viewOffsetX) / viewScale, y: (screenY - viewOffsetY) / viewScale };
}

// Pointer Events (not mouse events) so this works with Apple Pencil on iPad Safari — Safari
// doesn't reliably synthesize mouse events for a pencil/touch drag, but it does dispatch proper
// pointer events for mouse, pen, and touch alike. setPointerCapture keeps move/up events
// targeted at the canvas even if the pointer drifts outside its bounds mid-stroke, which also
// replaces the old mouseleave-based fallback. activePointerId guards against a second touch
// (e.g. a resting palm) starting a stray second stroke while one is already in progress.
let activePointerId = null;

canvas.addEventListener("pointerdown", (e) => {
  if (activePointerId !== null) return;
  activePointerId = e.pointerId;
  canvas.setPointerCapture(e.pointerId);

  if (spacePanning) {
    isPanning = true;
    panStartClientX = e.clientX;
    panStartClientY = e.clientY;
    panStartOffsetX = viewOffsetX;
    panStartOffsetY = viewOffsetY;
    canvas.style.cursor = "grabbing";
    return;
  }

  isDrawing = true;
  const { x, y } = screenToWorld(e.clientX, e.clientY);
  lastX = x;
  lastY = y;
  totalDistance = 0;

  currentStroke = {
    type: "freehand",
    batchId: ++strokeBatchCounter,
    points: [],
    settings: currentPenSettings(),
  };
});

let currentStroke = null;

canvas.addEventListener("pointermove", (e) => {
  if (e.pointerId !== activePointerId) return;

  if (isPanning) {
    viewOffsetX = panStartOffsetX + (e.clientX - panStartClientX);
    viewOffsetY = panStartOffsetY + (e.clientY - panStartClientY);
    redrawCanvas();
    return;
  }

  if (!isDrawing) return;

  const { x: currentX, y: currentY } = screenToWorld(e.clientX, e.clientY);

  currentStroke.points.push({ x1: lastX, y1: lastY, x2: currentX, y2: currentY });

  drawLiveSegment(lastX, lastY, currentX, currentY);

  lastX = currentX;
  lastY = currentY;
});

function finishStroke(e) {
  if (e && e.pointerId !== activePointerId) return;
  activePointerId = null;

  if (isPanning) {
    isPanning = false;
    canvas.style.cursor = spacePanning ? "grab" : "crosshair";
    return;
  }

  if (isDrawing && currentStroke && currentStroke.points.length > 0) {
    strokes.push(currentStroke);
    redoStack = [];
    redrawCanvas(); // re-render with the width-profile taper now that the full length is known
  }
  isDrawing = false;
  currentStroke = null;
}

canvas.addEventListener("pointerup", finishStroke);
canvas.addEventListener("pointercancel", finishStroke);

function redrawCanvas() {
  setCanvasBackground();
  applyViewTransform();
  strokes.forEach((stroke) => drawStrokeToContext(ctx, stroke));
}

function undo() {
  if (strokes.length === 0) return;

  const batchId = strokes[strokes.length - 1].batchId;
  const removed = [];
  while (strokes.length > 0 && strokes[strokes.length - 1].batchId === batchId) {
    removed.push(strokes.pop());
  }
  redoStack.push(removed.reverse());
  redrawCanvas();
}

function redo() {
  if (redoStack.length > 0) {
    strokes.push(...redoStack.pop());
    redrawCanvas();
  }
}

// ============================================================================
// Export: SVG / PNG / JPG
// ============================================================================

function catmullRom2bezier(points) {
  let d = "";
  for (let i = 0; i < points.length - 1; i++) {
    const p0 = points[i - 1] || points[i];
    const p1 = points[i];
    const p2 = points[i + 1];
    const p3 = points[i + 2] || p2;

    const cp1x = p1.x + (p2.x - p0.x) / 6;
    const cp1y = p1.y + (p2.y - p0.y) / 6;
    const cp2x = p2.x - (p3.x - p1.x) / 6;
    const cp2y = p2.y - (p3.y - p1.y) / 6;

    d += `C ${cp1x},${cp1y} ${cp2x},${cp2y} ${p2.x},${p2.y} `;
  }
  return d;
}

// Mirrors drawStrokeToContext's geometry but emits one <path> per recorded point-pair (each
// can carry its own tapered stroke-width and dasharray, matching the canvas render).
function buildSvgPathsForStroke(stroke) {
  const settings = stroke.settings;
  const paths = [];

  if (settings.drawMode === "solid") {
    if (settings.invertNib) {
      // Invert: unchanged — the original whole-stroke envelope polygon.
      const { top, bottom } = buildNibEnvelope(stroke);
      if (top.length >= 2) {
        const outEdge = top.map((p) => `${p.x} ${p.y}`).join(" L ");
        const backEdge = bottom
          .slice()
          .reverse()
          .map((p) => `${p.x} ${p.y}`)
          .join(" L ");
        const d = `M ${outEdge} L ${backEdge} Z`;
        paths.push(`<path d="${d}" fill="${settings.color}" stroke="none" />`);
      }
      return paths;
    }

    // One <path> per segment (matching drawBroadNibStroke's canvas render) rather than one
    // whole-stroke envelope — a single envelope self-intersects on tight curves; see
    // drawBroadNibStroke's comment for why. Each quad is stretched a hair past its own segment
    // (SEAM_OVERLAP) so adjacent quads overlap instead of exactly touching, same reason as the
    // canvas version: two independently-edged shapes meeting at precisely the same line can
    // still render a hairline gap between them.
    const SEAM_OVERLAP = 0.75;
    const totalLength = computeStrokeLength(stroke.points);
    const nibAngleRad = nibEdgeAngleRad(settings);
    const dirX = Math.cos(nibAngleRad);
    const dirY = Math.sin(nibAngleRad);
    let tempDistance = 0;

    stroke.points.forEach((p) => {
      const segLength = Math.hypot(p.x2 - p.x1, p.y2 - p.y1);
      const tOverall = totalLength > 0 ? tempDistance / totalLength : 0;
      const halfWidth = computeTaperedWidth(settings.armLength, settings.widthProfile ?? 0, tOverall) / 2;
      const ox = dirX * halfWidth;
      const oy = dirY * halfWidth;

      const ux = segLength > 0 ? (p.x2 - p.x1) / segLength : 0;
      const uy = segLength > 0 ? (p.y2 - p.y1) / segLength : 0;
      const x1 = p.x1 - ux * SEAM_OVERLAP;
      const y1 = p.y1 - uy * SEAM_OVERLAP;
      const x2 = p.x2 + ux * SEAM_OVERLAP;
      const y2 = p.y2 + uy * SEAM_OVERLAP;

      const d = `M ${x1 + ox} ${y1 + oy} L ${x2 + ox} ${y2 + oy} L ${x2 - ox} ${y2 - oy} L ${x1 - ox} ${y1 - oy} Z`;
      // Also stroked (not just filled) with a thin outline in the same color — see
      // drawBroadNibStroke's comment: this pads the quad ~0.5px in every direction, closing gaps
      // where two separate strokes cross at a junction the along-travel overlap can't reach.
      paths.push(`<path d="${d}" fill="${settings.color}" stroke="${settings.color}" stroke-width="2" />`);
      tempDistance += segLength;
    });

    return paths;
  }

  const totalLength = computeStrokeLength(stroke.points);

  if (settings.drawMode === "zig") {
    const zigPoints = extractZigPoints(buildAllOscillationSamples(stroke));
    for (let i = 1; i < zigPoints.length; i++) {
      const a = zigPoints[i - 1];
      const b = zigPoints[i];
      const tOverall = totalLength > 0 ? a.dist / totalLength : 0;
      const width = computeTaperedWidth(settings.lineWidth, settings.widthProfile ?? 0, tOverall);
      const dash = dashPatternFor(settings.style, width);
      const d = `M ${a.penX} ${a.penY} L ${b.penX} ${b.penY}`;
      paths.push(
        `<path d="${d}" fill="none" stroke="${settings.color}" stroke-width="${width.toFixed(2)}" stroke-linecap="butt" stroke-linejoin="miter"${dash.length ? ` stroke-dasharray="${dash.join(",")}"` : ""} />`,
      );
    }
    return paths;
  }

  const offset = getAngleOffset(settings.baseAngle);
  let tempDistance = 0;

  stroke.points.forEach((point) => {
    const built = buildOscillationSamples(point.x1, point.y1, point.x2, point.y2, tempDistance, offset, settings);
    if (!built) return;
    const { samples, distance } = built;

    const tOverall = totalLength > 0 ? tempDistance / totalLength : 0;
    const width = computeTaperedWidth(settings.lineWidth, settings.widthProfile ?? 0, tOverall);
    const dash = dashPatternFor(settings.style, width);

    const penPoints = samples.map((p) => ({ x: p.penX, y: p.penY }));
    if (penPoints.length >= 2) {
      const d = `M ${penPoints[0].x} ${penPoints[0].y} ` + catmullRom2bezier(penPoints);
      paths.push(
        `<path d="${d}" fill="none" stroke="${settings.color}" stroke-width="${width.toFixed(2)}" stroke-linecap="round" stroke-linejoin="round"${dash.length ? ` stroke-dasharray="${dash.join(",")}"` : ""} />`,
      );
    }

    tempDistance += distance;
  });

  return paths;
}

function renderStrokesToContext(targetCtx) {
  targetCtx.fillStyle = backgroundColor;
  targetCtx.fillRect(0, 0, canvas.clientWidth, canvas.clientHeight);
  strokes.forEach((stroke) => drawStrokeToContext(targetCtx, stroke));
}

function downloadDataUrl(dataUrl, filename) {
  const link = document.createElement("a");
  link.download = filename;
  link.href = dataUrl;
  link.click();
}

function savePNG() {
  const tempCanvas = document.createElement("canvas");
  tempCanvas.width = canvas.clientWidth;
  tempCanvas.height = canvas.clientHeight;
  renderStrokesToContext(tempCanvas.getContext("2d"));
  downloadDataUrl(tempCanvas.toDataURL("image/png"), "scribble-pen.png");
}

function saveJPG() {
  const tempCanvas = document.createElement("canvas");
  tempCanvas.width = canvas.clientWidth;
  tempCanvas.height = canvas.clientHeight;
  renderStrokesToContext(tempCanvas.getContext("2d"));
  downloadDataUrl(tempCanvas.toDataURL("image/jpeg", 0.92), "scribble-pen.jpg");
}

function saveSVG() {
  const svgPaths = [];
  strokes.forEach((stroke) => svgPaths.push(...buildSvgPathsForStroke(stroke)));

  const svgContent = `
    <svg xmlns="http://www.w3.org/2000/svg"
         width="${canvas.clientWidth}"
         height="${canvas.clientHeight}"
         viewBox="0 0 ${canvas.clientWidth} ${canvas.clientHeight}">
      <rect width="100%" height="100%" fill="${backgroundColor}" />
      ${svgPaths.join("\n")}
    </svg>
  `;

  const blob = new Blob([svgContent], { type: "image/svg+xml" });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "scribble-pen.svg";
  a.click();
  URL.revokeObjectURL(url);
}

document.getElementById("exportSvgBtn")?.addEventListener("click", saveSVG);
document.getElementById("exportPngBtn")?.addEventListener("click", savePNG);
document.getElementById("exportJpgBtn")?.addEventListener("click", saveJPG);

// ============================================================================
// Mode toggle (footer button) — manual override of the OS/browser dark-mode preference
// ============================================================================

const modeToggleBtn = document.getElementById("modeToggleBtn");

modeToggleBtn?.addEventListener("click", () => {
  themeOverride = effectiveDarkMode() ? "light" : "dark";
  document.documentElement.dataset.theme = themeOverride;
  applyEffectiveThemeToCanvasColors();
});

// ============================================================================
// Initial paint
// ============================================================================

// Sizes a canvas's pixel buffer to match its actual rendered CSS size × devicePixelRatio
// (capped at 2x), then scales the context so every existing drawing call — which all use
// "logical" coordinates equal to CSS pixels — keeps working unchanged. Without this, the
// canvas's fixed HTML width/height attributes get stretched (non-uniformly, since they don't
// match the container's aspect ratio) to fill whatever CSS box they're laid out into, which is
// what was reading as pixelated/blurry.
function setupCanvasResolution(canvasEl, context) {
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  const cssWidth = canvasEl.clientWidth;
  const cssHeight = canvasEl.clientHeight;
  if (cssWidth === 0 || cssHeight === 0) return dpr;

  canvasEl.width = Math.round(cssWidth * dpr);
  canvasEl.height = Math.round(cssHeight * dpr);
  context.setTransform(dpr, 0, 0, dpr, 0, 0);
  return dpr;
}

canvasDpr = setupCanvasResolution(canvas, ctx);
if (previewCanvas && previewCtx) setupCanvasResolution(previewCanvas, previewCtx);

redrawCanvas();
renderPreview();
