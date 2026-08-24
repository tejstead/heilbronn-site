// Animated tesseract-to-Heilbronn n=16 visualizer
// No dependencies, vanilla JS, HTML5 Canvas
(function () {
  'use strict';

  // --- Constants ---
  var OMEGA_XW = 0.55;
  var OMEGA_YZ = 0.20;
  var START_OFFSET_XW = 0.3;
  var PERSPECTIVE_D = 2.0;

  // Phase timings (seconds)
  var T1 = 5.0;   // end of rotation
  var T2 = 8.0;   // end of deceleration/blend
  var T3 = 10.0;  // end of frozen pause
  var T4 = 12.5;  // end of affine stretch
  var T5 = 23.5;  // end of triangle reveal
  var T_TOTAL = T5;

  // Heilbronn affine map
  var A_HEIL = [
    [0.6774193548387097, -0.06451612903225806, 0.25806451612903225, 0.0],
    [0.0, 0.30303030303030304, 0.06060606060606061, 0.6363636363636364]
  ];

  // Orthographic freeze rotation angles
  var ORTHO_ANGLE_XW = 0.12;
  var ORTHO_ANGLE_YZ = 0.08;

  // 8 axis-aligned face parallelograms (bit-field vertex indices)
  var AXIS_FACES = [
    [0, 1, 4, 5], [0, 2, 8, 10], [1, 3, 9, 11], [2, 3, 6, 7],
    [4, 6, 12, 14], [5, 7, 13, 15], [8, 9, 12, 13], [10, 11, 14, 15]
  ];

  // 6 diagonal parallelograms (bit-field vertex indices)
  var DIAG_FACES = [
    [0, 3, 4, 7], [2, 6, 9, 13], [3, 5, 10, 12],
    [4, 6, 8, 10], [5, 7, 9, 11], [8, 11, 12, 15]
  ];

  // 8 remaining minimal triangles not in any parallelogram group
  var STRAY_TRIS = [
    [0,6,11], [0,6,12], [1,7,13], [2,8,14],
    [3,5,8], [3,9,15], [4,9,15], [7,10,12]
  ];

  // 32 edges of tesseract (Hamming distance 1)
  var EDGES = [];
  (function buildEdges() {
    for (var i = 0; i < 16; i++) {
      for (var b = 0; b < 4; b++) {
        var j = i ^ (1 << b);
        if (j > i) EDGES.push([i, j]);
      }
    }
  })();

  // 16 vertices of {0,1}^4
  var VERTICES_01 = [];
  for (var i = 0; i < 16; i++) {
    VERTICES_01.push([
      (i >> 0) & 1,
      (i >> 1) & 1,
      (i >> 2) & 1,
      (i >> 3) & 1
    ]);
  }

  // Centered vertices at {-0.5, 0.5}^4
  var VERTICES_CENTERED = VERTICES_01.map(function (v) {
    return [v[0] - 0.5, v[1] - 0.5, v[2] - 0.5, v[3] - 0.5];
  });

  // --- Theme colors (read from CSS custom properties) ---
  var theme = { bg: '#16161a', fg: '#e8e6e1', line: '#2c2c33', accent: '#ef7d54' };

  function readTheme() {
    var style = getComputedStyle(document.documentElement);
    theme.bg = style.getPropertyValue('--bg').trim() || theme.bg;
    theme.fg = style.getPropertyValue('--fg').trim() || theme.fg;
    theme.line = style.getPropertyValue('--line').trim() || theme.line;
    theme.accent = style.getPropertyValue('--accent').trim() || theme.accent;
  }

  // --- Utility functions ---
  function ease_in_out(t) {
    if (t < 0.5) return 4 * t * t * t;
    return 1 - Math.pow(-2 * t + 2, 3) / 2;
  }

  function lerp(a, b, t) {
    return a + (b - a) * t;
  }

  function rotate_xw(v, angle) {
    var c = Math.cos(angle), s = Math.sin(angle);
    return [
      c * v[0] + s * v[3],
      v[1],
      v[2],
      -s * v[0] + c * v[3]
    ];
  }

  function rotate_yz(v, angle) {
    var c = Math.cos(angle), s = Math.sin(angle);
    return [
      v[0],
      c * v[1] + s * v[2],
      -s * v[1] + c * v[2],
      v[3]
    ];
  }

  function project_perspective(v) {
    var d = PERSPECTIVE_D;
    var scale = d / (d + v[3]);
    return [
      (v[0] + 0.12 * v[2]) * scale,
      (v[1] + 0.20 * v[2]) * scale
    ];
  }

  function apply_heil(v01) {
    return [
      A_HEIL[0][0] * v01[0] + A_HEIL[0][1] * v01[1] + A_HEIL[0][2] * v01[2] + A_HEIL[0][3] * v01[3],
      A_HEIL[1][0] * v01[0] + A_HEIL[1][1] * v01[1] + A_HEIL[1][2] * v01[2] + A_HEIL[1][3] * v01[3]
    ];
  }

  function compute_ortho_freeze() {
    var pts = [];
    for (var i = 0; i < 16; i++) {
      var v01 = VERTICES_01[i];
      var vc = [v01[0] - 0.5, v01[1] - 0.5, v01[2] - 0.5, v01[3] - 0.5];
      vc = rotate_xw(vc, ORTHO_ANGLE_XW);
      vc = rotate_yz(vc, ORTHO_ANGLE_YZ);
      var v01r = [vc[0] + 0.5, vc[1] + 0.5, vc[2] + 0.5, vc[3] + 0.5];
      pts.push(apply_heil(v01r));
    }
    return pts;
  }

  function compute_heil_final() {
    var pts = [];
    for (var i = 0; i < 16; i++) {
      pts.push(apply_heil(VERTICES_01[i]));
    }
    return pts;
  }

  function normalize_to_box(pts2d, width, height, margin) {
    var minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
    for (var i = 0; i < pts2d.length; i++) {
      if (pts2d[i][0] < minX) minX = pts2d[i][0];
      if (pts2d[i][0] > maxX) maxX = pts2d[i][0];
      if (pts2d[i][1] < minY) minY = pts2d[i][1];
      if (pts2d[i][1] > maxY) maxY = pts2d[i][1];
    }
    var rangeX = maxX - minX || 1;
    var rangeY = maxY - minY || 1;
    var scale = Math.min((width - 2 * margin) / rangeX, (height - 2 * margin) / rangeY);
    var cx = (minX + maxX) / 2;
    var cy = (minY + maxY) / 2;
    var result = [];
    for (var i = 0; i < pts2d.length; i++) {
      result.push([
        width / 2 + (pts2d[i][0] - cx) * scale,
        height / 2 + (pts2d[i][1] - cy) * scale
      ]);
    }
    return result;
  }

  function triangle_area_raw(p0, p1, p2) {
    return 0.5 * Math.abs(
      (p1[0] - p0[0]) * (p2[1] - p0[1]) - (p2[0] - p0[0]) * (p1[1] - p0[1])
    );
  }

  // --- Precompute ALL 64 minimal triangles from the full C(16,3) set ---
  var ALL_MIN_TRIANGLES = [];

  function precomputeAllMinTriangles() {
    var TARGET_AREA = 7.0 / 341.0;
    var TOL = 1e-6;
    var pts = compute_heil_final();
    ALL_MIN_TRIANGLES = [];
    for (var i = 0; i < 16; i++) {
      for (var j = i + 1; j < 16; j++) {
        for (var k = j + 1; k < 16; k++) {
          var area = triangle_area_raw(pts[i], pts[j], pts[k]);
          if (Math.abs(area - TARGET_AREA) < TOL) {
            ALL_MIN_TRIANGLES.push([i, j, k]);
          }
        }
      }
    }
  }
  precomputeAllMinTriangles();

  // For each face, filter to triangles whose 3 vertices are all in the face's vertex set
  function triangles_in_face(faceIndices) {
    var faceSet = {};
    for (var i = 0; i < faceIndices.length; i++) {
      faceSet[faceIndices[i]] = true;
    }
    var result = [];
    for (var t = 0; t < ALL_MIN_TRIANGLES.length; t++) {
      var tri = ALL_MIN_TRIANGLES[t];
      if (faceSet[tri[0]] && faceSet[tri[1]] && faceSet[tri[2]]) {
        result.push(tri);
      }
    }
    return result;
  }

  // Precompute per-face triangles
  var axisTriangles = [];
  var diagTriangles = [];

  function precomputeFaceTriangles() {
    axisTriangles = [];
    diagTriangles = [];
    for (var i = 0; i < AXIS_FACES.length; i++) {
      axisTriangles.push(triangles_in_face(AXIS_FACES[i]));
    }
    for (var i = 0; i < DIAG_FACES.length; i++) {
      diagTriangles.push(triangles_in_face(DIAG_FACES[i]));
    }
  }
  precomputeFaceTriangles();
  console.log('[tesseract] min triangles found:', ALL_MIN_TRIANGLES.length,
    '| axis faces:', axisTriangles.map(function(t){return t.length;}),
    '| diag faces:', diagTriangles.map(function(t){return t.length;}));

  // --- Bounding box of Heilbronn points (for drawing the unit square outline) ---
  var heilFinal = compute_heil_final();
  var orthoFreeze = compute_ortho_freeze();

  function computeBBox(pts) {
    var minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
    for (var i = 0; i < pts.length; i++) {
      if (pts[i][0] < minX) minX = pts[i][0];
      if (pts[i][0] > maxX) maxX = pts[i][0];
      if (pts[i][1] < minY) minY = pts[i][1];
      if (pts[i][1] > maxY) maxY = pts[i][1];
    }
    return { minX: minX, maxX: maxX, minY: minY, maxY: maxY };
  }

  // --- Main animation state ---
  var canvas, ctx;
  var animStart = null;
  var animId = null;
  var currentTime = 0;
  var playing = true;
  var scrubber = null;
  var playBtn = null;

  function resizeCanvas() {
    var container = canvas.parentElement;
    var w = container ? container.clientWidth : 600;
    var size = Math.min(w, 600);
    canvas.width = size;
    canvas.height = size;
  }

  function getProjectedPoints(t) {
    var width = canvas.width;
    var height = canvas.height;
    var margin = 40;

    if (t <= T1) {
      var angle_xw = START_OFFSET_XW + OMEGA_XW * t;
      var angle_yz = OMEGA_YZ * t;
      var pts2d = [];
      for (var i = 0; i < 16; i++) {
        var v = VERTICES_CENTERED[i];
        v = rotate_xw(v, angle_xw);
        v = rotate_yz(v, angle_yz);
        pts2d.push(project_perspective(v));
      }
      return { pts: normalize_to_box(pts2d, width, height, margin), edgeAlpha: 1.0, phase: 1 };
    }

    if (t <= T2) {
      var blend = ease_in_out((t - T1) / (T2 - T1));
      var dt = t - T1;
      var dur = T2 - T1;
      var frac = dt / dur;
      var angle_xw = START_OFFSET_XW + OMEGA_XW * T1 + OMEGA_XW * dt * (1 - frac / 2);
      var angle_yz = OMEGA_YZ * T1 + OMEGA_YZ * dt * (1 - frac / 2);

      var perspPts = [];
      for (var i = 0; i < 16; i++) {
        var v = VERTICES_CENTERED[i];
        v = rotate_xw(v, angle_xw);
        v = rotate_yz(v, angle_yz);
        perspPts.push(project_perspective(v));
      }
      var perspNorm = normalize_to_box(perspPts, width, height, margin);
      var orthoNorm = normalize_to_box(orthoFreeze, width, height, margin);

      var pts = [];
      for (var i = 0; i < 16; i++) {
        pts.push([
          lerp(perspNorm[i][0], orthoNorm[i][0], blend),
          lerp(perspNorm[i][1], orthoNorm[i][1], blend)
        ]);
      }
      return { pts: pts, edgeAlpha: 1.0, phase: 2 };
    }

    if (t <= T3) {
      var pts = normalize_to_box(orthoFreeze, canvas.width, canvas.height, margin);
      return { pts: pts, edgeAlpha: 1.0, phase: 3 };
    }

    if (t <= T4) {
      var blend = ease_in_out((t - T3) / (T4 - T3));
      var orthoNorm = normalize_to_box(orthoFreeze, width, height, margin);
      var heilNorm = normalize_to_box(heilFinal, width, height, margin);
      var pts = [];
      for (var i = 0; i < 16; i++) {
        pts.push([
          lerp(orthoNorm[i][0], heilNorm[i][0], blend),
          lerp(orthoNorm[i][1], heilNorm[i][1], blend)
        ]);
      }
      var edgeAlpha = 1.0 - blend;
      return { pts: pts, edgeAlpha: edgeAlpha, phase: 4 };
    }

    // Phase 5: triangle reveal
    var heilNorm = normalize_to_box(heilFinal, width, height, margin);
    return { pts: heilNorm, edgeAlpha: 0.0, phase: 5, phaseT: (t - T4) / (T5 - T4) };
  }

  function getTriangleRevealState(phaseT) {
    // Total duration = T5 - T4 = 11s. phaseT goes 0 to 1.
    // Layout: first face tri-by-tri, then 7 axis faces staggered, then 6 diag staggered, then 8 strays
    // Total must fit within phaseT [0, 0.9] to leave hold time at end
    var FIRST_END = 0.12;
    var AXIS_STAGGER = 0.05;
    var DIAG_STAGGER = 0.05;
    var STRAY_STAGGER = 0.02;
    var AXIS_START = FIRST_END;                          // 0.12
    var DIAG_START = AXIS_START + 7 * AXIS_STAGGER;     // 0.47
    var STRAY_START = DIAG_START + 6 * DIAG_STAGGER;    // 0.77
    // STRAY ends at 0.77 + 8*0.02 = 0.93 -- fits within 1.0
    var FADE_DUR = 0.04;

    var state = {
      firstAlpha: [],
      faceAlphas: [], // alpha for axis faces 1-7
      diagAlphas: [], // alpha for diag faces 0-5
      strayAlphas: [] // alpha for 8 remaining triangles
    };

    // First face: triangle by triangle
    var numTris = axisTriangles[0] ? axisTriangles[0].length : 4;
    var perTri = FIRST_END / numTris;
    for (var i = 0; i < numTris; i++) {
      var triStart = i * perTri;
      var triEnd = triStart + perTri * 0.7; // fade in over 70% of slot
      if (phaseT >= triEnd) {
        state.firstAlpha.push(1.0);
      } else if (phaseT >= triStart) {
        state.firstAlpha.push(Math.min(1.0, (phaseT - triStart) / (perTri * 0.7)));
      } else {
        state.firstAlpha.push(0.0);
      }
    }

    // Remaining 7 axis faces, staggered
    for (var fi = 0; fi < 7; fi++) {
      var fStart = AXIS_START + fi * AXIS_STAGGER;
      if (phaseT >= fStart + FADE_DUR) {
        state.faceAlphas.push(1.0);
      } else if (phaseT >= fStart) {
        state.faceAlphas.push((phaseT - fStart) / FADE_DUR);
      } else {
        state.faceAlphas.push(0.0);
      }
    }

    // 6 diagonal faces, staggered
    for (var di = 0; di < 6; di++) {
      var dStart = DIAG_START + di * DIAG_STAGGER;
      if (phaseT >= dStart + FADE_DUR) {
        state.diagAlphas.push(1.0);
      } else if (phaseT >= dStart) {
        state.diagAlphas.push((phaseT - dStart) / FADE_DUR);
      } else {
        state.diagAlphas.push(0.0);
      }
    }

    // 8 stray triangles
    for (var si = 0; si < 8; si++) {
      var sStart = STRAY_START + si * STRAY_STAGGER;
      if (phaseT >= sStart + FADE_DUR) {
        state.strayAlphas.push(1.0);
      } else if (phaseT >= sStart) {
        state.strayAlphas.push((phaseT - sStart) / FADE_DUR);
      } else {
        state.strayAlphas.push(0.0);
      }
    }

    return state;
  }

  // Draw the bounding square outline (only in phases 4 and 5)
  function drawBoundingSquare(pts) {
    var minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
    for (var i = 0; i < pts.length; i++) {
      if (pts[i][0] < minX) minX = pts[i][0];
      if (pts[i][0] > maxX) maxX = pts[i][0];
      if (pts[i][1] < minY) minY = pts[i][1];
      if (pts[i][1] > maxY) maxY = pts[i][1];
    }
    ctx.strokeStyle = theme.line;
    ctx.lineWidth = 1.5;
    ctx.strokeRect(minX, minY, maxX - minX, maxY - minY);
  }

  function drawScene(t) {
    var width = canvas.width;
    var height = canvas.height;
    ctx.fillStyle = theme.bg;
    ctx.fillRect(0, 0, width, height);

    var state = getProjectedPoints(t);
    var pts = state.pts;

    // Bounding square in phases 4 and 5
    if (state.phase === 4 || state.phase === 5) {
      drawBoundingSquare(pts);
    }

    // Draw edges
    if (state.edgeAlpha > 0.01) {
      ctx.strokeStyle = 'rgba(0,200,200,' + state.edgeAlpha.toFixed(3) + ')';
      ctx.lineWidth = 1.5;
      ctx.beginPath();
      for (var e = 0; e < EDGES.length; e++) {
        var a = pts[EDGES[e][0]];
        var b = pts[EDGES[e][1]];
        ctx.moveTo(a[0], a[1]);
        ctx.lineTo(b[0], b[1]);
      }
      ctx.stroke();
    }

    // Draw triangles in phase 5
    if (state.phase === 5 && state.phaseT !== undefined) {
      var reveal = getTriangleRevealState(state.phaseT);

      // First face triangles (one by one)
      if (axisTriangles[0]) {
        for (var ti = 0; ti < reveal.firstAlpha.length; ti++) {
          var alpha = reveal.firstAlpha[ti];
          if (alpha > 0.01 && axisTriangles[0][ti]) {
            var tri = axisTriangles[0][ti];
            ctx.fillStyle = 'rgba(50,130,255,' + (alpha * 0.4).toFixed(3) + ')';
            ctx.beginPath();
            ctx.moveTo(pts[tri[0]][0], pts[tri[0]][1]);
            ctx.lineTo(pts[tri[1]][0], pts[tri[1]][1]);
            ctx.lineTo(pts[tri[2]][0], pts[tri[2]][1]);
            ctx.closePath();
            ctx.fill();
            ctx.strokeStyle = 'rgba(50,130,255,' + (alpha * 0.8).toFixed(3) + ')';
            ctx.lineWidth = 1;
            ctx.stroke();
          }
        }
      }

      // Remaining 7 axis faces (staggered)
      for (var fi = 0; fi < 7; fi++) {
        var alpha = reveal.faceAlphas[fi];
        if (alpha > 0.01 && axisTriangles[fi + 1]) {
          var tris = axisTriangles[fi + 1];
          for (var ti = 0; ti < tris.length; ti++) {
            var tri = tris[ti];
            ctx.fillStyle = 'rgba(50,130,255,' + (alpha * 0.4).toFixed(3) + ')';
            ctx.beginPath();
            ctx.moveTo(pts[tri[0]][0], pts[tri[0]][1]);
            ctx.lineTo(pts[tri[1]][0], pts[tri[1]][1]);
            ctx.lineTo(pts[tri[2]][0], pts[tri[2]][1]);
            ctx.closePath();
            ctx.fill();
            ctx.strokeStyle = 'rgba(50,130,255,' + (alpha * 0.8).toFixed(3) + ')';
            ctx.lineWidth = 1;
            ctx.stroke();
          }
        }
      }

      // 6 diagonal faces (staggered)
      for (var fi = 0; fi < 6; fi++) {
        var alpha = reveal.diagAlphas[fi];
        if (alpha > 0.01 && diagTriangles[fi]) {
          var tris = diagTriangles[fi];
          for (var ti = 0; ti < tris.length; ti++) {
            var tri = tris[ti];
            ctx.fillStyle = 'rgba(255,150,30,' + (alpha * 0.4).toFixed(3) + ')';
            ctx.beginPath();
            ctx.moveTo(pts[tri[0]][0], pts[tri[0]][1]);
            ctx.lineTo(pts[tri[1]][0], pts[tri[1]][1]);
            ctx.lineTo(pts[tri[2]][0], pts[tri[2]][1]);
            ctx.closePath();
            ctx.fill();
            ctx.strokeStyle = 'rgba(255,150,30,' + (alpha * 0.8).toFixed(3) + ')';
            ctx.lineWidth = 1;
            ctx.stroke();
          }
        }
      }

      // 8 stray triangles (green-ish)
      for (var si = 0; si < STRAY_TRIS.length; si++) {
        var alpha = reveal.strayAlphas[si];
        if (alpha > 0.01) {
          var tri = STRAY_TRIS[si];
          ctx.fillStyle = 'rgba(100,210,130,' + (alpha * 0.4).toFixed(3) + ')';
          ctx.beginPath();
          ctx.moveTo(pts[tri[0]][0], pts[tri[0]][1]);
          ctx.lineTo(pts[tri[1]][0], pts[tri[1]][1]);
          ctx.lineTo(pts[tri[2]][0], pts[tri[2]][1]);
          ctx.closePath();
          ctx.fill();
          ctx.strokeStyle = 'rgba(100,210,130,' + (alpha * 0.8).toFixed(3) + ')';
          ctx.lineWidth = 1;
          ctx.stroke();
        }
      }
    }

    // Draw vertices
    ctx.fillStyle = theme.fg;
    for (var i = 0; i < 16; i++) {
      ctx.beginPath();
      ctx.arc(pts[i][0], pts[i][1], 3.5, 0, 2 * Math.PI);
      ctx.fill();
    }
  }

  // --- Playback controls ---
  function updateScrubber() {
    if (scrubber) {
      scrubber.value = Math.round((currentTime / T_TOTAL) * 1000);
    }
  }

  function setPlaying(val) {
    playing = val;
    if (playBtn) {
      playBtn.textContent = playing ? 'Pause' : 'Play';
    }
    if (playing) {
      animStart = performance.now() - currentTime * 1000;
      if (!animId) animId = requestAnimationFrame(tick);
    }
  }

  function tick(timestamp) {
    if (!playing) {
      animId = null;
      return;
    }
    if (!animStart) animStart = timestamp - currentTime * 1000;
    currentTime = (timestamp - animStart) / 1000;
    if (currentTime >= T_TOTAL) {
      currentTime = T_TOTAL;
      playing = false;
      if (playBtn) playBtn.textContent = 'Play';
    }
    updateScrubber();
    drawScene(currentTime);
    if (playing) {
      animId = requestAnimationFrame(tick);
    } else {
      animId = null;
    }
  }

  function seekTo(t) {
    currentTime = Math.max(0, Math.min(T_TOTAL, t));
    animStart = null;
    drawScene(currentTime);
    updateScrubber();
  }

  function init() {
    canvas = document.getElementById('tesseract-canvas');
    if (!canvas) return;
    ctx = canvas.getContext('2d');

    playBtn = document.getElementById('tesseract-playpause');
    scrubber = document.getElementById('tesseract-scrub');

    readTheme();
    resizeCanvas();

    // Play/pause button
    if (playBtn) {
      playBtn.addEventListener('click', function () {
        if (currentTime >= T_TOTAL) {
          currentTime = 0;
          setPlaying(true);
        } else {
          setPlaying(!playing);
        }
      });
    }

    // Scrubber
    if (scrubber) {
      scrubber.addEventListener('input', function () {
        var wasPlaying = playing;
        if (playing) setPlaying(false);
        var frac = parseInt(scrubber.value, 10) / 1000;
        seekTo(frac * T_TOTAL);
      });
    }

    // Click canvas to toggle play/pause
    canvas.addEventListener('click', function () {
      if (currentTime >= T_TOTAL) {
        currentTime = 0;
        setPlaying(true);
      } else {
        setPlaying(!playing);
      }
    });

    // Resize handling
    window.addEventListener('resize', function () {
      resizeCanvas();
      drawScene(currentTime);
    });

    // Respond to color scheme changes
    if (window.matchMedia) {
      var mq = window.matchMedia('(prefers-color-scheme: dark)');
      var handler = function () {
        readTheme();
        drawScene(currentTime);
      };
      if (mq.addEventListener) {
        mq.addEventListener('change', handler);
      } else if (mq.addListener) {
        mq.addListener(handler);
      }
    }

    // Start playing
    currentTime = 0;
    setPlaying(true);
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
