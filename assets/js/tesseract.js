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

  // Heilbronn affine map
  var A_HEIL = [
    [0.6774193548387097, -0.06451612903225806, 0.25806451612903225, 0.0],
    [0.0, 0.30303030303030304, 0.06060606060606061, 0.6363636363636364]
  ];

  // Orthographic freeze rotation angles
  var ORTHO_ANGLE_XW = 0.12;
  var ORTHO_ANGLE_YZ = 0.08;

  // 8 axis-aligned face parallelograms (ordered quads)
  var AXIS_FACES = [
    [4, 0, 1, 5], [0, 8, 10, 2], [4, 12, 14, 6], [1, 9, 11, 3],
    [5, 13, 15, 7], [6, 2, 3, 7], [12, 8, 9, 13], [14, 10, 11, 15]
  ];

  // 6 diagonal parallelograms (ordered quads)
  var DIAG_FACES = [
    [0, 2, 14, 12], [1, 3, 15, 13], [9, 10, 14, 13],
    [4, 6, 11, 9], [1, 2, 6, 5], [3, 5, 12, 10]
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
    // Apply rotation R(0.12, 0.08) to centered vertices, then project via A_HEIL
    var pts = [];
    for (var i = 0; i < 16; i++) {
      var v = VERTICES_CENTERED[i];
      v = rotate_xw(v, ORTHO_ANGLE_XW);
      v = rotate_yz(v, ORTHO_ANGLE_YZ);
      // Project through A_HEIL applied to {0,1}^4 vertex + rotation offset
      // We need to map back: rotated centered = rotated(v - 0.5) => for A_HEIL we use the 01 vertex
      // Actually: A_HEIL @ R.T means we rotate the coordinate system
      // ortho freeze = A_HEIL applied to R.T @ {0,1}^4 vertices
      // Let's compute it properly: R.T rotates the basis, so we rotate {0,1}^4 vertices
      var v01 = VERTICES_01[i];
      var vc = [v01[0] - 0.5, v01[1] - 0.5, v01[2] - 0.5, v01[3] - 0.5];
      vc = rotate_xw(vc, ORTHO_ANGLE_XW);
      vc = rotate_yz(vc, ORTHO_ANGLE_YZ);
      // Map back to 01 range for A_HEIL
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

  function triangle_area(p0, p1, p2) {
    return 0.5 * Math.abs(
      (p1[0] - p0[0]) * (p2[1] - p0[1]) - (p2[0] - p0[0]) * (p1[1] - p0[1])
    );
  }

  // Find minimal triangles from 4 quad vertices in the Heilbronn configuration
  function find_min_triangles_in_face(faceIndices, pts2d) {
    var TARGET_AREA = 7.0 / 341.0;
    var TOL = 1e-6;
    var triangles = [];
    var indices = faceIndices;
    // All C(4,3) = 4 triangles from the quad
    var combos = [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]];

    // Compute the bounding area to normalize
    // pts2d are already in the Heilbronn unit: A_HEIL maps {0,1}^4 to ~[0,1]^2
    // We need to check area relative to the full point set bounding box
    // Actually the area 7/341 is in the normalized Heilbronn coordinates
    // We need to work in the raw A_HEIL output coordinates

    for (var c = 0; c < combos.length; c++) {
      var i0 = indices[combos[c][0]];
      var i1 = indices[combos[c][1]];
      var i2 = indices[combos[c][2]];
      var area = triangle_area(pts2d[i0], pts2d[i1], pts2d[i2]);
      if (Math.abs(area - TARGET_AREA) < TOL) {
        triangles.push([i0, i1, i2]);
      }
    }
    return triangles;
  }

  // --- Main animation ---
  var canvas, ctx;
  var animStart = null;
  var animId = null;
  var orthoFreeze = compute_ortho_freeze();
  var heilFinal = compute_heil_final();

  // Precompute min triangles for each face in the final Heilbronn config
  var axisTriangles = [];
  var diagTriangles = [];

  function precomputeTriangles() {
    axisTriangles = [];
    diagTriangles = [];
    for (var i = 0; i < AXIS_FACES.length; i++) {
      var tris = find_min_triangles_in_face(AXIS_FACES[i], heilFinal);
      axisTriangles.push(tris);
    }
    for (var i = 0; i < DIAG_FACES.length; i++) {
      var tris = find_min_triangles_in_face(DIAG_FACES[i], heilFinal);
      diagTriangles.push(tris);
    }
  }
  precomputeTriangles();

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
      // Phase 1: rotating perspective
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
      // Phase 2: decelerate + blend perspective to orthographic
      var blend = ease_in_out((t - T1) / (T2 - T1));
      // Rotation decelerates
      var dt = t - T1;
      var dur = T2 - T1;
      // Speed goes from full to zero: integrate deceleration
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
      // Phase 3: frozen orthographic
      var pts = normalize_to_box(orthoFreeze, canvas.width, canvas.height, margin);
      return { pts: pts, edgeAlpha: 1.0, phase: 3 };
    }

    if (t <= T4) {
      // Phase 4: affine stretch to Heilbronn, edges fade
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
    // phaseT goes 0 to 1 over the reveal phase (11 seconds)
    // First face (axis[0]) triangle-by-triangle: 0 to 0.2
    // Remaining 7 axis faces all at once: 0.2 to 0.5
    // 6 diagonal faces: 0.5 to 0.85
    // Hold: 0.85 to 1.0
    var state = {
      firstFaceTris: 0, // 0-4, how many triangles of first face visible
      axisVisible: 0,   // 0 or 1, whether remaining axis faces visible
      diagVisible: 0,   // 0 or 1
      axisAlpha: 0,
      diagAlpha: 0,
      firstAlpha: []
    };

    if (phaseT < 0.2) {
      // First face triangles one by one
      var sub = phaseT / 0.2; // 0-1 over this sub-phase
      var numTris = axisTriangles[0].length || 4;
      var perTri = 1.0 / numTris;
      for (var i = 0; i < numTris; i++) {
        var triStart = i * perTri;
        var triEnd = (i + 1) * perTri;
        if (sub >= triEnd) {
          state.firstAlpha.push(1.0);
        } else if (sub >= triStart) {
          state.firstAlpha.push(ease_in_out((sub - triStart) / perTri));
        } else {
          state.firstAlpha.push(0.0);
        }
      }
      state.firstFaceTris = numTris;
    } else {
      // All first face triangles visible
      var numTris = axisTriangles[0].length || 4;
      for (var i = 0; i < numTris; i++) state.firstAlpha.push(1.0);
      state.firstFaceTris = numTris;

      if (phaseT < 0.5) {
        var sub = ease_in_out((phaseT - 0.2) / 0.3);
        state.axisVisible = 1;
        state.axisAlpha = sub;
      } else if (phaseT < 0.85) {
        state.axisVisible = 1;
        state.axisAlpha = 1.0;
        var sub = ease_in_out((phaseT - 0.5) / 0.35);
        state.diagVisible = 1;
        state.diagAlpha = sub;
      } else {
        state.axisVisible = 1;
        state.axisAlpha = 1.0;
        state.diagVisible = 1;
        state.diagAlpha = 1.0;
      }
    }
    return state;
  }

  function drawFrame(timestamp) {
    if (!animStart) animStart = timestamp;
    var t = (timestamp - animStart) / 1000;

    if (t > T5 + 1.0) {
      // Animation done, draw final frame and stop
      drawScene(T5);
      return;
    }

    drawScene(Math.min(t, T5));
    animId = requestAnimationFrame(drawFrame);
  }

  function drawScene(t) {
    var width = canvas.width;
    var height = canvas.height;
    ctx.fillStyle = '#000';
    ctx.fillRect(0, 0, width, height);

    var state = getProjectedPoints(t);
    var pts = state.pts;

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

      // Draw first face triangles
      for (var ti = 0; ti < reveal.firstAlpha.length; ti++) {
        if (reveal.firstAlpha[ti] > 0.01 && axisTriangles[0] && axisTriangles[0][ti]) {
          var tri = axisTriangles[0][ti];
          var alpha = reveal.firstAlpha[ti] * 0.4;
          ctx.fillStyle = 'rgba(50,130,255,' + alpha.toFixed(3) + ')';
          ctx.beginPath();
          ctx.moveTo(pts[tri[0]][0], pts[tri[0]][1]);
          ctx.lineTo(pts[tri[1]][0], pts[tri[1]][1]);
          ctx.lineTo(pts[tri[2]][0], pts[tri[2]][1]);
          ctx.closePath();
          ctx.fill();
          // Edge
          ctx.strokeStyle = 'rgba(50,130,255,' + (reveal.firstAlpha[ti] * 0.8).toFixed(3) + ')';
          ctx.lineWidth = 1;
          ctx.stroke();
        }
      }

      // Draw remaining axis face triangles
      if (reveal.axisVisible && reveal.axisAlpha > 0.01) {
        for (var fi = 1; fi < AXIS_FACES.length; fi++) {
          var tris = axisTriangles[fi];
          for (var ti = 0; ti < tris.length; ti++) {
            var tri = tris[ti];
            var alpha = reveal.axisAlpha * 0.4;
            ctx.fillStyle = 'rgba(50,130,255,' + alpha.toFixed(3) + ')';
            ctx.beginPath();
            ctx.moveTo(pts[tri[0]][0], pts[tri[0]][1]);
            ctx.lineTo(pts[tri[1]][0], pts[tri[1]][1]);
            ctx.lineTo(pts[tri[2]][0], pts[tri[2]][1]);
            ctx.closePath();
            ctx.fill();
            ctx.strokeStyle = 'rgba(50,130,255,' + (reveal.axisAlpha * 0.8).toFixed(3) + ')';
            ctx.lineWidth = 1;
            ctx.stroke();
          }
        }
      }

      // Draw diagonal face triangles
      if (reveal.diagVisible && reveal.diagAlpha > 0.01) {
        for (var fi = 0; fi < DIAG_FACES.length; fi++) {
          var tris = diagTriangles[fi];
          for (var ti = 0; ti < tris.length; ti++) {
            var tri = tris[ti];
            var alpha = reveal.diagAlpha * 0.4;
            ctx.fillStyle = 'rgba(255,150,30,' + alpha.toFixed(3) + ')';
            ctx.beginPath();
            ctx.moveTo(pts[tri[0]][0], pts[tri[0]][1]);
            ctx.lineTo(pts[tri[1]][0], pts[tri[1]][1]);
            ctx.lineTo(pts[tri[2]][0], pts[tri[2]][1]);
            ctx.closePath();
            ctx.fill();
            ctx.strokeStyle = 'rgba(255,150,30,' + (reveal.diagAlpha * 0.8).toFixed(3) + ')';
            ctx.lineWidth = 1;
            ctx.stroke();
          }
        }
      }
    }

    // Draw vertices
    ctx.fillStyle = '#fff';
    for (var i = 0; i < 16; i++) {
      ctx.beginPath();
      ctx.arc(pts[i][0], pts[i][1], 3.5, 0, 2 * Math.PI);
      ctx.fill();
    }
  }

  function startAnimation() {
    if (animId) cancelAnimationFrame(animId);
    animStart = null;
    resizeCanvas();
    animId = requestAnimationFrame(drawFrame);
  }

  function init() {
    canvas = document.getElementById('tesseract-canvas');
    if (!canvas) return;
    ctx = canvas.getContext('2d');

    resizeCanvas();
    window.addEventListener('resize', function () {
      resizeCanvas();
      if (!animId) drawScene(T5); // redraw final if animation done
    });

    var replayBtn = document.getElementById('tesseract-replay');
    if (replayBtn) {
      replayBtn.addEventListener('click', function () {
        startAnimation();
      });
    }

    startAnimation();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
