// Family viewer enhancement: slider + play/pause over the precomputed family
// samples. Pure progressive enhancement — the static SVG already shows the
// stored member with the family traces; this adds motion. Every sample was
// verified in exact arithmetic at build time; frames interpolate linearly
// between adjacent samples.
"use strict";

document.querySelectorAll("figure.family").forEach(init);

function init(fig) {
  const svg = fig.querySelector("svg");
  const dataEl = fig.querySelector("script.family-data");
  const controls = fig.querySelector(".family-controls");
  if (!svg || !dataEl || !controls) return;
  const data = JSON.parse(dataEl.textContent);
  const S = data.samples, K = S.length, n = S[0].length;
  controls.hidden = false;

  const circles = [...svg.querySelectorAll(".points circle")];
  const mintriLayer = svg.querySelector("g.mintris");
  const domainPoly = svg.querySelector("g.domain polygon");
  const range = controls.querySelector(".fam-range");
  const playBtn = controls.querySelector(".fam-play");
  const valEl = controls.querySelector(".fam-val");
  const tiesEl = controls.querySelector(".fam-ties");
  const pool = [...mintriLayer.querySelectorAll("polygon")];

  const tris = [];
  for (let a = 0; a < n - 2; a++)
    for (let b = a + 1; b < n - 1; b++)
      for (let c = b + 1; c < n; c++) tris.push([a, b, c]);

  function member(u) {
    const x = u * (K - 1);
    const i = Math.min(K - 2, Math.floor(x));
    const t = x - i;
    return S[i].map((p, j) => [
      p[0] + (S[i + 1][j][0] - p[0]) * t,
      p[1] + (S[i + 1][j][1] - p[1]) * t,
    ]);
  }

  function render(u) {
    const P = member(u);
    circles.forEach(c => {
      const j = +c.dataset.idx;
      c.setAttribute("cx", P[j][0]);
      c.setAttribute("cy", P[j][1]);
    });
    if (data.hull && domainPoly)
      domainPoly.setAttribute("points",
        data.hull.map(j => P[j].join(",")).join(" "));
    let min = Infinity;
    const areas = tris.map(([a, b, c]) => {
      const ar = Math.abs(
        (P[b][0] - P[a][0]) * (P[c][1] - P[a][1]) -
        (P[c][0] - P[a][0]) * (P[b][1] - P[a][1])) / 2;
      if (ar < min) min = ar;
      return ar;
    });
    let k = 0;
    tris.forEach((t, idx) => {
      if (areas[idx] > min * (1 + data.tieTol)) return;
      let el = pool[k];
      if (!el) {
        el = document.createElementNS("http://www.w3.org/2000/svg", "polygon");
        el.setAttribute("class", "mintri cc-0");
        mintriLayer.appendChild(el);
        pool.push(el);
      }
      el.style.display = "";
      el.setAttribute("points", t.map(j => P[j].join(",")).join(" "));
      k++;
    });
    for (let r = k; r < pool.length; r++) pool[r].style.display = "none";
    tiesEl.textContent = k + " minimal triangle" + (k === 1 ? "" : "s");
    const p = data.param;
    valEl.textContent =
      u <= 0 ? p.lo_label :
      u >= 1 ? p.hi_label :
      (p.lo + (p.hi - p.lo) * u).toFixed(6);
  }

  range.addEventListener("input", () => render(+range.value / 1000));
  let playing = false, dir = 1;
  function tick() {
    if (playing) {
      let v = +range.value + dir * 4;
      if (v >= 1000) { v = 1000; dir = -1; }
      if (v <= 0) { v = 0; dir = 1; }
      range.value = v;
      render(v / 1000);
    }
    requestAnimationFrame(tick);
  }
  playBtn.addEventListener("click", () => {
    playing = !playing;
    playBtn.textContent = playing ? "pause" : "play";
    playBtn.setAttribute("aria-pressed", String(playing));
  });
  render(+range.value / 1000);
  requestAnimationFrame(tick);
}
