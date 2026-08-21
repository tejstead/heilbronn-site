// Viewer enhancement: congruence-class highlighting, symmetry-orbit
// highlighting on point hover, and a static symmetry-elements toggle.
// Pure progressive enhancement — the static SVG already shows the
// configuration and its minimal triangles; this only adds interaction.
"use strict";

document.querySelectorAll("figure.viewer").forEach(init);

function init(fig) {
  const svg = fig.querySelector("svg");
  const controls = fig.querySelector(".viewer-controls");
  if (!svg || !controls) return;
  controls.hidden = false;

  // --- Congruence classes -------------------------------------------------
  let sticky = false;
  const ccButtons = controls.querySelectorAll("[data-cc]");
  ccButtons.forEach(btn => {
    btn.addEventListener("click", () => {
      const cur = svg.getAttribute("data-focus-cc");
      ccButtons.forEach(b => b.setAttribute("aria-pressed", "false"));
      if (btn.dataset.cc === "all" || cur === btn.dataset.cc) {
        svg.removeAttribute("data-focus-cc");
      } else {
        svg.setAttribute("data-focus-cc", btn.dataset.cc);
        btn.setAttribute("aria-pressed", "true");
      }
      sticky = svg.hasAttribute("data-focus-cc");
    });
  });
  svg.querySelectorAll(".mintri").forEach(tri => {
    tri.addEventListener("mouseenter", () => {
      if (!sticky) svg.setAttribute("data-focus-cc", tri.dataset.cc);
    });
    tri.addEventListener("mouseleave", () => {
      if (!sticky) svg.removeAttribute("data-focus-cc");
    });
  });

  // --- Symmetry orbits: hovering a point highlights its orbit -------------
  const circles = [...svg.querySelectorAll(".points circle")];
  circles.forEach(c => {
    c.addEventListener("mouseenter", () => {
      const o = c.dataset.orbit;
      circles.forEach(x => x.classList.toggle("orbit-hl", x.dataset.orbit === o));
    });
    c.addEventListener("mouseleave", () => {
      circles.forEach(x => x.classList.remove("orbit-hl"));
    });
  });

  // --- Symmetry elements (axes, rotation center): static toggle -----------
  const symLayer = svg.querySelector("g.sym");
  const toggle = controls.querySelector('[data-sym="axes"]');
  if (symLayer && toggle) {
    let on = false;
    toggle.addEventListener("click", () => {
      on = !on;
      toggle.setAttribute("aria-pressed", String(on));
      symLayer.style.display = on ? "inline" : "";
    });
  }
}
