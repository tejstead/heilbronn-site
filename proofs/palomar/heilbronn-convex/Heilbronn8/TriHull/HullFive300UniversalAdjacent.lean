import Heilbronn8.Cover
import Heilbronn8.TriHull.HullFive300
import Heilbronn8.TriHull.HullFive300UniversalAdjacentScalar

set_option maxHeartbeats 0

/-!
# Geometry adapter for the full adjacent hull-five chart

The labels are fixed as

`A = 0, B = 1, X = 4, C = 2, D = 3, P = 5, Q = 6, R = 7`.

Unlike the older six-sign adapter, this theorem does not assume any central or
outer determinant sign.  It normalizes the geometric rows and lets the scalar
dispatcher force and split all remaining signs.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- Occupancy data for the full adjacent chart.  The last twelve fields are
the positive fan, ear, and cross triangles used by the scalar closures. -/
structure HullFive300AdjacentCell (v : Fin 8 → Point) : Prop where
  abc_pos : 0 < sig (v 0) (v 1) (v 2)
  p_in_abc : InTriStrict (v 5) (v 0) (v 1) (v 2)
  q_in_pbc : InTriStrict (v 6) (v 5) (v 1) (v 2)
  r_in_pca : InTriStrict (v 7) (v 5) (v 2) (v 0)
  qbx_pos : 0 < sig (v 6) (v 1) (v 4)
  qxc_pos : 0 < sig (v 6) (v 4) (v 2)
  rcd_pos : 0 < sig (v 7) (v 2) (v 3)
  rda_pos : 0 < sig (v 7) (v 3) (v 0)
  pbx_pos : 0 < sig (v 5) (v 1) (v 4)
  pxc_pos : 0 < sig (v 5) (v 4) (v 2)
  pcd_pos : 0 < sig (v 5) (v 2) (v 3)
  pda_pos : 0 < sig (v 5) (v 3) (v 0)
  bxc_pos : 0 < sig (v 1) (v 4) (v 2)
  cda_pos : 0 < sig (v 2) (v 3) (v 0)
  rxc_pos : 0 < sig (v 7) (v 4) (v 2)
  qcd_pos : 0 < sig (v 6) (v 2) (v 3)

private lemma two_le_scaledSig_of_pos
    (v : Fin 8 → Point) (hm : 0 < minTri v)
    {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpos : 0 < sig (v i) (v j) (v k)) :
    2 ≤ (2 / minTri v) * sig (v i) (v j) (v k) := by
  have hmin := minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
  rw [abs_of_pos hpos] at hmin
  have hscale : 0 < (2 / minTri v) := div_pos (by norm_num) hm
  have hscaleMin : (2 / minTri v) * minTri v = 2 := by
    field_simp [ne_of_gt hm]
  calc
    2 = (2 / minTri v) * minTri v := hscaleMin.symm
    _ ≤ (2 / minTri v) * sig (v i) (v j) (v k) :=
      mul_le_mul_of_nonneg_left hmin hscale.le

private lemma two_le_abs_scaledSig
    (v : Fin 8 → Point) (hm : 0 < minTri v)
    {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    2 ≤ |(2 / minTri v) * sig (v i) (v j) (v k)| := by
  have hmin := minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
  have hscale : 0 < (2 / minTri v) := div_pos (by norm_num) hm
  have hscaleMin : (2 / minTri v) * minTri v = 2 := by
    field_simp [ne_of_gt hm]
  calc
    2 = (2 / minTri v) * minTri v := hscaleMin.symm
    _ ≤ (2 / minTri v) * |sig (v i) (v j) (v k)| :=
      mul_le_mul_of_nonneg_left hmin hscale.le
    _ = |(2 / minTri v) * sig (v i) (v j) (v k)| := by
      rw [abs_mul, abs_of_pos hscale]

/-- The full adjacent chart forces the target fan bound without any explicit
central or outer sign hypothesis. -/
theorem hullFive300_adjacent_forces_fan_bound
    (v : Fin 8 → Point) (hm : 0 < minTri v)
    (hcell : HullFive300AdjacentCell v) :
    minTri v * 25 ≤
      2 * (sig (v 5) (v 1) (v 4) +
        sig (v 5) (v 4) (v 2) +
        sig (v 5) (v 2) (v 3) +
        sig (v 5) (v 3) (v 0) +
        sig (v 5) (v 0) (v 1)) := by
  let scale : ℝ := 2 / minTri v
  let n : Fin 8 → Fin 8 → Fin 8 → ℝ :=
    fun i j k ↦ scale * sig (v i) (v j) (v k)

  let alpha : ℝ := n 5 1 2
  let beta : ℝ := n 5 2 0
  let a : ℝ := n 5 1 6
  let b : ℝ := n 5 6 2
  let c : ℝ := n 6 1 2
  let d : ℝ := n 5 2 7
  let e : ℝ := n 5 7 0
  let f : ℝ := n 7 2 0
  let g : ℝ := n 5 0 1
  let x : ℝ := n 6 1 4
  let y : ℝ := n 6 4 2
  let z : ℝ := n 7 2 3
  let w : ℝ := n 7 3 0
  let p : ℝ := n 0 5 6
  let Q : ℝ := n 1 7 5
  let Delta : ℝ := n 5 6 7
  let A : ℝ := n 0 6 7
  let B : ℝ := n 1 6 7
  let N : ℝ := n 2 7 6
  let W : ℝ := g + p + Q - Delta
  let T : ℝ := alpha + beta + g
  let delta : ℝ := n 4 5 6
  let tau : ℝ := n 7 5 3
  let axr : ℝ := n 0 4 7
  let bqd : ℝ := n 1 6 3
  let u : ℝ := n 5 1 4
  let V : ℝ := n 5 4 2
  let k : ℝ := n 5 2 3
  let l : ℝ := n 5 3 0
  let E : ℝ := n 1 4 2
  let F : ℝ := n 2 3 0
  let ellR : ℝ := n 7 4 2
  let ellL : ℝ := n 6 2 3
  let xi : ℝ := n 4 6 7
  let eta : ℝ := n 3 6 7
  let H : ℝ := scale *
    (sig (v 5) (v 1) (v 4) +
      sig (v 5) (v 4) (v 2) +
      sig (v 5) (v 2) (v 3) +
      sig (v 5) (v 3) (v 0) +
      sig (v 5) (v 0) (v 1))

  have hfloor (i j k : Fin 8)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hpos : 0 < sig (v i) (v j) (v k)) : 2 ≤ n i j k := by
    simpa only [n, scale] using
      two_le_scaledSig_of_pos v hm hij hik hjk hpos
  have habsFloor (i j k : Fin 8)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      2 ≤ |n i j k| := by
    simpa only [n, scale] using
      two_le_abs_scaledSig v hm hij hik hjk

  obtain ⟨halphaPos, hbetaPos, hgPos⟩ :=
    inTriStrict_fan_pos hcell.abc_pos hcell.p_in_abc
  obtain ⟨hcPos, hbRotPos, haRotPos⟩ :=
    inTriStrict_fan_pos halphaPos hcell.q_in_pbc
  have haPos : 0 < sig (v 5) (v 1) (v 6) := by
    rwa [sig_rotate (v 6) (v 5) (v 1)] at haRotPos
  have hbPos : 0 < sig (v 5) (v 6) (v 2) := by
    rwa [sig_rotate (v 5) (v 6) (v 2)]
  obtain ⟨hfPos, heRotPos, hdRotPos⟩ :=
    inTriStrict_fan_pos hbetaPos hcell.r_in_pca
  have hdPos : 0 < sig (v 5) (v 2) (v 7) := by
    rwa [sig_rotate (v 7) (v 5) (v 2)] at hdRotPos
  have hePos : 0 < sig (v 5) (v 7) (v 0) := by
    rwa [sig_rotate (v 5) (v 7) (v 0)]

  have ha : 2 ≤ a := hfloor 5 1 6 (by decide) (by decide) (by decide) haPos
  have hb : 2 ≤ b := hfloor 5 6 2 (by decide) (by decide) (by decide) hbPos
  have hc : 2 ≤ c := hfloor 6 1 2 (by decide) (by decide) (by decide) hcPos
  have hd : 2 ≤ d := hfloor 5 2 7 (by decide) (by decide) (by decide) hdPos
  have he : 2 ≤ e := hfloor 5 7 0 (by decide) (by decide) (by decide) hePos
  have hf : 2 ≤ f := hfloor 7 2 0 (by decide) (by decide) (by decide) hfPos
  have hg : 2 ≤ g := hfloor 5 0 1 (by decide) (by decide) (by decide) hgPos
  have hx : 2 ≤ x :=
    hfloor 6 1 4 (by decide) (by decide) (by decide) hcell.qbx_pos
  have hy : 2 ≤ y :=
    hfloor 6 4 2 (by decide) (by decide) (by decide) hcell.qxc_pos
  have hz : 2 ≤ z :=
    hfloor 7 2 3 (by decide) (by decide) (by decide) hcell.rcd_pos
  have hw : 2 ≤ w :=
    hfloor 7 3 0 (by decide) (by decide) (by decide) hcell.rda_pos
  have hu : 2 ≤ u :=
    hfloor 5 1 4 (by decide) (by decide) (by decide) hcell.pbx_pos
  have hV : 2 ≤ V :=
    hfloor 5 4 2 (by decide) (by decide) (by decide) hcell.pxc_pos
  have hk : 2 ≤ k :=
    hfloor 5 2 3 (by decide) (by decide) (by decide) hcell.pcd_pos
  have hl : 2 ≤ l :=
    hfloor 5 3 0 (by decide) (by decide) (by decide) hcell.pda_pos
  have hE : 2 ≤ E :=
    hfloor 1 4 2 (by decide) (by decide) (by decide) hcell.bxc_pos
  have hF : 2 ≤ F :=
    hfloor 2 3 0 (by decide) (by decide) (by decide) hcell.cda_pos
  have hellR : 2 ≤ ellR :=
    hfloor 7 4 2 (by decide) (by decide) (by decide) hcell.rxc_pos
  have hellL : 2 ≤ ellL :=
    hfloor 6 2 3 (by decide) (by decide) (by decide) hcell.qcd_pos

  have hpAbs : 2 ≤ |p| := habsFloor 0 5 6 (by decide) (by decide) (by decide)
  have hQAbs : 2 ≤ |Q| := habsFloor 1 7 5 (by decide) (by decide) (by decide)
  have hDeltaAbs : 2 ≤ |Delta| :=
    habsFloor 5 6 7 (by decide) (by decide) (by decide)
  have hAAbs : 2 ≤ |A| := habsFloor 0 6 7 (by decide) (by decide) (by decide)
  have hBAbs : 2 ≤ |B| := habsFloor 1 6 7 (by decide) (by decide) (by decide)
  have hNAbs : 2 ≤ |N| := habsFloor 2 7 6 (by decide) (by decide) (by decide)
  have hdeltaAbs : 2 ≤ |delta| :=
    habsFloor 4 5 6 (by decide) (by decide) (by decide)
  have htauAbs : 2 ≤ |tau| := habsFloor 7 5 3 (by decide) (by decide) (by decide)
  have haxrAbs : 2 ≤ |axr| := habsFloor 0 4 7 (by decide) (by decide) (by decide)
  have hbqdAbs : 2 ≤ |bqd| := habsFloor 1 6 3 (by decide) (by decide) (by decide)
  have hxiAbs : 2 ≤ |xi| := habsFloor 4 6 7 (by decide) (by decide) (by decide)
  have hetaAbs : 2 ≤ |eta| := habsFloor 3 6 7 (by decide) (by decide) (by decide)

  have halpha : alpha = a + b + c := by
    dsimp [alpha, a, b, c, n, scale]
    simp only [sig]
    ring
  have hbeta : beta = d + e + f := by
    dsimp [beta, d, e, f, n, scale]
    simp only [sig]
    ring
  have hT : T = alpha + beta + g := by rfl
  have hH : H = a + b + d + e + x + y + z + w + g := by
    dsimp [H, a, b, d, e, x, y, z, w, g, n]
    simp only [sig]
    ring
  have huDef : u = a + x + delta := by
    dsimp [u, a, x, delta, n, scale]
    simp only [sig]
    ring
  have hVDef : V = b + y - delta := by
    dsimp [V, b, y, delta, n, scale]
    simp only [sig]
    ring
  have hkDef : k = d + z - tau := by
    dsimp [k, d, z, tau, n, scale]
    simp only [sig]
    ring
  have hlDef : l = e + w + tau := by
    dsimp [l, e, w, tau, n, scale]
    simp only [sig]
    ring
  have hEDef : E = x + y - c := by
    dsimp [E, x, y, c, n, scale]
    simp only [sig]
    ring
  have hFDef : F = z + w - f := by
    dsimp [F, z, w, f, n, scale]
    simp only [sig]
    ring

  have hAPQ : alpha * p = a * beta - b * g := by
    dsimp [alpha, p, a, beta, b, g, n, scale]
    simp only [sig]
    ring
  have hBRP : beta * Q = e * alpha - d * g := by
    dsimp [beta, Q, e, alpha, d, g, n, scale]
    simp only [sig]
    ring
  have hDeltaLeft : alpha * Delta = a * d + b * Q := by
    dsimp [alpha, Delta, a, d, b, Q, n, scale]
    simp only [sig]
    ring
  have hDeltaRight : beta * Delta = b * e + d * p := by
    dsimp [beta, Delta, b, e, d, p, n, scale]
    simp only [sig]
    ring
  have hADef : A = Delta + e - p := by
    dsimp [A, Delta, e, p, n, scale]
    simp only [sig]
    ring
  have hBDef : B = Delta + a - Q := by
    dsimp [B, Delta, a, Q, n, scale]
    simp only [sig]
    ring
  have hND : N + Delta = b + d := by
    dsimp [N, Delta, b, d, n, scale]
    simp only [sig]
    ring
  have hWDef : W = g + p + Q - Delta := by rfl
  have hTcentral : T = A + B + c + f + N + W := by
    dsimp [T, W, alpha, beta, A, B, c, f, N, g, p, Q, Delta, n, scale]
    simp only [sig]
    ring
  have hNW : N * W = A * (B + c) + B * f := by
    dsimp [N, W, A, B, c, f, g, p, Q, Delta, n, scale]
    simp only [sig]
    ring
  have hDW : Delta * W = A * a + B * e - A * B := by
    dsimp [Delta, W, A, a, B, e, g, p, Q, n, scale]
    simp only [sig]
    ring
  have haN : a * N = b * B + c * Delta := by
    dsimp [a, N, b, B, c, Delta, n, scale]
    simp only [sig]
    ring
  have heN : e * N = d * A + f * Delta := by
    dsimp [e, N, d, A, f, Delta, n, scale]
    simp only [sig]
    ring
  have hae : a * e = p * Q + g * Delta := by
    dsimp [a, e, p, Q, g, Delta, n, scale]
    simp only [sig]
    ring

  have hfanQ : b * x = a * y + c * delta := by
    dsimp [b, x, a, y, c, delta, n, scale]
    simp only [sig]
    ring
  have hfanR : d * w = e * z + f * tau := by
    dsimp [d, w, e, z, f, tau, n, scale]
    simp only [sig]
    ring
  have hEllR : b * ellR = N * V - d * y := by
    dsimp [b, ellR, N, V, d, y, n, scale]
    simp only [sig]
    ring
  have hEllL : d * ellL = N * k - b * z := by
    dsimp [d, ellL, N, k, b, z, n, scale]
    simp only [sig]
    ring
  have hAXR : b * axr = V * A - delta * f - y * e := by
    dsimp [b, axr, V, A, delta, f, y, e, n, scale]
    simp only [sig]
    ring
  have hBQD : d * bqd = k * B - tau * c - z * a := by
    dsimp [d, bqd, k, B, tau, c, z, a, n, scale]
    simp only [sig]
    ring
  have hAXRendpoint :
      a * axr = u * A - x * e - delta * (g + Q + e) := by
    dsimp [a, axr, u, A, x, e, delta, g, Q, n, scale]
    simp only [sig]
    ring
  have hBQDendpoint :
      e * bqd = l * B - w * a - tau * (g + a + p) := by
    dsimp [e, bqd, l, B, w, a, tau, g, p, n, scale]
    simp only [sig]
    ring
  have hXiN : b * xi = -N * delta - y * Delta := by
    dsimp [b, xi, N, delta, y, Delta, n, scale]
    simp only [sig]
    ring
  have hXiC : c * xi = B * y - N * x := by
    dsimp [c, xi, B, y, N, x, n, scale]
    simp only [sig]
    ring
  have hXiB : -B * delta = a * xi + x * Delta := by
    dsimp [B, delta, a, xi, x, Delta, n, scale]
    simp only [sig]
    ring
  have hEtaN : d * eta = -N * tau - z * Delta := by
    dsimp [d, eta, N, tau, z, Delta, n, scale]
    simp only [sig]
    ring
  have hEtaF : f * eta = A * z - N * w := by
    dsimp [f, eta, A, z, N, w, n, scale]
    simp only [sig]
    ring
  have hEtaA : -A * tau = e * eta + w * Delta := by
    dsimp [A, tau, e, eta, w, Delta, n, scale]
    simp only [sig]
    ring

  have hscalar : 25 ≤ H :=
    hullFive300_adjacent_scalar
      (a := a) (b := b) (c := c) (d := d) (e := e) (f := f) (g := g)
      (x := x) (y := y) (z := z) (w := w)
      (alpha := alpha) (beta := beta) (T := T)
      (p := p) (Q := Q) (Delta := Delta) (A := A) (B := B) (N := N)
      (W := W) (delta := delta) (tau := tau) (axr := axr) (bqd := bqd)
      (u := u) (V := V) (k := k) (l := l) (E := E) (F := F)
      (ellR := ellR) (ellL := ellL) (xi := xi) (eta := eta) (H := H)
      ha hb hc hd he hf hg hx hy hz hw hu hV hk hl hE hF hellR hellL
      hpAbs hQAbs hDeltaAbs hAAbs hBAbs hNAbs
      hdeltaAbs htauAbs haxrAbs hbqdAbs hxiAbs hetaAbs
      halpha hbeta hT hH huDef hVDef hkDef hlDef hEDef hFDef
      hAPQ hBRP hDeltaLeft hDeltaRight hADef hBDef hND hWDef
      hTcentral hNW hDW haN heN hae hfanQ hfanR hEllR hEllL
      hAXR hBQD hAXRendpoint hBQDendpoint hXiN hXiC hXiB
      hEtaN hEtaF hEtaA

  have hminScale : minTri v * scale = 2 := by
    dsimp [scale]
    field_simp [ne_of_gt hm]
  calc
    minTri v * 25 ≤ minTri v * H :=
      mul_le_mul_of_nonneg_left hscalar hm.le
    _ = 2 * (sig (v 5) (v 1) (v 4) +
        sig (v 5) (v 4) (v 2) +
        sig (v 5) (v 2) (v 3) +
        sig (v 5) (v 3) (v 0) +
        sig (v 5) (v 0) (v 1)) := by
      dsimp [H]
      rw [← mul_assoc, hminScale]

end Heilbronn8.TriHull
