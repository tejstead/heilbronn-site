import Heilbronn8.TriHull.HullFive300RightProfiles
import Heilbronn8.TriHull.HullFive300Cab717Scalar
import Heilbronn8.TriHull.HullFive300Cab717NegativeScalar

/-!
# Geometry bridge for the positive-`DPR` half of CAB type 717

The sequential hull chart is `A-B-X-C-D`.  For a `CAB` packet we rename the
inner points as `P=C` (slot 7), `Q=A` (slot 5), and `R=B` (slot 6).  The
ten signs below are the exceptional type-717 cell left by the central
same-sector census.

This file intentionally proves only the half with `[DPR] > 0`.  That sign is
not forced by the ten central signs, so the theorem name and interface keep
the extra hypothesis explicit.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- The exceptional central CAB sign cell, in the bit order
`BPQ, XPQ, CPQ, BPR, XPR, CPR, BQR, XQR, CQR, PQR`.

Here `P=e 7`, `Q=e 5`, and `R=e 6`. -/
structure HullFive300Cab717InnerSigns
    (v : Configuration) (e : Fin 8 → Fin 8) : Prop where
  bpq_pos : 0 < sig (v (e 1)) (v (e 7)) (v (e 5))
  xpq_neg : sig (v (e 2)) (v (e 7)) (v (e 5)) < 0
  cpq_pos : 0 < sig (v (e 3)) (v (e 7)) (v (e 5))
  bpr_pos : 0 < sig (v (e 1)) (v (e 7)) (v (e 6))
  xpr_neg : sig (v (e 2)) (v (e 7)) (v (e 6)) < 0
  cpr_neg : sig (v (e 3)) (v (e 7)) (v (e 6)) < 0
  bqr_pos : 0 < sig (v (e 1)) (v (e 5)) (v (e 6))
  xqr_pos : 0 < sig (v (e 2)) (v (e 5)) (v (e 6))
  cqr_neg : sig (v (e 3)) (v (e 5)) (v (e 6)) < 0
  pqr_pos : 0 < sig (v (e 7)) (v (e 5)) (v (e 6))

private lemma cab717_minTri_le_sig_of_pos
    (v : Configuration) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpos : 0 < sig (v (e i)) (v (e j)) (v (e k))) :
    minTri v ≤ sig (v (e i)) (v (e j)) (v (e k)) := by
  have hmin := minTri_le_abs_sig_of_pairwise_ne v
    (a := e i) (b := e j) (c := e k)
    (fun h ↦ hij (he h)) (fun h ↦ hik (he h))
    (fun h ↦ hjk (he h))
  simpa [abs_of_pos hpos] using hmin

private lemma cab717_sequential_cycle_pos
    (v : Configuration) (e : Fin 8 → Fin 8)
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (i j k : Fin 5) (hij : i < j) (hjk : j < k) :
    0 < sig
      (v (e (hullFiveSequentialCycleSlot i)))
      (v (e (hullFiveSequentialCycleSlot j)))
      (v (e (hullFiveSequentialCycleSlot k))) :=
  hcyc.pos i j k hij hjk

/-- The exceptional CAB cell forces the hull bound whenever `[DPR] > 0`.

The extra sign is essential: the central type-717 cell itself has realizers
of both `DPR` signs. -/
theorem hullFive300_cab717_packet_bound_of_dpr_pos
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hm : 0 < minTri v)
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (p : HullFiveEndRightProfileC v e 7)
    (q : HullFiveEndRightProfileA v e 5)
    (r : HullFiveEndRightProfileB v e 6)
    (h717 : HullFive300Cab717InnerSigns v e)
    (hDPR : 0 < sig (v (e 4)) (v (e 7)) (v (e 6))) :
    minTri v * 25 ≤ 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) +
        sig (v (e 0)) (v (e 3)) (v (e 4))) := by
  let E := sig (v (e 1)) (v (e 2)) (v (e 3))
  let p0 := sig (v (e 2)) (v (e 3)) (v (e 7))
  let p1 := -sig (v (e 1)) (v (e 3)) (v (e 7))
  let u := sig (v (e 1)) (v (e 2)) (v (e 7))
  let r0 := sig (v (e 2)) (v (e 3)) (v (e 6))
  let s := -sig (v (e 1)) (v (e 3)) (v (e 6))
  let r2 := sig (v (e 1)) (v (e 2)) (v (e 6))
  let j := sig (v (e 1)) (v (e 7)) (v (e 6))
  let g := -sig (v (e 3)) (v (e 7)) (v (e 6))
  let h := -sig (v (e 2)) (v (e 7)) (v (e 6))
  let b := sig (v (e 2)) (v (e 4)) (v (e 7))
  let f := sig (v (e 2)) (v (e 4)) (v (e 6))
  let K := sig (v (e 4)) (v (e 1)) (v (e 2))
  let L := sig (v (e 2)) (v (e 3)) (v (e 4))
  let Z := sig (v (e 1)) (v (e 3)) (v (e 4))
  let W := sig (v (e 0)) (v (e 1)) (v (e 4))
  let T := sig (v (e 0)) (v (e 1)) (v (e 3))
  let F := sig (v (e 0)) (v (e 3)) (v (e 4))
  let H := sig (v (e 0)) (v (e 1)) (v (e 2)) +
    sig (v (e 0)) (v (e 2)) (v (e 3)) + F

  have hEpos : 0 < E := by
    simpa [E, hullFiveSequentialCycleSlot] using
      cab717_sequential_cycle_pos v e hcyc 1 2 3
        (by decide) (by decide)
  have hKpos : 0 < K := by
    have hpos := cab717_sequential_cycle_pos v e hcyc 1 2 4
      (by decide) (by decide)
    dsimp only [K]
    rw [sig_rotate]
    exact hpos
  have hWpos : 0 < W := by
    simpa [W, hullFiveSequentialCycleSlot] using
      cab717_sequential_cycle_pos v e hcyc 0 1 4
        (by decide) (by decide)
  have hTpos : 0 < T := by
    simpa [T, hullFiveSequentialCycleSlot] using
      cab717_sequential_cycle_pos v e hcyc 0 1 3
        (by decide) (by decide)
  have hFpos : 0 < F := by
    simpa [F, hullFiveSequentialCycleSlot] using
      cab717_sequential_cycle_pos v e hcyc 0 3 4
        (by decide) (by decide)

  obtain ⟨_, _, hupos⟩ := inTriStrict_fan_pos hEpos p.bxc
  have hupos' : 0 < u := by
    dsimp only [u]
    rw [← sig_rotate]
    exact hupos

  obtain ⟨hr0pos, hsraw, hr2pos⟩ := inTriStrict_fan_pos hEpos r.bxc
  have hspos : 0 < s := by
    dsimp only [s]
    simp only [sig] at hsraw ⊢
    nlinarith
  have hr0pos' : 0 < r0 := by
    dsimp only [r0]
    rw [← sig_rotate]
    exact hr0pos
  have hr2pos' : 0 < r2 := by
    dsimp only [r2]
    rw [← sig_rotate]
    exact hr2pos

  obtain ⟨_, hfraw, _⟩ := inTriStrict_fan_pos hKpos r.dbx
  have hfpos : 0 < f := by
    dsimp only [f]
    rw [← sig_rotate]
    exact hfraw

  have hjpos : 0 < j := by simpa only [j] using h717.bpr_pos
  have hgpos : 0 < g := by
    dsimp only [g]
    linarith [h717.cpr_neg]
  have hhpos : 0 < h := by
    dsimp only [h]
    linarith [h717.xpr_neg]

  have hu : minTri v ≤ u := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 1) (j := 2) (k := 7)
    (by decide) (by decide) (by decide) hupos'
  have hj : minTri v ≤ j := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 1) (j := 7) (k := 6)
    (by decide) (by decide) (by decide) hjpos
  have hg : minTri v ≤ g := by
    have hpos : 0 < sig (v (e 3)) (v (e 6)) (v (e 7)) := by
      rw [sig_swap]
      exact hgpos
    have hfloor := cab717_minTri_le_sig_of_pos v e e.injective
      (i := 3) (j := 6) (k := 7)
      (by decide) (by decide) (by decide) hpos
    dsimp only [g]
    rw [sig_swap] at hfloor
    exact hfloor
  have hh : minTri v ≤ h := by
    have hpos : 0 < sig (v (e 2)) (v (e 6)) (v (e 7)) := by
      rw [sig_swap]
      exact hhpos
    have hfloor := cab717_minTri_le_sig_of_pos v e e.injective
      (i := 2) (j := 6) (k := 7)
      (by decide) (by decide) (by decide) hpos
    dsimp only [h]
    rw [sig_swap] at hfloor
    exact hfloor
  have hs : minTri v ≤ s := by
    have hpos : 0 < sig (v (e 1)) (v (e 6)) (v (e 3)) := by
      dsimp only [s] at hspos
      rw [sig_swap]
      exact hspos
    have hfloor := cab717_minTri_le_sig_of_pos v e e.injective
      (i := 1) (j := 6) (k := 3)
      (by decide) (by decide) (by decide) hpos
    dsimp only [s]
    rw [sig_swap] at hfloor
    exact hfloor
  have hr0 : minTri v ≤ r0 := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 2) (j := 3) (k := 6)
    (by decide) (by decide) (by decide) hr0pos'
  have hr2floor : minTri v ≤ r2 :=
    cab717_minTri_le_sig_of_pos v e e.injective
      (i := 1) (j := 2) (k := 6)
      (by decide) (by decide) (by decide) hr2pos'
  have hf : minTri v ≤ f := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 2) (j := 4) (k := 6)
    (by decide) (by decide) (by decide) hfpos
  have hW : minTri v ≤ W := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 0) (j := 1) (k := 4)
    (by decide) (by decide) (by decide) hWpos
  have hT : minTri v ≤ T := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 0) (j := 1) (k := 3)
    (by decide) (by decide) (by decide) hTpos
  have hF : minTri v ≤ F := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 0) (j := 3) (k := 4)
    (by decide) (by decide) (by decide) hFpos
  have hDPRfloor := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 4) (j := 7) (k := 6)
    (by decide) (by decide) (by decide) hDPR

  let fE : Fin 6 → Fin 8 := e ∘ ![1, 2, 3, 7, 5, 6]
  have hEfloor : (17 / 2 : ℝ) * minTri v ≤ E := by
    have hthree := threePointTriangle_normalized_lower_bound_unconditional
      v fE (e.injective.comp (by decide)) hm hEpos p.bxc q.bxc r.bxc
    have hscaled := (le_div_iff₀ hm).mp hthree
    simpa [fE, E, Function.comp_apply] using hscaled

  have hE_P : E = p0 + p1 + u := by
    dsimp [E, p0, p1, u]
    simp only [sig]
    ring
  have hE_R : E = r0 + s + r2 := by
    dsimp [E, r0, s, r2]
    simp only [sig]
    ring
  have hp1 : p1 = s + j + g := by
    dsimp [p1, s, j, g]
    simp only [sig]
    ring
  have hsector : r2 = u + j + h := by
    dsimp [r2, u, j, h]
    simp only [sig]
    ring
  have hcentralPair : j * r0 = g * r2 + h * s := by
    dsimp [j, r0, g, r2, h, s]
    simp only [sig]
    ring
  have hpair : E * h = p0 * r2 - u * r0 := by
    dsimp [E, h, p0, r2, u, r0]
    simp only [sig]
    ring
  have hbrow : E * b = K * p0 - L * u := by
    dsimp [E, b, K, p0, L, u]
    simp only [sig]
    ring
  have hfrow : E * f = K * r0 - L * r2 := by
    dsimp [E, f, K, r0, L, r2]
    simp only [sig]
    ring
  have hDPRrow : b = f + h + sig (v (e 4)) (v (e 7)) (v (e 6)) := by
    dsimp [b, f, h]
    simp only [sig]
    ring
  have hDPRineq : f + h + minTri v ≤ b := by
    nlinarith [hDPRfloor, hDPRrow]
  have hZ : Z = K + L - E := by
    dsimp [Z, K, L, E]
    simp only [sig]
    ring
  have hHullCentral : H = E + Z + W := by
    dsimp [H, E, Z, W, F]
    simp only [sig]
    ring
  have hHullEar : H = E + T + F := by
    dsimp [H, E, T, F]
    simp only [sig]
    ring

  have hbound := hullFive300_cab717_hull_bound
    (m := minTri v) (E := E) (p0 := p0) (p1 := p1) (u := u)
    (r0 := r0) (s := s) (r2 := r2) (j := j) (g := g) (h := h)
    (b := b) (f := f) (K := K) (L := L) (Z := Z) (W := W)
    (H := H) (T := T) (F := F)
    hm hu hj hg hh hs hf hr0 hr2floor hW hT hF hEfloor
    hE_P hE_R hp1 hsector hcentralPair hpair hbrow hfrow hDPRineq hZ
    hHullCentral hHullEar
  simpa only [H, F, mul_comm] using hbound

/-- The reflected exceptional cell forces the hull bound when `[AQR] < 0`.

This is the same scalar argument with the signed chart negated and
`(A',B',X',C',D',P',R') = (D,C,X,B,A,Q,R)`.  In particular the scalar
opposite triangle `Z'` is the original `[ABC]`. -/
theorem hullFive300_cab717_packet_bound_of_aqr_neg
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hm : 0 < minTri v)
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (p : HullFiveEndRightProfileC v e 7)
    (q : HullFiveEndRightProfileA v e 5)
    (r : HullFiveEndRightProfileB v e 6)
    (h717 : HullFive300Cab717InnerSigns v e)
    (hAQR : sig (v (e 0)) (v (e 5)) (v (e 6)) < 0) :
    minTri v * 25 ≤ 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) +
        sig (v (e 0)) (v (e 3)) (v (e 4))) := by
  let E := sig (v (e 1)) (v (e 2)) (v (e 3))
  let p0 := -sig (v (e 2)) (v (e 1)) (v (e 5))
  let p1 := sig (v (e 3)) (v (e 1)) (v (e 5))
  let u := -sig (v (e 3)) (v (e 2)) (v (e 5))
  let r0 := -sig (v (e 2)) (v (e 1)) (v (e 6))
  let s := sig (v (e 3)) (v (e 1)) (v (e 6))
  let r2 := -sig (v (e 3)) (v (e 2)) (v (e 6))
  let j := -sig (v (e 3)) (v (e 5)) (v (e 6))
  let g := sig (v (e 1)) (v (e 5)) (v (e 6))
  let h := sig (v (e 2)) (v (e 5)) (v (e 6))
  let b := -sig (v (e 2)) (v (e 0)) (v (e 5))
  let f := -sig (v (e 2)) (v (e 0)) (v (e 6))
  let K := -sig (v (e 0)) (v (e 3)) (v (e 2))
  let L := -sig (v (e 2)) (v (e 1)) (v (e 0))
  let Z := -sig (v (e 3)) (v (e 1)) (v (e 0))
  let W := sig (v (e 0)) (v (e 3)) (v (e 4))
  let T := sig (v (e 1)) (v (e 3)) (v (e 4))
  let F := sig (v (e 0)) (v (e 1)) (v (e 4))
  let H := sig (v (e 0)) (v (e 1)) (v (e 2)) +
    sig (v (e 0)) (v (e 2)) (v (e 3)) +
    sig (v (e 0)) (v (e 3)) (v (e 4))

  have hEpos : 0 < E := by
    simpa [E, hullFiveSequentialCycleSlot] using
      cab717_sequential_cycle_pos v e hcyc 1 2 3
        (by decide) (by decide)
  have hAXCpos :
      0 < sig (v (e 0)) (v (e 2)) (v (e 3)) := by
    simpa [hullFiveSequentialCycleSlot] using
      cab717_sequential_cycle_pos v e hcyc 0 2 3
        (by decide) (by decide)
  have hWpos : 0 < W := by
    simpa [W, hullFiveSequentialCycleSlot] using
      cab717_sequential_cycle_pos v e hcyc 0 3 4
        (by decide) (by decide)
  have hTpos : 0 < T := by
    simpa [T, hullFiveSequentialCycleSlot] using
      cab717_sequential_cycle_pos v e hcyc 1 3 4
        (by decide) (by decide)
  have hFpos : 0 < F := by
    simpa [F, hullFiveSequentialCycleSlot] using
      cab717_sequential_cycle_pos v e hcyc 0 1 4
        (by decide) (by decide)

  obtain ⟨hq0, _, _⟩ := inTriStrict_fan_pos hEpos q.bxc
  obtain ⟨rr0, rs, rr2⟩ := inTriStrict_fan_pos hEpos r.bxc
  obtain ⟨_, _, rf⟩ := inTriStrict_fan_pos hAXCpos r.axc

  have huRaw := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 5) (j := 2) (k := 3)
    (by decide) (by decide) (by decide) hq0
  have hu : minTri v ≤ u := by
    dsimp only [u]
    simp only [sig] at huRaw ⊢
    nlinarith
  have hjpos : 0 < sig (v (e 3)) (v (e 6)) (v (e 5)) := by
    rw [sig_swap]
    linarith [h717.cqr_neg]
  have hjRaw := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 3) (j := 6) (k := 5)
    (by decide) (by decide) (by decide) hjpos
  have hj : minTri v ≤ j := by
    dsimp only [j]
    rw [sig_swap] at hjRaw
    exact hjRaw
  have hg : minTri v ≤ g :=
    cab717_minTri_le_sig_of_pos v e e.injective
      (i := 1) (j := 5) (k := 6)
      (by decide) (by decide) (by decide) h717.bqr_pos
  have hh : minTri v ≤ h :=
    cab717_minTri_le_sig_of_pos v e e.injective
      (i := 2) (j := 5) (k := 6)
      (by decide) (by decide) (by decide) h717.xqr_pos
  have hsRaw := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 6) (j := 3) (k := 1)
    (by decide) (by decide) (by decide) rs
  have hs : minTri v ≤ s := by
    dsimp only [s]
    simp only [sig] at hsRaw ⊢
    nlinarith
  have hr0Raw := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 6) (j := 1) (k := 2)
    (by decide) (by decide) (by decide) rr2
  have hr0 : minTri v ≤ r0 := by
    dsimp only [r0]
    simp only [sig] at hr0Raw ⊢
    nlinarith
  have hr2Raw := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 6) (j := 2) (k := 3)
    (by decide) (by decide) (by decide) rr0
  have hr2floor : minTri v ≤ r2 := by
    dsimp only [r2]
    simp only [sig] at hr2Raw ⊢
    nlinarith
  have hfRaw := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 6) (j := 0) (k := 2)
    (by decide) (by decide) (by decide) rf
  have hf : minTri v ≤ f := by
    dsimp only [f]
    simp only [sig] at hfRaw ⊢
    nlinarith
  have hW : minTri v ≤ W := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 0) (j := 3) (k := 4)
    (by decide) (by decide) (by decide) hWpos
  have hT : minTri v ≤ T := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 1) (j := 3) (k := 4)
    (by decide) (by decide) (by decide) hTpos
  have hF : minTri v ≤ F := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 0) (j := 1) (k := 4)
    (by decide) (by decide) (by decide) hFpos
  have hAQRpos : 0 < sig (v (e 0)) (v (e 6)) (v (e 5)) := by
    rw [sig_swap]
    linarith [hAQR]
  have hAQRfloor := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 0) (j := 6) (k := 5)
    (by decide) (by decide) (by decide) hAQRpos
  rw [sig_swap] at hAQRfloor

  let fE : Fin 6 → Fin 8 := e ∘ ![1, 2, 3, 7, 5, 6]
  have hEfloor : (17 / 2 : ℝ) * minTri v ≤ E := by
    have hthree := threePointTriangle_normalized_lower_bound_unconditional
      v fE (e.injective.comp (by decide)) hm hEpos p.bxc q.bxc r.bxc
    have hscaled := (le_div_iff₀ hm).mp hthree
    simpa [fE, E, Function.comp_apply] using hscaled

  have hE_P : E = p0 + p1 + u := by
    dsimp [E, p0, p1, u]
    simp only [sig]
    ring
  have hE_R : E = r0 + s + r2 := by
    dsimp [E, r0, s, r2]
    simp only [sig]
    ring
  have hp1 : p1 = s + j + g := by
    dsimp [p1, s, j, g]
    simp only [sig]
    ring
  have hsector : r2 = u + j + h := by
    dsimp [r2, u, j, h]
    simp only [sig]
    ring
  have hcentralPair : j * r0 = g * r2 + h * s := by
    dsimp [j, r0, g, r2, h, s]
    simp only [sig]
    ring
  have hpair : E * h = p0 * r2 - u * r0 := by
    dsimp [E, h, p0, r2, u, r0]
    simp only [sig]
    ring
  have hbrow : E * b = K * p0 - L * u := by
    dsimp [E, b, K, p0, L, u]
    simp only [sig]
    ring
  have hfrow : E * f = K * r0 - L * r2 := by
    dsimp [E, f, K, r0, L, r2]
    simp only [sig]
    ring
  have hAQRrow :
      b = f + h - sig (v (e 0)) (v (e 5)) (v (e 6)) := by
    dsimp [b, f, h]
    simp only [sig]
    ring
  have hDPRineq : f + h + minTri v ≤ b := by
    linarith only [hAQRfloor, hAQRrow]
  have hZ : Z = K + L - E := by
    dsimp [Z, K, L, E]
    simp only [sig]
    ring
  have hHullCentral : H = E + Z + W := by
    dsimp [H, E, Z, W]
    simp only [sig]
    ring
  have hHullEar : H = E + T + F := by
    dsimp [H, E, T, F]
    simp only [sig]
    ring

  have hbound := hullFive300_cab717_hull_bound
    (m := minTri v) (E := E) (p0 := p0) (p1 := p1) (u := u)
    (r0 := r0) (s := s) (r2 := r2) (j := j) (g := g) (h := h)
    (b := b) (f := f) (K := K) (L := L) (Z := Z) (W := W)
    (H := H) (T := T) (F := F)
    hm hu hj hg hh hs hf hr0 hr2floor hW hT hF hEfloor
    hE_P hE_R hp1 hsector hcentralPair hpair hbrow hfrow hDPRineq hZ
    hHullCentral hHullEar
  simpa only [H, mul_comm] using hbound

/-- The remaining mixed outer-sign cell, `[DPR] < 0 < [AQR]`.

The proof exposes the two fan remainders
`beta = [ABX] - [PXA]` and `delta = [XCD] - [QDX]`.  The two pair rows and
the two outer-sign rows are exactly the hypotheses of
`hullFive300_cab717_negative_hull_bound`. -/
theorem hullFive300_cab717_packet_bound_of_dpr_neg_aqr_pos
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hm : 0 < minTri v)
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (p : HullFiveEndRightProfileC v e 7)
    (q : HullFiveEndRightProfileA v e 5)
    (r : HullFiveEndRightProfileB v e 6)
    (_h717 : HullFive300Cab717InnerSigns v e)
    (hDPR : sig (v (e 4)) (v (e 7)) (v (e 6)) < 0)
    (hAQR : 0 < sig (v (e 0)) (v (e 5)) (v (e 6))) :
    minTri v * 25 ≤ 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) +
        sig (v (e 0)) (v (e 3)) (v (e 4))) := by
  let U := sig (v (e 0)) (v (e 1)) (v (e 2))
  let V := sig (v (e 0)) (v (e 2)) (v (e 3))
  let K := sig (v (e 4)) (v (e 1)) (v (e 2))
  let L := sig (v (e 2)) (v (e 3)) (v (e 4))
  let N := sig (v (e 2)) (v (e 4)) (v (e 0))
  let a := sig (v (e 7)) (v (e 2)) (v (e 0))
  let b := sig (v (e 7)) (v (e 2)) (v (e 4))
  let c := sig (v (e 5)) (v (e 0)) (v (e 2))
  let d := sig (v (e 5)) (v (e 4)) (v (e 2))
  let ea := sig (v (e 6)) (v (e 0)) (v (e 2))
  let f := sig (v (e 6)) (v (e 2)) (v (e 4))
  let y := sig (v (e 7)) (v (e 1)) (v (e 2))
  let qab := sig (v (e 7)) (v (e 0)) (v (e 1))
  let qxc := sig (v (e 5)) (v (e 2)) (v (e 3))
  let qcd := sig (v (e 5)) (v (e 3)) (v (e 4))
  let rda := sig (v (e 6)) (v (e 4)) (v (e 0))
  let beta := U - a
  let delta := L - d
  let H := sig (v (e 0)) (v (e 1)) (v (e 2)) +
    sig (v (e 0)) (v (e 2)) (v (e 3)) +
    sig (v (e 0)) (v (e 3)) (v (e 4))

  have hUpos : 0 < U := by
    simpa [U, hullFiveSequentialCycleSlot] using
      cab717_sequential_cycle_pos v e hcyc 0 1 2
        (by decide) (by decide)
  have hVpos : 0 < V := by
    simpa [V, hullFiveSequentialCycleSlot] using
      cab717_sequential_cycle_pos v e hcyc 0 2 3
        (by decide) (by decide)
  have hKpos : 0 < K := by
    have hpos := cab717_sequential_cycle_pos v e hcyc 1 2 4
      (by decide) (by decide)
    dsimp only [K]
    rw [sig_rotate]
    exact hpos
  have hLpos : 0 < L := by
    simpa [L, hullFiveSequentialCycleSlot] using
      cab717_sequential_cycle_pos v e hcyc 2 3 4
        (by decide) (by decide)
  have hNpos : 0 < N := by
    have hpos := cab717_sequential_cycle_pos v e hcyc 0 2 4
      (by decide) (by decide)
    dsimp only [N]
    rw [sig_rotate, sig_rotate]
    exact hpos

  obtain ⟨hypos, hapos, hqabpos⟩ := inTriStrict_fan_pos hUpos p.abx
  obtain ⟨_, hbpos, _⟩ := inTriStrict_fan_pos hKpos p.dbx
  obtain ⟨hqxcpos, hqcapos, hcpos⟩ := inTriStrict_fan_pos hVpos q.axc
  obtain ⟨hqcdpos, hdpos, _⟩ := inTriStrict_fan_pos hLpos q.xcd
  obtain ⟨hrdapos, hepos, hfpos⟩ := inTriStrict_fan_pos hNpos r.xda

  have ha : minTri v ≤ a := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 7) (j := 2) (k := 0)
    (by decide) (by decide) (by decide) hapos
  have hb : minTri v ≤ b := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 7) (j := 2) (k := 4)
    (by decide) (by decide) (by decide) hbpos
  have hc : minTri v ≤ c := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 5) (j := 0) (k := 2)
    (by decide) (by decide) (by decide) hcpos
  have hd : minTri v ≤ d := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 5) (j := 4) (k := 2)
    (by decide) (by decide) (by decide) hdpos
  have he : minTri v ≤ ea := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 6) (j := 0) (k := 2)
    (by decide) (by decide) (by decide) hepos
  have hf : minTri v ≤ f := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 6) (j := 2) (k := 4)
    (by decide) (by decide) (by decide) hfpos
  have hy : minTri v ≤ y := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 7) (j := 1) (k := 2)
    (by decide) (by decide) (by decide) hypos
  have hqab : minTri v ≤ qab := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 7) (j := 0) (k := 1)
    (by decide) (by decide) (by decide) hqabpos
  have hqxc : minTri v ≤ qxc := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 5) (j := 2) (k := 3)
    (by decide) (by decide) (by decide) hqxcpos
  have hqca : minTri v ≤ sig (v (e 5)) (v (e 3)) (v (e 0)) :=
    cab717_minTri_le_sig_of_pos v e e.injective
      (i := 5) (j := 3) (k := 0)
      (by decide) (by decide) (by decide) hqcapos
  have hqcd : minTri v ≤ qcd := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 5) (j := 3) (k := 4)
    (by decide) (by decide) (by decide) hqcdpos
  have hrda : minTri v ≤ rda := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 6) (j := 4) (k := 0)
    (by decide) (by decide) (by decide) hrdapos

  have hUfan : U = y + a + qab := by
    dsimp [U, y, a, qab]
    simp only [sig]
    ring
  have hKfan :
      K = y + b + sig (v (e 7)) (v (e 4)) (v (e 1)) := by
    dsimp [K, y, b]
    simp only [sig]
    ring
  have hPDB : minTri v ≤ sig (v (e 7)) (v (e 4)) (v (e 1)) := by
    obtain ⟨_, _, hpdbpos⟩ := inTriStrict_fan_pos hKpos p.dbx
    exact cab717_minTri_le_sig_of_pos v e e.injective
      (i := 7) (j := 4) (k := 1)
      (by decide) (by decide) (by decide) hpdbpos
  have hVfan :
      V = qxc + sig (v (e 5)) (v (e 3)) (v (e 0)) + c := by
    dsimp [V, qxc, c]
    simp only [sig]
    ring
  have hLfan : L = qcd + d + qxc := by
    dsimp [L, qcd, d, qxc]
    simp only [sig]
    ring
  have hNfan : N = rda + ea + f := by
    dsimp [N, rda, ea, f]
    simp only [sig]
    ring

  have hbeta : 2 * minTri v ≤ beta := by
    dsimp only [beta]
    nlinarith [hUfan, hy, hqab]
  have hdelta : 2 * minTri v ≤ delta := by
    dsimp only [delta]
    nlinarith [hLfan, hqcd, hqxc]
  have hKgap : b + 2 * minTri v ≤ K := by
    linarith only [hKfan, hy, hPDB]
  have hVgap : c + 2 * minTri v ≤ V := by
    linarith only [hVfan, hqxc, hqca]

  have hyrow : U * b - K * a = N * y := by
    dsimp [U, b, K, a, N, y]
    simp only [sig]
    ring
  have hqrow : L * c - V * d = N * qxc := by
    dsimp [L, c, V, d, N, qxc]
    simp only [sig]
    ring
  have hDPRrow :
      b * ea + a * f - N * (b - f) =
        -N * sig (v (e 4)) (v (e 7)) (v (e 6)) := by
    dsimp [b, ea, a, f, N]
    simp only [sig]
    ring
  have hAQRrow :
      N * (ea - c) + d * ea + c * f =
        N * sig (v (e 0)) (v (e 5)) (v (e 6)) := by
    dsimp [N, ea, c, d, f]
    simp only [sig]
    ring

  have hDPRpos : 0 < sig (v (e 4)) (v (e 6)) (v (e 7)) := by
    rw [sig_swap]
    linarith [hDPR]
  have hDPRfloorRaw := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 4) (j := 6) (k := 7)
    (by decide) (by decide) (by decide) hDPRpos
  have hDPRfloor :
      minTri v ≤ -sig (v (e 4)) (v (e 7)) (v (e 6)) := by
    rw [sig_swap] at hDPRfloorRaw
    exact hDPRfloorRaw
  have hAQRfloor := cab717_minTri_le_sig_of_pos v e e.injective
    (i := 0) (j := 5) (k := 6)
    (by decide) (by decide) (by decide) hAQR

  have hN0 : 0 ≤ N := hNpos.le
  have hyN := mul_le_mul_of_nonneg_left hy hN0
  have hqN := mul_le_mul_of_nonneg_left hqxc hN0
  have hDPRN := mul_le_mul_of_nonneg_right hDPRfloor hN0
  have hAQRN := mul_le_mul_of_nonneg_right hAQRfloor hN0
  have ha0 : 0 ≤ a := le_trans hm.le ha
  have hd0 : 0 ≤ d := le_trans hm.le hd
  have hKamul := mul_le_mul_of_nonneg_right hKgap ha0
  have hVdmul := mul_le_mul_of_nonneg_right hVgap hd0
  have hUbeta : U = a + beta := by
    dsimp only [beta]
    ring
  have hLdelta : L = d + delta := by
    dsimp only [delta]
    ring
  have hUbeta_b : U * b = (a + beta) * b := by rw [hUbeta]
  have hLdelta_c : L * c = (d + delta) * c := by rw [hLdelta]
  have hbetab : minTri v * (N + 2 * a) ≤ beta * b := by
    nlinarith only [hyrow, hyN, hKamul, hUbeta_b]
  have hdeltac : minTri v * (N + 2 * d) ≤ delta * c := by
    nlinarith only [hqrow, hqN, hVdmul, hLdelta_c]

  have hDPRlower :
      minTri v * N ≤ b * ea + a * f - N * (b - f) := by
    nlinarith only [hDPRrow, hDPRN]
  have hAQRlower :
      minTri v * N ≤ N * (ea - c) + d * ea + c * f := by
    nlinarith only [hAQRrow, hAQRN]
  have hDrewrite :
      b * ea + a * f - N * (b - f) =
        f * (a + N) - b * (f + rda) := by
    rw [hNfan]
    ring
  have hArewrite :
      N * (ea - c) + d * ea + c * f =
        ea * (d + N) - c * (ea + rda) := by
    rw [hNfan]
    ring
  have hbcap :
      b * (f + rda) ≤ f * (a + N) - minTri v * N := by
    nlinarith only [hDPRlower, hDrewrite]
  have hccap :
      c * (ea + rda) ≤ ea * (d + N) - minTri v * N := by
    nlinarith only [hAQRlower, hArewrite]

  have hfr0 : 0 ≤ f + rda := by nlinarith only [hf, hrda, hm]
  have her0 : 0 ≤ ea + rda := by nlinarith only [he, hrda, hm]
  have hbeta0 : 0 ≤ beta := by nlinarith only [hbeta, hm]
  have hdelta0 : 0 ≤ delta := by nlinarith only [hdelta, hm]
  have hDleft := mul_le_mul_of_nonneg_right hbetab hfr0
  have hAleft := mul_le_mul_of_nonneg_right hdeltac her0
  have hDright := mul_le_mul_of_nonneg_left hbcap hbeta0
  have hAright := mul_le_mul_of_nonneg_left hccap hdelta0
  have hDcross :
      minTri v * (N + 2 * a) * (f + rda) ≤
        beta * (f * (a + N) - minTri v * N) := by
    calc
      minTri v * (N + 2 * a) * (f + rda)
          ≤ (beta * b) * (f + rda) := hDleft
      _ = beta * (b * (f + rda)) := by ring
      _ ≤ beta * (f * (a + N) - minTri v * N) := hDright
  have hAcross :
      minTri v * (N + 2 * d) * (ea + rda) ≤
        delta * (ea * (d + N) - minTri v * N) := by
    calc
      minTri v * (N + 2 * d) * (ea + rda)
          ≤ (delta * c) * (ea + rda) := hAleft
      _ = delta * (c * (ea + rda)) := by ring
      _ ≤ delta * (ea * (d + N) - minTri v * N) := hAright

  have hH : H = a + d + rda + (beta + f) + (delta + ea) := by
    dsimp [H, U, L, N, a, d, rda, beta, delta, ea, f]
    simp only [sig]
    ring
  have hbound := hullFive300_cab717_negative_hull_bound
    (m := minTri v) (N := N) (a := a) (d := d) (e := ea) (f := f)
    (r := rda) (beta := beta) (delta := delta) (H := H)
    hm hNpos ha hd he hf hrda hbeta hdelta hDcross hAcross hH
  simpa only [H, mul_comm] using hbound

/-- The complete metric endpoint for the exceptional CAB sign cell.

The two outer determinants are nonzero because `minTri v > 0`; their three
possible relevant sign cells are exactly the preceding theorems. -/
theorem hullFive300_cab717_packet_bound
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hm : 0 < minTri v)
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (p : HullFiveEndRightProfileC v e 7)
    (q : HullFiveEndRightProfileA v e 5)
    (r : HullFiveEndRightProfileB v e 6)
    (h717 : HullFive300Cab717InnerSigns v e) :
    minTri v * 25 ≤ 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) +
        sig (v (e 0)) (v (e 3)) (v (e 4))) := by
  let dpr := sig (v (e 4)) (v (e 7)) (v (e 6))
  let aqr := sig (v (e 0)) (v (e 5)) (v (e 6))
  have hdprMin := minTri_le_abs_sig_of_pairwise_ne v
    (a := e 4) (b := e 7) (c := e 6)
    (by exact fun h ↦ (by decide : (4 : Fin 8) ≠ 7) (e.injective h))
    (by exact fun h ↦ (by decide : (4 : Fin 8) ≠ 6) (e.injective h))
    (by exact fun h ↦ (by decide : (7 : Fin 8) ≠ 6) (e.injective h))
  have haqrMin := minTri_le_abs_sig_of_pairwise_ne v
    (a := e 0) (b := e 5) (c := e 6)
    (by exact fun h ↦ (by decide : (0 : Fin 8) ≠ 5) (e.injective h))
    (by exact fun h ↦ (by decide : (0 : Fin 8) ≠ 6) (e.injective h))
    (by exact fun h ↦ (by decide : (5 : Fin 8) ≠ 6) (e.injective h))
  have hdprNe : dpr ≠ 0 := by
    intro hz
    have habs : abs dpr = 0 := by rw [hz, abs_zero]
    dsimp only [dpr] at habs hdprMin
    nlinarith
  have haqrNe : aqr ≠ 0 := by
    intro hz
    have habs : abs aqr = 0 := by rw [hz, abs_zero]
    dsimp only [aqr] at habs haqrMin
    nlinarith
  rcases lt_or_gt_of_ne hdprNe with hdprNeg | hdprPos
  · rcases lt_or_gt_of_ne haqrNe with haqrNeg | haqrPos
    · apply hullFive300_cab717_packet_bound_of_aqr_neg
        v e hm hcyc p q r h717
      simpa only [aqr] using haqrNeg
    · apply hullFive300_cab717_packet_bound_of_dpr_neg_aqr_pos
        v e hm hcyc p q r h717
      · simpa only [dpr] using hdprNeg
      · simpa only [aqr] using haqrPos
  · apply hullFive300_cab717_packet_bound_of_dpr_pos
      v e hm hcyc p q r h717
    simpa only [dpr] using hdprPos

end Heilbronn8.TriHull
