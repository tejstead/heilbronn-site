import Heilbronn8.Survivors.Join.HullSixTwoFourP03MaximalQScalar
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixTwoFourSoundSemanticBridge

/-!
# The maximal-q `p = (0,3)` partial frontier

Only the retained `X` frontier is decoded.  The remaining endpoint chord is
given its unconditional absolute triangle floor and split into its two signs.
No exact chamber table and no other `Q` cross-chord sign is used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

/-- The maximal-q frontier record with first cuts `p = (0,3)`. -/
def HullSixTwoFourIsP03MaximalQFrontier
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixTwoFourIsMaximalQFrontier T ∧ T.p0 = 0 ∧ T.p1 = 3

namespace HullSixCompactCrossChordResidual

/-- The `p = (0,3)` partial `X` frontier is incompatible with a beating
oriented `2 + 4` view. -/
theorem twoFourP03MaximalQAt_false
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 2,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset i))))
    (hlower : ∀ j : Fin 4,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))) < 0)
    (T : HullSixTwoFourCuts) (hp0 : T.p0 = 0) (hp1 : T.p1 = 3)
    (hFrontier : HullSixQBlindFrontierHolds T.p T.q (minTri cfg)
      (fun i j => sig (cfg P)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))) :
    False := by
  let m := minTri cfg
  let U : Fin 2 → ℝ × ℝ := fun i ↦
    cfg (cycle (rotation + hullSixTwoFourUpperOffset i))
  let L : Fin 4 → ℝ × ℝ := fun j ↦
    cfg (cycle (rotation + hullSixTwoFourLowerOffset j))
  let a := hullSixThreeThreeUpperHeight (cfg P) (cfg Q) (U 0) m
  let b := hullSixThreeThreeUpperHeight (cfg P) (cfg Q) (U 1) m
  let c := hullSixThreeThreeLowerHeight (cfg P) (cfg Q) (L 0) m
  let d := hullSixThreeThreeLowerHeight (cfg P) (cfg Q) (L 1) m
  let e := hullSixThreeThreeLowerHeight (cfg P) (cfg Q) (L 2) m
  let f := hullSixThreeThreeLowerHeight (cfg P) (cfg Q) (L 3) m
  let A := sig (cfg P) (U 0) (U 1) / m
  let Ap := sig (cfg Q) (U 0) (U 1) / m
  let C := sig (cfg P) (U 1) (L 0) / m
  let E0 := sig (cfg P) (L 0) (L 1) / m
  let E1 := sig (cfg P) (L 1) (L 2) / m
  let E2 := sig (cfg P) (L 2) (L 3) / m
  let F := sig (cfg P) (L 3) (U 0) / m
  let Fp := sig (cfg Q) (L 3) (U 0) / m
  let X00 := sig (cfg P) (U 0) (L 0) / m
  let X10 := sig (cfg P) (U 1) (L 0) / m
  let X11 := sig (cfg P) (U 1) (L 1) / m
  let X12 := sig (cfg P) (U 1) (L 2) / m
  let X13 := sig (cfg P) (U 1) (L 3) / m
  let Y13 := sig (cfg Q) (U 1) (L 3) / m
  let H := doubledHullArea cfg / m

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hnorm {s : ℝ} (hs : m ≤ s) : (1 : ℝ) ≤ s / m := by
    exact (le_div_iff₀ hm).2 (by simpa using hs)
  have hnormNeg {s : ℝ} (hs : s ≤ -m) : s / m ≤ (-1 : ℝ) := by
    exact (div_le_iff₀ hm).2 (by simpa using hs)

  have ha1 : 1 ≤ a := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at h
    exact hnorm (by simpa [m, U] using h)
  have hb1 : 1 ≤ b := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourUpperOffset 1)
    rw [abs_of_pos (hupper 1)] at h
    exact hnorm (by simpa [m, U] using h)
  have hc1 : 1 ≤ c := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 0) := by
      simpa [m, L] using h
    simpa [c, hullSixThreeThreeLowerHeight] using hnorm hraw
  have hd1 : 1 ≤ d := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 1)
    rw [abs_of_neg (hlower 1)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 1) := by
      simpa [m, L] using h
    simpa [d, hullSixThreeThreeLowerHeight] using hnorm hraw
  have he1 : 1 ≤ e := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 2) := by
      simpa [m, L] using h
    simpa [e, hullSixThreeThreeLowerHeight] using hnorm hraw
  have hf1 : 1 ≤ f := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 3)
    rw [abs_of_neg (hlower 3)] at h
    have hraw : m ≤ -sig (cfg P) (cfg Q) (L 3) := by
      simpa [m, L] using h
    simpa [f, hullSixThreeThreeLowerHeight] using hnorm hraw

  have hA1 : 1 ≤ A := by
    have h := R.twoFour_P_boundary_floor V rotation 0
    exact hnorm (by simpa [m, A, U, hullSixTwoFourUpperOffset] using h)
  have hC1 : 1 ≤ C := by
    have h := R.twoFour_P_boundary_floor V rotation 1
    exact hnorm (by simpa [m, C, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)
  have hE01 : 1 ≤ E0 := by
    have h := R.twoFour_P_boundary_floor V rotation 2
    exact hnorm (by simpa [m, E0, L, hullSixTwoFourLowerOffset] using h)
  have hE11 : 1 ≤ E1 := by
    have h := R.twoFour_P_boundary_floor V rotation 3
    exact hnorm (by simpa [m, E1, L, hullSixTwoFourLowerOffset] using h)
  have hE21 : 1 ≤ E2 := by
    have h := R.twoFour_P_boundary_floor V rotation 4
    exact hnorm (by simpa [m, E2, L, hullSixTwoFourLowerOffset] using h)
  have hFp1 : 1 ≤ Fp := by
    have h := R.twoFour_Q_boundary_floor V rotation 5
    exact hnorm (by simpa [m, Fp, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using h)

  rcases hFrontier with ⟨hLeft, hNegative, hStrong⟩
  have hX00Raw : sig (cfg P) (U 0) (L 0) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp0] using
      hNegative (0 : Fin 2) (0 : Fin 4) (by simp [HullSixTwoFourCuts.p, hp0])
  have hX10Raw : m ≤ sig (cfg P) (U 1) (L 0) := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp1] using
      hLeft (1 : Fin 2) (0 : Fin 4) (by simp [HullSixTwoFourCuts.p, hp1])
  have hX11Raw : m ≤ sig (cfg P) (U 1) (L 1) := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp1] using
      hLeft (1 : Fin 2) (1 : Fin 4) (by simp [HullSixTwoFourCuts.p, hp1])
  have hX12Raw : m ≤ sig (cfg P) (U 1) (L 2) := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp1] using
      hLeft (1 : Fin 2) (2 : Fin 4) (by simp [HullSixTwoFourCuts.p, hp1])
  have hX13Raw : sig (cfg P) (U 1) (L 3) ≤ -m := by
    simpa [m, U, L, HullSixTwoFourCuts.p, hp1] using
      hNegative (1 : Fin 2) (3 : Fin 4) (by simp [HullSixTwoFourCuts.p, hp1])
  have hX00 : X00 ≤ -1 := hnormNeg (by simpa [X00] using hX00Raw)
  have hX10 : 1 ≤ X10 := hnorm (by simpa [X10] using hX10Raw)
  have hX11 : 1 ≤ X11 := hnorm (by simpa [X11] using hX11Raw)
  have hX12 : 1 ≤ X12 := hnorm (by simpa [X12] using hX12Raw)
  have hX13 : X13 ≤ -1 := hnormNeg (by simpa [X13] using hX13Raw)

  have hApBase : Ap = A + a - b := by
    dsimp [Ap, A, a, b, hullSixThreeThreeUpperHeight]
    rw [sig_twoFour_qBlind_base_change]
  have hFpBase : Fp = F - a - f := by
    dsimp [Fp, F, a, f, hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hF : a + f + 1 ≤ F := by linarith [hFpBase, hFp1]
  have hY13Base : Y13 = X13 + b + f := by
    dsimp [Y13, X13, b, f, hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    rw [sig_twoFour_qBlind_base_change]
    ring
  have hFpIdentity : b * Fp = f * Ap - a * Y13 := by
    dsimp [a, b, f, Ap, Fp, Y13,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hAIdentity : c * A = a * X10 - b * X00 := by
    dsimp [a, b, c, A, X10, X00,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hcA : a + b ≤ c * A := by
    rw [hAIdentity]
    have haX : a ≤ a * X10 := by
      simpa using mul_le_mul_of_nonneg_left hX10
        (le_trans zero_le_one ha1)
    have hbX : b * X00 ≤ -b := by
      simpa using mul_le_mul_of_nonneg_left hX00
        (le_trans zero_le_one hb1)
    linarith
  have hE2Identity : b * E2 = f * X12 - e * X13 := by
    dsimp [b, e, f, E2, X12, X13,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hRec : b * E1 = e * X11 - d * X12 := by
    dsimp [b, d, e, E1, X11, X12,
      hullSixThreeThreeUpperHeight, hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring

  let ear0 := sig (L 0) (L 1) (L 2) / m
  let ear1 := sig (L 1) (L 2) (L 3) / m
  let earP := sig (U 1) (L 0) (L 1) / m
  have hEar0Floor : 1 ≤ ear0 := by
    have h := R.twoFour_hullEar_floor rotation 2
    exact hnorm (by simpa [m, ear0, L, hullSixTwoFourLowerOffset,
      add_assoc] using h)
  have hEar1Floor : 1 ≤ ear1 := by
    have h := R.twoFour_hullEar_floor rotation 3
    exact hnorm (by simpa [m, ear1, L, hullSixTwoFourLowerOffset,
      add_assoc] using h)
  have hEarPFloor : 1 ≤ earP := by
    have h := R.twoFour_hullEar_floor rotation 1
    exact hnorm (by simpa [m, earP, U, L, hullSixTwoFourUpperOffset,
      hullSixTwoFourLowerOffset, add_assoc] using h)
  have hEar0Identity :
      (d - c) * E1 - (e - d) * E0 = d * ear0 := by
    dsimp [c, d, e, E0, E1, ear0,
      hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar0 : d ≤ (d - c) * E1 - (e - d) * E0 := by
    rw [hEar0Identity]
    simpa using mul_le_mul_of_nonneg_left hEar0Floor
      (le_trans zero_le_one hd1)
  have hEar1Identity :
      (e - f) * E1 + (e - d) * E2 = e * ear1 := by
    dsimp [d, e, f, E1, E2, ear1,
      hullSixThreeThreeLowerHeight]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hEar1 : e ≤ (e - f) * E1 + (e - d) * E2 := by
    rw [hEar1Identity]
    simpa using mul_le_mul_of_nonneg_left hEar1Floor
      (le_trans zero_le_one he1)
  have hEarPIdentity : C + E0 - X11 = earP := by
    dsimp [C, E0, X11, earP]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hHullP : 1 ≤ C + E0 - X11 := by
    rw [hEarPIdentity]
    exact hEarPFloor

  have hPFanNorm : H = A + C + E0 + E1 + E2 + F := by
    have hFan := R.twoFour_P_fan_sum V rotation
    dsimp [H]
    rw [hFan]
    dsimp [A, C, E0, E1, E2, F, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset]
    simp only [add_zero]
    field_simp [hm.ne'] <;> simp only [sig] <;> ring
  have hClose : (25 : ℝ) / 2 < H → False := by
    intro hNorm
    have hwide : 25 * m < 2 * doubledHullArea cfg := by
      dsimp [H] at hNorm
      have hscaled : (25 : ℝ) / 2 * m < doubledHullArea cfg :=
        (lt_div_iff₀ hm).1 hNorm
      nlinarith
    have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
      change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
      exact R.cut_margin
    nlinarith only [hwide, hcut]

  have hU1Q : Q ≠ cycle (rotation + hullSixTwoFourUpperOffset 1) := by
    intro h
    exact V.Q_outside ⟨rotation + hullSixTwoFourUpperOffset 1, h.symm⟩
  have hL3Q : Q ≠ cycle (rotation + hullSixTwoFourLowerOffset 3) := by
    intro h
    exact V.Q_outside ⟨rotation + hullSixTwoFourLowerOffset 3, h.symm⟩
  have hU1L3 :
      cycle (rotation + hullSixTwoFourUpperOffset 1) ≠
        cycle (rotation + hullSixTwoFourLowerOffset 3) := by
    apply R.cycle_injective.ne
    fin_cases rotation <;> decide
  have hY13FloorRaw : m ≤ |sig (cfg Q) (U 1) (L 3)| := by
    simpa [m, U, L] using minTri_le_abs_sig_of_pairwise_ne cfg
      hU1Q hL3Q hU1L3
  have hY13Abs : 1 ≤ |Y13| := by
    have h := hnorm hY13FloorRaw
    dsimp [Y13]
    rw [abs_div, abs_of_pos hm]
    exact h

  by_cases hY13nonneg : 0 ≤ Y13
  · have hY13pos : 1 ≤ Y13 := by
      rw [abs_of_nonneg hY13nonneg] at hY13Abs
      exact hY13Abs
    have hfAp : a + b ≤ f * Ap := by
      have hbFp : b ≤ b * Fp := by
        simpa using mul_le_mul_of_nonneg_left hFp1
          (le_trans zero_le_one hb1)
      have haY : a ≤ a * Y13 := by
        simpa using mul_le_mul_of_nonneg_left hY13pos
          (le_trans zero_le_one ha1)
      linarith [hFpIdentity]
    have hbE2 : e + f ≤ b * E2 := by
      rw [hE2Identity]
      have hfX : f ≤ f * X12 := by
        simpa using mul_le_mul_of_nonneg_left hX12
          (le_trans zero_le_one hf1)
      have heX : e * X13 ≤ -e := by
        simpa using mul_le_mul_of_nonneg_left hX13
          (le_trans zero_le_one he1)
      linarith
    by_cases hde : d ≤ e
    · apply hClose
      rw [hPFanNorm]
      exact Survivors.Join.hullSixTwoFour_p03_e_ge_d_scalar
        ha1 hb1 hc1 hd1 he1 hf1 hE01 hE11 hde hApBase hcA hfAp hbE2 hF
        hEar0 hRec hX12 hHullP
    · have hed : e ≤ d := le_of_lt (lt_of_not_ge hde)
      apply hClose
      rw [hPFanNorm]
      exact Survivors.Join.hullSixTwoFour_p03Y13Pos_e_le_d_scalar
        ha1 hb1 hd1 he1 hf1 hE11 hE21 hed hApBase hfAp hbE2 hF
        hEar1 hRec hX12 hHullP
  · have hY13neg : Y13 ≤ -1 := by
      have hnonpos : Y13 ≤ 0 := le_of_not_ge hY13nonneg
      rw [abs_of_nonpos hnonpos] at hY13Abs
      linarith
    have hX13Strong : X13 ≤ -(b + f + 1) := by
      linarith [hY13Base]
    have hbE2Strong : b * e + e * f + e + f ≤ b * E2 := by
      rw [hE2Identity]
      have hfX : f ≤ f * X12 := by
        simpa using mul_le_mul_of_nonneg_left hX12
          (le_trans zero_le_one hf1)
      have heX : e * X13 ≤ -e * (b + f + 1) := by
        have hmul := mul_le_mul_of_nonneg_left hX13Strong
          (le_trans zero_le_one he1)
        nlinarith only [hmul]
      nlinarith
    by_cases hde : d ≤ e
    · apply hClose
      rw [hPFanNorm]
      exact Survivors.Join.hullSixTwoFour_p03Y13Neg_d_le_e_scalar
        ha1 hb1 hc1 hd1 he1 hf1 hE01 hE11 hde hcA hbE2Strong hF
        hEar0 hRec hX12 hHullP
    · have hed : e ≤ d := le_of_lt (lt_of_not_ge hde)
      apply hClose
      rw [hPFanNorm]
      exact Survivors.Join.hullSixTwoFour_p03Y13Neg_e_le_d_scalar
        ha1 hb1 hd1 he1 hf1 hA1 hE11 hE21 hed hbE2Strong hF
        hEar1 hRec hX12 hHullP

end HullSixCompactCrossChordResidual

/-- Global provider for the maximal-q `p = (0,3)` fibre. -/
theorem hullSixTwoFourP03MaximalQFrontierProvider :
    HullSixTwoFourXFrontierProvider HullSixTwoFourIsP03MaximalQFrontier := by
  intro cfg cycle p q R F T hLegal hPacket hFrontier
  change HullSixQBlindFrontierHolds T.p T.q (minTri cfg)
    (fun i j =>
      sig (cfg F.P)
        (cfg (cycle (F.rotation + hullSixTwoFourUpperOffset i)))
        (cfg (cycle (F.rotation + hullSixTwoFourLowerOffset j)))) at hFrontier
  exact R.twoFourP03MaximalQAt_false F.view F.rotation
    F.upper_pos F.lower_neg T hPacket.2.1 hPacket.2.2
      hFrontier

end Heilbronn8
