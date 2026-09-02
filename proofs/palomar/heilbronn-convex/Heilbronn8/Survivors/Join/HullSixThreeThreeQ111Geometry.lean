import Heilbronn8.Survivors.Join.HullSixThreeThreeQ133Geometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeQBlindQ111ScalarAMGM
import Heilbronn8.Survivors.Join.HullSixFerrersPropagation

/-!
# Geometric adapter for the q-blind `011 / 111` chambers

At a rotated oriented `3 + 3` frame, this branch uses the four signed cross
floors `-X00`, `X10`, `-Y01`, and `-Y21`.  Boundary and line-level floors
supply the remaining hypotheses of `hullSixThreeThreeQ111_scalar`.  The
normalized determinant-coordinate seam reconstructs its conclusion as the
six-term `P`-fan sum, contradicting the beating margin.

The `011 / 011` wrapper has an `R` cell at `(0,0)`.  Base change and the two
line-level floors strengthen that cell to `X00 <= -3m`, so it feeds the same
core theorem as `011 / 111`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

private lemma threeThree_q111_shiftedBoundary_floor
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (base : Fin 8) (hOutside : base ∉ Set.range cycle)
    (hpos : ∀ i,
      0 < sig (cfg base) (cfg (cycle i)) (cfg (cycle (i + 1))))
    (rotation offset : Fin 6) :
    minTri cfg ≤ sig (cfg base) (cfg (cycle (rotation + offset)))
      (cfg (cycle (rotation + (offset + 1)))) := by
  have h := minTri_le_sixCycle_boundary_sig cfg cycle R.cycle_injective
    base hOutside (rotation + offset) (hpos (rotation + offset))
  have hnext : (rotation + offset) + 1 =
      rotation + (offset + 1) := by
    simp [add_assoc]
  simpa only [hnext] using h

namespace HullSixCompactCrossChordResidual

/-- The four signed cells used by the q-blind `011 / 111` scalar
certificate are incompatible with a beating compact residual. -/
theorem threeThreeQ111At_false_of_crossFloors
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : ∀ j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0)
    (hX00 : sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))) ≤
        -minTri cfg)
    (hX10 : minTri cfg ≤ sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))))
    (hY01 : sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) ≤
        -minTri cfg)
    (hY21 : sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) ≤
        -minTri cfg) :
    False := by
  let m := minTri cfg
  let U0 := cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0))
  let U1 := cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1))
  let U2 := cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2))
  let L0 := cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))
  let L1 := cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))
  let L2 := cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))

  let a := hullSixThreeThreeUpperHeight (cfg P) (cfg Q) U0 m
  let b := hullSixThreeThreeUpperHeight (cfg P) (cfg Q) U1 m
  let c := hullSixThreeThreeUpperHeight (cfg P) (cfg Q) U2 m
  let d := hullSixThreeThreeLowerHeight (cfg P) (cfg Q) L0 m
  let e := hullSixThreeThreeLowerHeight (cfg P) (cfg Q) L1 m
  let f := hullSixThreeThreeLowerHeight (cfg P) (cfg Q) L2 m
  let r := hullSixThreeThreeRGap (cfg P) (cfg Q) U0 L0 m
  let s := hullSixThreeThreeSGap (cfg P) (cfg Q) U1 L0 m
  let t := hullSixThreeThreeTGap (cfg P) (cfg Q) U1 U2 m
  let w := hullSixThreeThreeWGap (cfg P) (cfg Q) U2 L1 m
  let z := hullSixThreeThreeZGap (cfg P) (cfg Q) L1 L2 m

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hmNe : m ≠ 0 := ne_of_gt hm
  have hnorm {x : ℝ} (hx : m ≤ x) : 1 ≤ x / m := by
    exact (le_div_iff₀ hm).2 (by simpa using hx)

  have hU0pos : 0 < sig (cfg P) (cfg Q) U0 := by
    simpa [U0] using hupper 0
  have hU1pos : 0 < sig (cfg P) (cfg Q) U1 := by
    simpa [U1] using hupper 1
  have hU2pos : 0 < sig (cfg P) (cfg Q) U2 := by
    simpa [U2] using hupper 2
  have hL0neg : sig (cfg P) (cfg Q) L0 < 0 := by
    simpa [L0] using hlower 0
  have hL1neg : sig (cfg P) (cfg Q) L1 < 0 := by
    simpa [L1] using hlower 1
  have hL2neg : sig (cfg P) (cfg Q) L2 < 0 := by
    simpa [L2] using hlower 2
  have hU0Ne : sig (cfg P) (cfg Q) U0 ≠ 0 := ne_of_gt hU0pos
  have hU1Ne : sig (cfg P) (cfg Q) U1 ≠ 0 := ne_of_gt hU1pos
  have hU2Ne : sig (cfg P) (cfg Q) U2 ≠ 0 := ne_of_gt hU2pos
  have hL0Ne : sig (cfg P) (cfg Q) L0 ≠ 0 := ne_of_lt hL0neg
  have hL1Ne : sig (cfg P) (cfg Q) L1 ≠ 0 := ne_of_lt hL1neg
  have hL2Ne : sig (cfg P) (cfg Q) L2 ≠ 0 := ne_of_lt hL2neg

  have ha : 0 < a := by
    dsimp [a, hullSixThreeThreeUpperHeight]
    exact div_pos hU0pos hm
  have hb : 0 < b := by
    dsimp [b, hullSixThreeThreeUpperHeight]
    exact div_pos hU1pos hm
  have hc : 0 < c := by
    dsimp [c, hullSixThreeThreeUpperHeight]
    exact div_pos hU2pos hm
  have hd : 0 < d := by
    dsimp [d, hullSixThreeThreeLowerHeight]
    exact div_pos (neg_pos.mpr hL0neg) hm
  have he : 0 < e := by
    dsimp [e, hullSixThreeThreeLowerHeight]
    exact div_pos (neg_pos.mpr hL1neg) hm
  have hf : 0 < f := by
    dsimp [f, hullSixThreeThreeLowerHeight]
    exact div_pos (neg_pos.mpr hL2neg) hm

  have ha1 : 1 ≤ a := by
    have hfloor := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at hfloor
    simpa [a, U0, m, hullSixThreeThreeUpperHeight] using hnorm hfloor
  have hf1 : 1 ≤ f := by
    have hfloor := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at hfloor
    simpa [f, L2, m, hullSixThreeThreeLowerHeight] using hnorm hfloor

  have htRaw : m ≤ sig (cfg P) U1 U2 := by
    simpa [m, U1, U2, hullSixThreeThreeUpperOffset] using
      threeThree_q111_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 1
  have hl1qRaw : m ≤ sig (cfg Q) L1 L2 := by
    simpa [m, L1, L2, hullSixThreeThreeLowerOffset] using
      threeThree_q111_shiftedBoundary_floor R V Q V.Q_outside
        V.Q_boundary_pos rotation 4

  have hrEq : a * d * r = (-sig (cfg P) U0 L0) / m :=
    sig_threeThree_qBlind_rCross_identity
      (cfg P) (cfg Q) U0 L0 hmNe hU0Ne hL0Ne
  have hsEq : b * d * s = sig (cfg P) U1 L0 / m :=
    sig_threeThree_qBlind_sCross_identity
      (cfg P) (cfg Q) U1 L0 hmNe hU1Ne hL0Ne
  have htEq : b * c * t = sig (cfg P) U1 U2 / m :=
    sig_threeThree_qBlind_tFan_identity
      (cfg P) (cfg Q) U1 U2 hmNe hU1Ne hU2Ne
  have hl1qEq : e * f * z + f - e = sig (cfg Q) L1 L2 / m :=
    sig_threeThree_qBlind_qLower12_identity
      (cfg P) (cfg Q) L1 L2 hmNe hL1Ne hL2Ne
  have hY01Eq :
      a * e * (r + s + t + w) - a - e =
        (-sig (cfg Q) U0 L1) / m :=
    sig_threeThree_qBlind_qY01Neg_identity
      (cfg P) (cfg Q) U0 U1 U2 L0 L1 hmNe
        hU0Ne hU1Ne hU2Ne hL0Ne hL1Ne
  have hY21Eq : c * e * w - c - e = (-sig (cfg Q) U2 L1) / m :=
    sig_threeThree_qBlind_qY21Neg_identity
      (cfg P) (cfg Q) U2 L1 hmNe hU2Ne hL1Ne

  have hr : 1 ≤ a * d * r := by
    rw [hrEq]
    apply hnorm
    simpa [m, U0, L0] using (show minTri cfg ≤
      -sig (cfg P) U0 L0 by
        simpa [U0, L0] using (neg_le_neg hX00))
  have hs : 1 ≤ b * d * s := by
    rw [hsEq]
    exact hnorm (by simpa [m, U1, L0] using hX10)
  have ht : 1 ≤ b * c * t := by
    rw [htEq]
    exact hnorm htRaw
  have hl1q : 1 ≤ e * f * z + f - e := by
    rw [hl1qEq]
    exact hnorm hl1qRaw
  have hY01neg : 1 ≤ a * e * (r + s + t + w) - a - e := by
    rw [hY01Eq]
    apply hnorm
    simpa [m, U0, L1] using (show minTri cfg ≤
      -sig (cfg Q) U0 L1 by
        simpa [U0, L1] using (neg_le_neg hY01))
  have hY21neg : 1 ≤ c * e * w - c - e := by
    rw [hY21Eq]
    apply hnorm
    simpa [m, U2, L1] using (show minTri cfg ≤
      -sig (cfg Q) U2 L1 by
        simpa [U2, L1] using (neg_le_neg hY21))

  have hscalar :
      (25 : ℝ) / 2 <
        a * b * (r + s) + b * c * t + c * d * (s + t) +
          d * e * (s + t + w) + e * f * z +
            a * f * (r + s + t + w + z) :=
    hullSixThreeThreeQ111_scalar ha hb hc hd he hf ha1 hf1
      hr hs ht hl1q hY01neg hY21neg

  have hUpper01 : a * b * (r + s) = sig (cfg P) U0 U1 / m :=
    sig_threeThree_qBlind_upper01_identity
      (cfg P) (cfg Q) U0 U1 L0 hmNe hU0Ne hU1Ne hL0Ne
  have hUpper12 : b * c * t = sig (cfg P) U1 U2 / m :=
    sig_threeThree_qBlind_upper12_identity
      (cfg P) (cfg Q) U1 U2 hmNe hU1Ne hU2Ne
  have hCross20 : c * d * (s + t) = sig (cfg P) U2 L0 / m :=
    sig_threeThree_qBlind_cross20_identity
      (cfg P) (cfg Q) U1 U2 L0 hmNe hU1Ne hU2Ne hL0Ne
  have hLower01 :
      d * e * (s + t + w) = sig (cfg P) L0 L1 / m :=
    sig_threeThree_qBlind_lower01_identity
      (cfg P) (cfg Q) U1 U2 L0 L1 hmNe
        hU1Ne hU2Ne hL0Ne hL1Ne
  have hLower12 : e * f * z = sig (cfg P) L1 L2 / m :=
    sig_threeThree_qBlind_lower12_identity
      (cfg P) (cfg Q) L1 L2 hmNe hL1Ne hL2Ne
  have hWrap :
      a * f * (r + s + t + w + z) = sig (cfg P) L2 U0 / m :=
    sig_threeThree_qBlind_wrap_identity
      (cfg P) (cfg Q) U0 U1 U2 L0 L1 L2 hmNe
        hU0Ne hU1Ne hU2Ne hL0Ne hL1Ne hL2Ne
  rw [hUpper01, hUpper12, hCross20, hLower01, hLower12, hWrap]
    at hscalar

  let fan : Fin 6 → ℝ := fun i =>
    sig (cfg P) (cfg (cycle i)) (cfg (cycle (i + 1)))
  have hshifted :
      sumFinSix (fun i =>
        sig (cfg P) (cfg (cycle (rotation + i)))
          (cfg (cycle (rotation + (i + 1))))) = doubledHullArea cfg := by
    have hfun : (fun i =>
          sig (cfg P) (cfg (cycle (rotation + i)))
            (cfg (cycle (rotation + (i + 1))))) =
        (fun i => fan (rotation + i)) := by
      funext i
      simp [fan, add_assoc]
    rw [hfun, sumFinSix_add_left]
    exact V.P_fan_sum
  have hSumRaw : doubledHullArea cfg =
      sig (cfg P) (cfg (cycle rotation)) (cfg (cycle (rotation + 1))) +
      sig (cfg P) (cfg (cycle (rotation + 1)))
        (cfg (cycle (rotation + 2))) +
      sig (cfg P) (cfg (cycle (rotation + 2)))
        (cfg (cycle (rotation + 3))) +
      sig (cfg P) (cfg (cycle (rotation + 3)))
        (cfg (cycle (rotation + 4))) +
      sig (cfg P) (cfg (cycle (rotation + 4)))
        (cfg (cycle (rotation + 5))) +
      sig (cfg P) (cfg (cycle (rotation + 5))) (cfg (cycle rotation)) := by
    rw [← hshifted]
    simp [sumFinSix] <;> ring
  have hSum : doubledHullArea cfg =
      sig (cfg P) U0 U1 + sig (cfg P) U1 U2 +
        sig (cfg P) U2 L0 + sig (cfg P) L0 L1 +
          sig (cfg P) L1 L2 + sig (cfg P) L2 U0 := by
    simpa [U0, U1, U2, L0, L1, L2,
      hullSixThreeThreeUpperOffset, hullSixThreeThreeLowerOffset] using hSumRaw
  have hfanNorm :
      sig (cfg P) U0 U1 / m + sig (cfg P) U1 U2 / m +
          sig (cfg P) U2 L0 / m + sig (cfg P) L0 L1 / m +
            sig (cfg P) L1 L2 / m + sig (cfg P) L2 U0 / m =
        doubledHullArea cfg / m := by
    calc
      sig (cfg P) U0 U1 / m + sig (cfg P) U1 U2 / m +
            sig (cfg P) U2 L0 / m + sig (cfg P) L0 L1 / m +
              sig (cfg P) L1 L2 / m + sig (cfg P) L2 U0 / m =
          (sig (cfg P) U0 U1 + sig (cfg P) U1 U2 +
            sig (cfg P) U2 L0 + sig (cfg P) L0 L1 +
              sig (cfg P) L1 L2 + sig (cfg P) L2 U0) / m := by ring
      _ = doubledHullArea cfg / m := by rw [← hSum]
  rw [hfanNorm] at hscalar

  have hmul : ((25 : ℝ) / 2) * m < doubledHullArea cfg :=
    (lt_div_iff₀ hm).1 hscalar
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hmul, hcut]

end HullSixCompactCrossChordResidual

namespace HullSixThreeThreeCuts

/-- The signed q-blind branch `p = 011`, `q = 111`. -/
def q111 : HullSixThreeThreeCuts where
  p0 := 0
  p1 := 1
  p2 := 1
  q0 := 1
  q1 := 1
  q2 := 1

/-- The signed q-blind branch `p = 011`, `q = 011`. -/
def q011 : HullSixThreeThreeCuts where
  p0 := 0
  p1 := 1
  p2 := 1
  q0 := 0
  q1 := 1
  q2 := 1

end HullSixThreeThreeCuts

namespace HullSixCompactCrossChordResidual

/-- Ferrers-table wrapper for the `011 / 111` branch. -/
theorem threeThreeQ111At_false
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : ∀ j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0)
    (hQ111 : ∀ i j : Fin 3,
      HullSixChamberLabel.Holds
        (HullSixThreeThreeCuts.q111.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))) :
    False := by
  have h00 := hQ111 0 0
  have h10 := hQ111 1 0
  have h01 := hQ111 0 1
  have h21 := hQ111 2 1
  rw [show HullSixThreeThreeCuts.q111.table 0 0 =
    HullSixChamberLabel.M by decide] at h00
  rw [show HullSixThreeThreeCuts.q111.table 1 0 =
    HullSixChamberLabel.L by decide] at h10
  rw [show HullSixThreeThreeCuts.q111.table 0 1 =
    HullSixChamberLabel.R by decide] at h01
  rw [show HullSixThreeThreeCuts.q111.table 2 1 =
    HullSixChamberLabel.R by decide] at h21
  simp only [HullSixChamberLabel.Holds] at h00 h10 h01 h21
  exact R.threeThreeQ111At_false_of_crossFloors V rotation hupper hlower
    h00.1 h10 h01 h21

/-- Ferrers-table wrapper for the `011 / 011` branch.  Its `(0,0)` `R`
cell is strengthened on the `P` side by line-level base change. -/
theorem threeThreeQ011At_false
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 3,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i))))
    (hlower : ∀ j : Fin 3,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0)
    (hQ011 : ∀ i j : Fin 3,
      HullSixChamberLabel.Holds
        (HullSixThreeThreeCuts.q011.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))) :
    False := by
  let U0 := cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0))
  let L0 := cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))
  have h00 := hQ011 0 0
  have h10 := hQ011 1 0
  have h01 := hQ011 0 1
  have h21 := hQ011 2 1
  rw [show HullSixThreeThreeCuts.q011.table 0 0 =
    HullSixChamberLabel.R by decide] at h00
  rw [show HullSixThreeThreeCuts.q011.table 1 0 =
    HullSixChamberLabel.L by decide] at h10
  rw [show HullSixThreeThreeCuts.q011.table 0 1 =
    HullSixChamberLabel.R by decide] at h01
  rw [show HullSixThreeThreeCuts.q011.table 2 1 =
    HullSixChamberLabel.R by decide] at h21
  simp only [HullSixChamberLabel.Holds] at h10 h01 h21

  have hU0Raw : minTri cfg ≤ sig (cfg P) (cfg Q) U0 := by
    have hfloor := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at hfloor
    simpa [U0] using hfloor
  have hL0Raw : minTri cfg ≤ -sig (cfg P) (cfg Q) L0 := by
    have hfloor := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at hfloor
    simpa [L0] using hfloor
  have hbase :
      sig (cfg Q) U0 L0 =
        sig (cfg P) U0 L0 + sig (cfg P) (cfg Q) U0 +
          (-sig (cfg P) (cfg Q) L0) := by
    simp only [sig]
    ring
  have hX00Strong : sig (cfg P) U0 L0 ≤ -3 * minTri cfg :=
    chamberLabel_R_pDet_le_neg_three hU0Raw hL0Raw hbase h00
  have hX00 : sig (cfg P) U0 L0 ≤ -minTri cfg := by
    nlinarith [R.minTri_pos]
  exact R.threeThreeQ111At_false_of_crossFloors V rotation hupper hlower
    (by simpa [U0, L0] using hX00) h10 h01 h21

end HullSixCompactCrossChordResidual

end Heilbronn8
