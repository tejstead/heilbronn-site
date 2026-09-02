import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadGeometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeFiniteBridge
import Heilbronn8.Survivors.Join.HullSixThreeThreeQBlindQ122ScalarAMGM
import Heilbronn8.Survivors.Join.HullSixThreeThreeQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixThreeThreeQ112GeometryIdentities

/-!
# Geometric adapter for the q-blind `011 / 122` chambers

At a rotated oriented `3 + 3` frame, this branch uses the six signed cross
floors `X10`, `-X21`, `-Y01`, `+Y11`, `+Y21`, and `-Y22`.  Line-level and
boundary floors supply all remaining hypotheses of
`hullSixThreeThreeQ122_scalar`.  The normalized determinant-coordinate seam
then reconstructs its strict conclusion as the six-term `P`-fan sum,
contradicting the beating margin.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

private lemma threeThree_q122_shiftedBoundary_floor
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

/-- The six signed cells used by the q-blind `011 / 122` scalar
certificate are incompatible with a beating compact residual. -/
theorem threeThreeQ122At_false_of_crossFloors
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
    (hX10 : minTri cfg ≤ sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 0))))
    (hX21 : sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) ≤
        -minTri cfg)
    (hY01 : sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) ≤
        -minTri cfg)
    (hY11 : minTri cfg ≤ sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 1)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))))
    (hY21 : minTri cfg ≤ sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))))
    (hY22 : sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 2))) ≤
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

  have ha1 : 1 ≤ a := by
    have hfloor := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at hfloor
    simpa [a, U0, m, hullSixThreeThreeUpperHeight] using hnorm hfloor
  have hb1 : 1 ≤ b := by
    have hfloor := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 1)
    rw [abs_of_pos (hupper 1)] at hfloor
    simpa [b, U1, m, hullSixThreeThreeUpperHeight] using hnorm hfloor
  have hc1 : 1 ≤ c := by
    have hfloor := V.lineLevel_floor
      (rotation + hullSixThreeThreeUpperOffset 2)
    rw [abs_of_pos (hupper 2)] at hfloor
    simpa [c, U2, m, hullSixThreeThreeUpperHeight] using hnorm hfloor
  have hd1 : 1 ≤ d := by
    have hfloor := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at hfloor
    simpa [d, L0, m, hullSixThreeThreeLowerHeight] using hnorm hfloor
  have he1 : 1 ≤ e := by
    have hfloor := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 1)
    rw [abs_of_neg (hlower 1)] at hfloor
    simpa [e, L1, m, hullSixThreeThreeLowerHeight] using hnorm hfloor
  have hf1 : 1 ≤ f := by
    have hfloor := V.lineLevel_floor
      (rotation + hullSixThreeThreeLowerOffset 2)
    rw [abs_of_neg (hlower 2)] at hfloor
    simpa [f, L2, m, hullSixThreeThreeLowerHeight] using hnorm hfloor

  have htRaw : m ≤ sig (cfg P) U1 U2 := by
    simpa [m, U1, U2, hullSixThreeThreeUpperOffset] using
      threeThree_q122_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 1
  have hl1qRaw : m ≤ sig (cfg Q) L1 L2 := by
    simpa [m, L1, L2, hullSixThreeThreeLowerOffset] using
      threeThree_q122_shiftedBoundary_floor R V Q V.Q_outside
        V.Q_boundary_pos rotation 4

  have hsEq : b * d * s = sig (cfg P) U1 L0 / m :=
    sig_threeThree_qBlind_sCross_identity
      (cfg P) (cfg Q) U1 L0 hmNe hU1Ne hL0Ne
  have htEq : b * c * t = sig (cfg P) U1 U2 / m :=
    sig_threeThree_qBlind_tFan_identity
      (cfg P) (cfg Q) U1 U2 hmNe hU1Ne hU2Ne
  have hwEq : c * e * w = (-sig (cfg P) U2 L1) / m :=
    sig_threeThree_qBlind_wCross_identity
      (cfg P) (cfg Q) U2 L1 hmNe hU2Ne hL1Ne
  have hl1qEq : e * f * z + f - e = sig (cfg Q) L1 L2 / m :=
    sig_threeThree_qBlind_qLower12_identity
      (cfg P) (cfg Q) L1 L2 hmNe hL1Ne hL2Ne
  have hY01Eq :
      a * e * (r + s + t + w) - a - e =
        (-sig (cfg Q) U0 L1) / m :=
    sig_threeThree_qBlind_qY01Neg_identity
      (cfg P) (cfg Q) U0 U1 U2 L0 L1 hmNe
        hU0Ne hU1Ne hU2Ne hL0Ne hL1Ne
  have hY11NegEq :
      b * e * (t + w) - b - e = (-sig (cfg Q) U1 L1) / m :=
    sig_threeThree_q112_qY11Neg_identity
      (cfg P) (cfg Q) U1 U2 L1 hmNe hU1Ne hU2Ne hL1Ne
  have hY11Eq :
      b + e - b * e * (t + w) = sig (cfg Q) U1 L1 / m := by
    calc
      b + e - b * e * (t + w) =
          -(b * e * (t + w) - b - e) := by ring
      _ = -((-sig (cfg Q) U1 L1) / m) := by rw [hY11NegEq]
      _ = sig (cfg Q) U1 L1 / m := by ring
  have hY21Eq : c + e - c * e * w = sig (cfg Q) U2 L1 / m :=
    sig_threeThree_q112_qY21Pos_identity
      (cfg P) (cfg Q) U2 L1 hmNe hU2Ne hL1Ne
  have hY22Eq :
      c * f * (w + z) - c - f = (-sig (cfg Q) U2 L2) / m :=
    sig_threeThree_q112_qY22Neg_identity
      (cfg P) (cfg Q) U2 L1 L2 hmNe hU2Ne hL1Ne hL2Ne

  have hs : 1 ≤ b * d * s := by
    rw [hsEq]
    exact hnorm (by simpa [m, U1, L0] using hX10)
  have ht : 1 ≤ b * c * t := by
    rw [htEq]
    exact hnorm htRaw
  have hw : 1 ≤ c * e * w := by
    rw [hwEq]
    apply hnorm
    simpa [m, U2, L1] using (show minTri cfg ≤
      -sig (cfg P) U2 L1 by
        simpa [U2, L1] using (neg_le_neg hX21))
  have hl1q : 1 ≤ e * f * z + f - e := by
    rw [hl1qEq]
    exact hnorm hl1qRaw
  have hY01neg : 1 ≤ a * e * (r + s + t + w) - a - e := by
    rw [hY01Eq]
    apply hnorm
    simpa [m, U0, L1] using (show minTri cfg ≤
      -sig (cfg Q) U0 L1 by
        simpa [U0, L1] using (neg_le_neg hY01))
  have hY11pos : 1 ≤ b + e - b * e * (t + w) := by
    rw [hY11Eq]
    exact hnorm (by simpa [m, U1, L1] using hY11)
  have hY21pos : 1 ≤ c + e - c * e * w := by
    rw [hY21Eq]
    exact hnorm (by simpa [m, U2, L1] using hY21)
  have hY22neg : 1 ≤ c * f * (w + z) - c - f := by
    rw [hY22Eq]
    apply hnorm
    simpa [m, U2, L2] using (show minTri cfg ≤
      -sig (cfg Q) U2 L2 by
        simpa [U2, L2] using (neg_le_neg hY22))

  have hscalar :
      (25 : ℝ) / 2 <
        a * b * (r + s) + b * c * t + c * d * (s + t) +
          d * e * (s + t + w) + e * f * z +
            a * f * (r + s + t + w + z) :=
    hullSixThreeThreeQ122_scalar ha1 hb1 hc1 hd1 he1 hf1
      hs ht hw hl1q hY01neg hY11pos hY21pos hY22neg

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

/-- The signed q-blind branch `p = 011`, `q = 122`. -/
def q122 : HullSixThreeThreeCuts where
  p0 := 0
  p1 := 1
  p2 := 1
  q0 := 1
  q1 := 2
  q2 := 2

/-- The signed q-blind branch `p = 011`, `q = 022`. -/
def q022 : HullSixThreeThreeCuts where
  p0 := 0
  p1 := 1
  p2 := 1
  q0 := 0
  q1 := 2
  q2 := 2

end HullSixThreeThreeCuts

namespace HullSixCompactCrossChordResidual

/-- Ferrers-table wrapper for the `011 / 122` branch. -/
theorem threeThreeQ122At_false
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
    (hQ122 : ∀ i j : Fin 3,
      HullSixChamberLabel.Holds
        (HullSixThreeThreeCuts.q122.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))) :
    False := by
  have h10 := hQ122 1 0
  have h21 := hQ122 2 1
  have h01 := hQ122 0 1
  have h11 := hQ122 1 1
  have h22 := hQ122 2 2
  rw [show HullSixThreeThreeCuts.q122.table 1 0 =
    HullSixChamberLabel.L by decide] at h10
  rw [show HullSixThreeThreeCuts.q122.table 2 1 =
    HullSixChamberLabel.M by decide] at h21
  rw [show HullSixThreeThreeCuts.q122.table 0 1 =
    HullSixChamberLabel.R by decide] at h01
  rw [show HullSixThreeThreeCuts.q122.table 1 1 =
    HullSixChamberLabel.M by decide] at h11
  rw [show HullSixThreeThreeCuts.q122.table 2 2 =
    HullSixChamberLabel.R by decide] at h22
  simp only [HullSixChamberLabel.Holds] at h10 h21 h01 h11 h22
  exact R.threeThreeQ122At_false_of_crossFloors V rotation hupper hlower
    h10 h21.1 h01 h11.2 h21.2 h22

/-- Ferrers-table wrapper for the `011 / 022` branch.  The six cells used
by the Q122 scalar certificate agree with the `011 / 122` table. -/
theorem threeThreeQ022At_false
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
    (hQ022 : ∀ i j : Fin 3,
      HullSixChamberLabel.Holds
        (HullSixThreeThreeCuts.q022.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))) :
    False := by
  have h10 := hQ022 1 0
  have h21 := hQ022 2 1
  have h01 := hQ022 0 1
  have h11 := hQ022 1 1
  have h22 := hQ022 2 2
  rw [show HullSixThreeThreeCuts.q022.table 1 0 =
    HullSixChamberLabel.L by decide] at h10
  rw [show HullSixThreeThreeCuts.q022.table 2 1 =
    HullSixChamberLabel.M by decide] at h21
  rw [show HullSixThreeThreeCuts.q022.table 0 1 =
    HullSixChamberLabel.R by decide] at h01
  rw [show HullSixThreeThreeCuts.q022.table 1 1 =
    HullSixChamberLabel.M by decide] at h11
  rw [show HullSixThreeThreeCuts.q022.table 2 2 =
    HullSixChamberLabel.R by decide] at h22
  simp only [HullSixChamberLabel.Holds] at h10 h21 h01 h11 h22
  exact R.threeThreeQ122At_false_of_crossFloors V rotation hupper hlower
    h10 h21.1 h01 h11.2 h21.2 h22

end HullSixCompactCrossChordResidual

end Heilbronn8
