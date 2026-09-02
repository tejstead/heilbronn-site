import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadGeometry
import Heilbronn8.Survivors.Join.HullSixThreeThreeFiniteBridge
import Heilbronn8.Survivors.Join.HullSixThreeThreeQBlindQ233HeightMax
import Heilbronn8.Survivors.Join.HullSixThreeThreeQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixSemantic

/-!
# Geometric adapter for the q-blind `011 / 222`, `223`, and `233` chambers

At a rotated oriented `3 + 3` frame, these three branches share the five
signed cross floors `-X00`, `X10`, `-X21`, `+Y01`, and `-Y02`.  Line-level
and shifted boundary floors supply the height and fan hypotheses of
`hullSixThreeThreeQ233_scalar`; the consecutive lower hull ear supplies its
last premise.  The normalized determinant-coordinate seam then identifies
the strict scalar conclusion with the six-term `P`-fan sum, contradicting
the beating margin.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

private lemma threeThree_q233_shiftedBoundary_floor
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

private lemma threeThree_q233_shiftedConsecutiveTriple_pos
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (start : Fin 6) :
    0 < sig (cfg (cycle start)) (cfg (cycle (start + 1)))
      (cfg (cycle (start + 2))) := by
  have h012 := R.cycle_strict.pos 0 1 2 (by decide) (by decide)
  have h123 := R.cycle_strict.pos 1 2 3 (by decide) (by decide)
  have h234 := R.cycle_strict.pos 2 3 4 (by decide) (by decide)
  have h345 := R.cycle_strict.pos 3 4 5 (by decide) (by decide)
  have h045 := R.cycle_strict.pos 0 4 5 (by decide) (by decide)
  have h015 := R.cycle_strict.pos 0 1 5 (by decide) (by decide)
  have h450 :
      0 < sig (cfg (cycle 4)) (cfg (cycle 5)) (cfg (cycle 0)) := by
    rw [← sig_rotate]
    exact h045
  have h501 :
      0 < sig (cfg (cycle 5)) (cfg (cycle 0)) (cfg (cycle 1)) := by
    rw [← sig_rotate, ← sig_rotate]
    exact h015
  fin_cases start <;>
    first
    | simpa using h012
    | simpa using h123
    | simpa using h234
    | simpa using h345
    | simpa using h450
    | simpa using h501

private lemma threeThree_q233_shiftedConsecutiveTriple_floor
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (start : Fin 6) :
    minTri cfg ≤ sig (cfg (cycle start)) (cfg (cycle (start + 1)))
      (cfg (cycle (start + 2))) := by
  have h01 : start ≠ start + 1 := by
    fin_cases start <;> decide
  have h02 : start ≠ start + 2 := by
    fin_cases start <;> decide
  have h12 : start + 1 ≠ start + 2 := by
    fin_cases start <;> decide
  exact minTri_le_pos_sig_of_pairwise_ne cfg
    (R.cycle_injective.ne h01) (R.cycle_injective.ne h02)
    (R.cycle_injective.ne h12)
    (threeThree_q233_shiftedConsecutiveTriple_pos R start)

/-! The four determinant identities specific to the Y01-positive scalar
certificate.  They reuse the shared fan/path identities and base change,
keeping the underlying determinants atomic. -/

private lemma sig_threeThree_q233_qUpper01_identity
    (P Q U0 U1 L0 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU0 : sig P Q U0 ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeUpperHeight P Q U1 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m) +
        hullSixThreeThreeUpperHeight P Q U0 m -
          hullSixThreeThreeUpperHeight P Q U1 m =
      sig Q U0 U1 / m := by
  have hP := sig_threeThree_qBlind_upper01_identity
    P Q U0 U1 L0 hm hU0 hU1 hL0
  have hbase :
      sig Q U0 U1 / m = sig P U0 U1 / m +
        hullSixThreeThreeUpperHeight P Q U0 m -
          hullSixThreeThreeUpperHeight P Q U1 m := by
    rw [sig_crossChord_base_change P Q U0 U1]
    simp only [hullSixThreeThreeUpperHeight]
    ring
  calc
    hullSixThreeThreeUpperHeight P Q U0 m *
            hullSixThreeThreeUpperHeight P Q U1 m *
              (hullSixThreeThreeRGap P Q U0 L0 m +
                hullSixThreeThreeSGap P Q U1 L0 m) +
          hullSixThreeThreeUpperHeight P Q U0 m -
            hullSixThreeThreeUpperHeight P Q U1 m =
        sig P U0 U1 / m +
          hullSixThreeThreeUpperHeight P Q U0 m -
            hullSixThreeThreeUpperHeight P Q U1 m := by rw [hP]
    _ = sig Q U0 U1 / m := hbase.symm

private lemma sig_threeThree_q233_qY01Pos_identity
    (P Q U0 U1 U2 L0 L1 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU0 : sig P Q U0 ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hU2 : sig P Q U2 ≠ 0) (hL0 : sig P Q L0 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m +
          hullSixThreeThreeLowerHeight P Q L1 m -
        hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeTGap P Q U1 U2 m +
                  hullSixThreeThreeWGap P Q U2 L1 m) =
      sig Q U0 L1 / m := by
  have hneg := sig_threeThree_qBlind_qY01Neg_identity
    P Q U0 U1 U2 L0 L1 hm hU0 hU1 hU2 hL0 hL1
  calc
    hullSixThreeThreeUpperHeight P Q U0 m +
          hullSixThreeThreeLowerHeight P Q L1 m -
        hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeTGap P Q U1 U2 m +
                  hullSixThreeThreeWGap P Q U2 L1 m) =
        -(hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeTGap P Q U1 U2 m +
                  hullSixThreeThreeWGap P Q U2 L1 m) -
          hullSixThreeThreeUpperHeight P Q U0 m -
            hullSixThreeThreeLowerHeight P Q L1 m) := by ring
    _ = -((-sig Q U0 L1) / m) := by rw [hneg]
    _ = sig Q U0 L1 / m := by ring

private lemma sig_threeThree_q233_qY02Neg_identity
    (P Q U0 U1 U2 L0 L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU0 : sig P Q U0 ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hU2 : sig P Q U2 ≠ 0) (hL0 : sig P Q L0 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeTGap P Q U1 U2 m +
                  hullSixThreeThreeWGap P Q U2 L1 m +
                    hullSixThreeThreeZGap P Q L1 L2 m) -
        hullSixThreeThreeUpperHeight P Q U0 m -
          hullSixThreeThreeLowerHeight P Q L2 m =
      (-sig Q U0 L2) / m := by
  have hwrap := sig_threeThree_qBlind_wrap_identity
    P Q U0 U1 U2 L0 L1 L2 hm
      hU0 hU1 hU2 hL0 hL1 hL2
  have hbase :
      (-sig Q U0 L2) / m = sig P L2 U0 / m -
        hullSixThreeThreeUpperHeight P Q U0 m -
          hullSixThreeThreeLowerHeight P Q L2 m := by
    rw [sig_crossChord_base_change P Q U0 L2, sig_swap P U0 L2]
    simp only [hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    ring
  calc
    hullSixThreeThreeUpperHeight P Q U0 m *
            hullSixThreeThreeLowerHeight P Q L2 m *
              (hullSixThreeThreeRGap P Q U0 L0 m +
                hullSixThreeThreeSGap P Q U1 L0 m +
                  hullSixThreeThreeTGap P Q U1 U2 m +
                    hullSixThreeThreeWGap P Q U2 L1 m +
                      hullSixThreeThreeZGap P Q L1 L2 m) -
          hullSixThreeThreeUpperHeight P Q U0 m -
            hullSixThreeThreeLowerHeight P Q L2 m =
        sig P L2 U0 / m -
          hullSixThreeThreeUpperHeight P Q U0 m -
            hullSixThreeThreeLowerHeight P Q L2 m := by rw [hwrap]
    _ = (-sig Q U0 L2) / m := hbase.symm

private lemma sig_threeThree_q233_lowerEar_identity
    (P Q U1 U2 L0 L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hU2 : sig P Q U2 ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) (hL1 : sig P Q L1 ≠ 0)
    (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeLowerHeight P Q L0 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            (hullSixThreeThreeSGap P Q U1 L0 m +
              hullSixThreeThreeTGap P Q U1 U2 m +
                hullSixThreeThreeWGap P Q U2 L1 m) +
        hullSixThreeThreeLowerHeight P Q L1 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            hullSixThreeThreeZGap P Q L1 L2 m -
        hullSixThreeThreeLowerHeight P Q L0 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            (hullSixThreeThreeSGap P Q U1 L0 m +
              hullSixThreeThreeTGap P Q U1 U2 m +
                hullSixThreeThreeWGap P Q U2 L1 m +
                  hullSixThreeThreeZGap P Q L1 L2 m) =
      sig L0 L1 L2 / m := by
  have hr0 : hullSixThreeThreeRGap P Q L0 L0 m = 0 := by
    simp [hullSixThreeThreeRGap, sig]
  have hUpperLower :
      hullSixThreeThreeUpperHeight P Q L0 m =
        -hullSixThreeThreeLowerHeight P Q L0 m := by
    simp only [hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    ring
  have hlongRaw := sig_threeThree_qBlind_wrap_identity
    P Q L0 U1 U2 L0 L1 L2 hm
      hL0 hU1 hU2 hL0 hL1 hL2
  simp only [hr0, zero_add] at hlongRaw
  rw [hUpperLower] at hlongRaw
  have hlong :
      hullSixThreeThreeLowerHeight P Q L0 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            (hullSixThreeThreeSGap P Q U1 L0 m +
              hullSixThreeThreeTGap P Q U1 U2 m +
                hullSixThreeThreeWGap P Q U2 L1 m +
                  hullSixThreeThreeZGap P Q L1 L2 m) =
        sig P L0 L2 / m := by
    calc
      hullSixThreeThreeLowerHeight P Q L0 m *
            hullSixThreeThreeLowerHeight P Q L2 m *
              (hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeTGap P Q U1 U2 m +
                  hullSixThreeThreeWGap P Q U2 L1 m +
                    hullSixThreeThreeZGap P Q L1 L2 m) =
          -((-hullSixThreeThreeLowerHeight P Q L0 m) *
            hullSixThreeThreeLowerHeight P Q L2 m *
              (hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeTGap P Q U1 U2 m +
                  hullSixThreeThreeWGap P Q U2 L1 m +
                    hullSixThreeThreeZGap P Q L1 L2 m)) := by ring
      _ = -(sig P L2 L0 / m) := by rw [hlongRaw]
      _ = sig P L0 L2 / m := by rw [sig_swap P L2 L0]; ring
  have hLower01 := sig_threeThree_qBlind_lower01_identity
    P Q U1 U2 L0 L1 hm hU1 hU2 hL0 hL1
  have hLower12 := sig_threeThree_qBlind_lower12_identity
    P Q L1 L2 hm hL1 hL2
  have hcocycle :
      sig L0 L1 L2 / m = sig P L0 L1 / m +
        sig P L1 L2 / m - sig P L0 L2 / m := by
    rw [sig_crossChord_base_change P L0 L1 L2]
    ring
  calc
    hullSixThreeThreeLowerHeight P Q L0 m *
            hullSixThreeThreeLowerHeight P Q L1 m *
              (hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeTGap P Q U1 U2 m +
                  hullSixThreeThreeWGap P Q U2 L1 m) +
          hullSixThreeThreeLowerHeight P Q L1 m *
            hullSixThreeThreeLowerHeight P Q L2 m *
              hullSixThreeThreeZGap P Q L1 L2 m -
          hullSixThreeThreeLowerHeight P Q L0 m *
            hullSixThreeThreeLowerHeight P Q L2 m *
              (hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeTGap P Q U1 U2 m +
                  hullSixThreeThreeWGap P Q U2 L1 m +
                    hullSixThreeThreeZGap P Q L1 L2 m) =
        sig P L0 L1 / m + sig P L1 L2 / m -
          sig P L0 L2 / m := by
      rw [hLower01, hLower12, hlong]
    _ = sig L0 L1 L2 / m := hcocycle.symm

namespace HullSixCompactCrossChordResidual

/-- The five signed cells common to the q-blind `011 / 222`, `223`, and
`233` scalar certificates are incompatible with a beating compact residual. -/
theorem threeThreeQ233At_false_of_crossFloors
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
    (hX21 : sig (cfg P)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 2)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))) ≤
        -minTri cfg)
    (hY01 : minTri cfg ≤ sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset 1))))
    (hY02 : sig (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset 0)))
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
      threeThree_q233_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 1
  have hzRaw : m ≤ sig (cfg P) L1 L2 := by
    simpa [m, L1, L2, hullSixThreeThreeLowerOffset] using
      threeThree_q233_shiftedBoundary_floor R V P V.P_outside
        V.P_boundary_pos rotation 4
  have hUpper01qRaw : m ≤ sig (cfg Q) U0 U1 := by
    simpa [m, U0, U1, hullSixThreeThreeUpperOffset] using
      threeThree_q233_shiftedBoundary_floor R V Q V.Q_outside
        V.Q_boundary_pos rotation 0
  have hLowerEarRaw : m ≤ sig L0 L1 L2 := by
    simpa [m, L0, L1, L2, hullSixThreeThreeLowerOffset, add_assoc] using
      threeThree_q233_shiftedConsecutiveTriple_floor R (rotation + 3)

  have hrEq : a * d * r = (-sig (cfg P) U0 L0) / m :=
    sig_threeThree_qBlind_rCross_identity
      (cfg P) (cfg Q) U0 L0 hmNe hU0Ne hL0Ne
  have hsEq : b * d * s = sig (cfg P) U1 L0 / m :=
    sig_threeThree_qBlind_sCross_identity
      (cfg P) (cfg Q) U1 L0 hmNe hU1Ne hL0Ne
  have htEq : b * c * t = sig (cfg P) U1 U2 / m :=
    sig_threeThree_qBlind_tFan_identity
      (cfg P) (cfg Q) U1 U2 hmNe hU1Ne hU2Ne
  have hwEq : c * e * w = (-sig (cfg P) U2 L1) / m :=
    sig_threeThree_qBlind_wCross_identity
      (cfg P) (cfg Q) U2 L1 hmNe hU2Ne hL1Ne
  have hzEq : e * f * z = sig (cfg P) L1 L2 / m :=
    sig_threeThree_qBlind_zFan_identity
      (cfg P) (cfg Q) L1 L2 hmNe hL1Ne hL2Ne
  have hUpper01qEq :
      a * b * (r + s) + a - b = sig (cfg Q) U0 U1 / m :=
    sig_threeThree_q233_qUpper01_identity
      (cfg P) (cfg Q) U0 U1 L0 hmNe hU0Ne hU1Ne hL0Ne
  have hY01Eq :
      a + e - a * e * (r + s + t + w) = sig (cfg Q) U0 L1 / m :=
    sig_threeThree_q233_qY01Pos_identity
      (cfg P) (cfg Q) U0 U1 U2 L0 L1 hmNe
        hU0Ne hU1Ne hU2Ne hL0Ne hL1Ne
  have hY02Eq :
      a * f * (r + s + t + w + z) - a - f =
        (-sig (cfg Q) U0 L2) / m :=
    sig_threeThree_q233_qY02Neg_identity
      (cfg P) (cfg Q) U0 U1 U2 L0 L1 L2 hmNe
        hU0Ne hU1Ne hU2Ne hL0Ne hL1Ne hL2Ne
  have hLowerEarEq :
      d * e * (s + t + w) + e * f * z -
          d * f * (s + t + w + z) = sig L0 L1 L2 / m :=
    sig_threeThree_q233_lowerEar_identity
      (cfg P) (cfg Q) U1 U2 L0 L1 L2 hmNe
        hU1Ne hU2Ne hL0Ne hL1Ne hL2Ne

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
  have hw : 1 ≤ c * e * w := by
    rw [hwEq]
    apply hnorm
    simpa [m, U2, L1] using (show minTri cfg ≤
      -sig (cfg P) U2 L1 by
        simpa [U2, L1] using (neg_le_neg hX21))
  have hz : 1 ≤ e * f * z := by
    rw [hzEq]
    exact hnorm hzRaw
  have hUpper01q : 1 ≤ a * b * (r + s) + a - b := by
    rw [hUpper01qEq]
    exact hnorm hUpper01qRaw
  have hY01pos : 1 ≤ a + e - a * e * (r + s + t + w) := by
    rw [hY01Eq]
    exact hnorm (by simpa [m, U0, L1] using hY01)
  have hY02neg : 1 ≤ a * f * (r + s + t + w + z) - a - f := by
    rw [hY02Eq]
    apply hnorm
    simpa [m, U0, L2] using (show minTri cfg ≤
      -sig (cfg Q) U0 L2 by
        simpa [U0, L2] using (neg_le_neg hY02))
  have hLowerEar :
      1 ≤ d * e * (s + t + w) + e * f * z -
        d * f * (s + t + w + z) := by
    rw [hLowerEarEq]
    exact hnorm hLowerEarRaw

  have hscalar :
      (25 : ℝ) / 2 <
        a * b * (r + s) + b * c * t + c * d * (s + t) +
          d * e * (s + t + w) + e * f * z +
            a * f * (r + s + t + w + z) :=
    hullSixThreeThreeQ233_scalar ha1 hb1 hc1 hd1 he1 hf1
      hr hs ht hw hz hUpper01q hY01pos hY02neg hLowerEar

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

/-- The signed q-blind branch `p = 011`, `q = 222`. -/
def q222 : HullSixThreeThreeCuts where
  p0 := 0
  p1 := 1
  p2 := 1
  q0 := 2
  q1 := 2
  q2 := 2

/-- The signed q-blind branch `p = 011`, `q = 223`. -/
def q223 : HullSixThreeThreeCuts where
  p0 := 0
  p1 := 1
  p2 := 1
  q0 := 2
  q1 := 2
  q2 := 3

/-- The signed q-blind branch `p = 011`, `q = 233`. -/
def q233 : HullSixThreeThreeCuts where
  p0 := 0
  p1 := 1
  p2 := 1
  q0 := 2
  q1 := 3
  q2 := 3

end HullSixThreeThreeCuts

namespace HullSixCompactCrossChordResidual

/-- Ferrers-table wrapper for the `011 / 222` branch. -/
theorem threeThreeQ222At_false
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
    (hQ222 : ∀ i j : Fin 3,
      HullSixChamberLabel.Holds
        (HullSixThreeThreeCuts.q222.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))) :
    False := by
  have h00 := hQ222 0 0
  have h10 := hQ222 1 0
  have h21 := hQ222 2 1
  have h01 := hQ222 0 1
  have h02 := hQ222 0 2
  rw [show HullSixThreeThreeCuts.q222.table 0 0 =
    HullSixChamberLabel.M by decide] at h00
  rw [show HullSixThreeThreeCuts.q222.table 1 0 =
    HullSixChamberLabel.L by decide] at h10
  rw [show HullSixThreeThreeCuts.q222.table 2 1 =
    HullSixChamberLabel.M by decide] at h21
  rw [show HullSixThreeThreeCuts.q222.table 0 1 =
    HullSixChamberLabel.M by decide] at h01
  rw [show HullSixThreeThreeCuts.q222.table 0 2 =
    HullSixChamberLabel.R by decide] at h02
  simp only [HullSixChamberLabel.Holds] at h00 h10 h21 h01 h02
  exact R.threeThreeQ233At_false_of_crossFloors V rotation hupper hlower
    h00.1 h10 h21.1 h01.2 h02

/-- Ferrers-table wrapper for the `011 / 223` branch. -/
theorem threeThreeQ223At_false
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
    (hQ223 : ∀ i j : Fin 3,
      HullSixChamberLabel.Holds
        (HullSixThreeThreeCuts.q223.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))) :
    False := by
  have h00 := hQ223 0 0
  have h10 := hQ223 1 0
  have h21 := hQ223 2 1
  have h01 := hQ223 0 1
  have h02 := hQ223 0 2
  rw [show HullSixThreeThreeCuts.q223.table 0 0 =
    HullSixChamberLabel.M by decide] at h00
  rw [show HullSixThreeThreeCuts.q223.table 1 0 =
    HullSixChamberLabel.L by decide] at h10
  rw [show HullSixThreeThreeCuts.q223.table 2 1 =
    HullSixChamberLabel.M by decide] at h21
  rw [show HullSixThreeThreeCuts.q223.table 0 1 =
    HullSixChamberLabel.M by decide] at h01
  rw [show HullSixThreeThreeCuts.q223.table 0 2 =
    HullSixChamberLabel.R by decide] at h02
  simp only [HullSixChamberLabel.Holds] at h00 h10 h21 h01 h02
  exact R.threeThreeQ233At_false_of_crossFloors V rotation hupper hlower
    h00.1 h10 h21.1 h01.2 h02

/-- Ferrers-table wrapper for the `011 / 233` branch. -/
theorem threeThreeQ233At_false
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
    (hQ233 : ∀ i j : Fin 3,
      HullSixChamberLabel.Holds
        (HullSixThreeThreeCuts.q233.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
          (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))))) :
    False := by
  have h00 := hQ233 0 0
  have h10 := hQ233 1 0
  have h21 := hQ233 2 1
  have h01 := hQ233 0 1
  have h02 := hQ233 0 2
  rw [show HullSixThreeThreeCuts.q233.table 0 0 =
    HullSixChamberLabel.M by decide] at h00
  rw [show HullSixThreeThreeCuts.q233.table 1 0 =
    HullSixChamberLabel.L by decide] at h10
  rw [show HullSixThreeThreeCuts.q233.table 2 1 =
    HullSixChamberLabel.M by decide] at h21
  rw [show HullSixThreeThreeCuts.q233.table 0 1 =
    HullSixChamberLabel.M by decide] at h01
  rw [show HullSixThreeThreeCuts.q233.table 0 2 =
    HullSixChamberLabel.R by decide] at h02
  simp only [HullSixChamberLabel.Holds] at h00 h10 h21 h01 h02
  exact R.threeThreeQ233At_false_of_crossFloors V rotation hupper hlower
    h00.1 h10 h21.1 h01.2 h02

end HullSixCompactCrossChordResidual

end Heilbronn8
