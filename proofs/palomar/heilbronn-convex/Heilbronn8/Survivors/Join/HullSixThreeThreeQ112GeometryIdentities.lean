import Heilbronn8.Survivors.Join.HullSixThreeThreeQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixSemantic

/-!
# Determinant identities for the q-blind `011 / 112` chamber

These four identities are the Q112-specific part of the normalized
determinant-coordinate seam.  They expose the signed `Q`-chords `-Y11`,
`+Y21`, and `-Y22`, together with the mixed cyclic ear `L2 U0 U1` used by
the scalar certificate.  The proofs reuse the shared path identities and
base change, avoiding a second large rational determinant expansion.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- The negative `Y11` chord in successive-gap coordinates. -/
lemma sig_threeThree_q112_qY11Neg_identity
    (P Q U1 U2 L1 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hU2 : sig P Q U2 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U1 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            (hullSixThreeThreeTGap P Q U1 U2 m +
              hullSixThreeThreeWGap P Q U2 L1 m) -
        hullSixThreeThreeUpperHeight P Q U1 m -
          hullSixThreeThreeLowerHeight P Q L1 m =
      (-sig Q U1 L1) / m := by
  have hz :
      hullSixThreeThreeZGap P Q L1 L1 m = 0 := by
    simp [hullSixThreeThreeZGap, sig]
  have hpath :=
    sig_threeThree_qBlind_qY12Pos_identity
      P Q U1 U2 L1 L1 hm hU1 hU2 hL1 hL1
  simp only [hz, add_zero] at hpath
  calc
    hullSixThreeThreeUpperHeight P Q U1 m *
            hullSixThreeThreeLowerHeight P Q L1 m *
              (hullSixThreeThreeTGap P Q U1 U2 m +
                hullSixThreeThreeWGap P Q U2 L1 m) -
          hullSixThreeThreeUpperHeight P Q U1 m -
            hullSixThreeThreeLowerHeight P Q L1 m =
        -(hullSixThreeThreeUpperHeight P Q U1 m +
          hullSixThreeThreeLowerHeight P Q L1 m -
            hullSixThreeThreeUpperHeight P Q U1 m *
              hullSixThreeThreeLowerHeight P Q L1 m *
                (hullSixThreeThreeTGap P Q U1 U2 m +
                  hullSixThreeThreeWGap P Q U2 L1 m)) := by ring
    _ = -(sig Q U1 L1 / m) := by rw [hpath]
    _ = (-sig Q U1 L1) / m := by ring

/-- The positive `Y21` chord in successive-gap coordinates. -/
lemma sig_threeThree_q112_qY21Pos_identity
    (P Q U2 L1 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU2 : sig P Q U2 ≠ 0) (hL1 : sig P Q L1 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U2 m +
          hullSixThreeThreeLowerHeight P Q L1 m -
        hullSixThreeThreeUpperHeight P Q U2 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            hullSixThreeThreeWGap P Q U2 L1 m =
      sig Q U2 L1 / m := by
  have hpath :=
    sig_threeThree_qBlind_qY21Neg_identity
      P Q U2 L1 hm hU2 hL1
  calc
    hullSixThreeThreeUpperHeight P Q U2 m +
          hullSixThreeThreeLowerHeight P Q L1 m -
        hullSixThreeThreeUpperHeight P Q U2 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            hullSixThreeThreeWGap P Q U2 L1 m =
        -(hullSixThreeThreeUpperHeight P Q U2 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            hullSixThreeThreeWGap P Q U2 L1 m -
          hullSixThreeThreeUpperHeight P Q U2 m -
            hullSixThreeThreeLowerHeight P Q L1 m) := by ring
    _ = -((-sig Q U2 L1) / m) := by rw [hpath]
    _ = sig Q U2 L1 / m := by ring

/-- The negative `Y22` chord in successive-gap coordinates. -/
lemma sig_threeThree_q112_qY22Neg_identity
    (P Q U2 L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU2 : sig P Q U2 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U2 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            (hullSixThreeThreeWGap P Q U2 L1 m +
              hullSixThreeThreeZGap P Q L1 L2 m) -
        hullSixThreeThreeUpperHeight P Q U2 m -
          hullSixThreeThreeLowerHeight P Q L2 m =
      (-sig Q U2 L2) / m := by
  have ht :
      hullSixThreeThreeTGap P Q U2 U2 m = 0 := by
    simp [hullSixThreeThreeTGap, sig]
  have hpath :=
    sig_threeThree_qBlind_qY12Pos_identity
      P Q U2 U2 L1 L2 hm hU2 hU2 hL1 hL2
  simp only [ht, zero_add] at hpath
  calc
    hullSixThreeThreeUpperHeight P Q U2 m *
            hullSixThreeThreeLowerHeight P Q L2 m *
              (hullSixThreeThreeWGap P Q U2 L1 m +
                hullSixThreeThreeZGap P Q L1 L2 m) -
          hullSixThreeThreeUpperHeight P Q U2 m -
            hullSixThreeThreeLowerHeight P Q L2 m =
        -(hullSixThreeThreeUpperHeight P Q U2 m +
          hullSixThreeThreeLowerHeight P Q L2 m -
            hullSixThreeThreeUpperHeight P Q U2 m *
              hullSixThreeThreeLowerHeight P Q L2 m *
                (hullSixThreeThreeWGap P Q U2 L1 m +
                  hullSixThreeThreeZGap P Q L1 L2 m)) := by ring
    _ = -(sig Q U2 L2 / m) := by rw [hpath]
    _ = (-sig Q U2 L2) / m := by ring

/-- The mixed cyclic ear `L2 U0 U1` in successive-gap coordinates. -/
lemma sig_threeThree_q112_mixedEar_identity
    (P Q U0 U1 U2 L0 L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU0 : sig P Q U0 ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hU2 : sig P Q U2 ≠ 0) (hL0 : sig P Q L0 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeUpperHeight P Q U1 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m) +
        hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeTGap P Q U1 U2 m +
                  hullSixThreeThreeWGap P Q U2 L1 m +
                    hullSixThreeThreeZGap P Q L1 L2 m) -
        hullSixThreeThreeUpperHeight P Q U1 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            (hullSixThreeThreeTGap P Q U1 U2 m +
              hullSixThreeThreeWGap P Q U2 L1 m +
                hullSixThreeThreeZGap P Q L1 L2 m) =
      sig L2 U0 U1 / m := by
  have hUpper :=
    sig_threeThree_qBlind_upper01_identity
      P Q U0 U1 L0 hm hU0 hU1 hL0
  have hWrap :=
    sig_threeThree_qBlind_wrap_identity
      P Q U0 U1 U2 L0 L1 L2 hm
        hU0 hU1 hU2 hL0 hL1 hL2
  have hY12 :=
    sig_threeThree_qBlind_qY12Pos_identity
      P Q U1 U2 L1 L2 hm hU1 hU2 hL1 hL2
  have hbase :
      sig Q U1 L2 / m =
        sig P U1 L2 / m +
          hullSixThreeThreeUpperHeight P Q U1 m +
            hullSixThreeThreeLowerHeight P Q L2 m := by
    rw [sig_crossChord_base_change P Q U1 L2]
    simp only [hullSixThreeThreeUpperHeight,
      hullSixThreeThreeLowerHeight]
    ring
  have hCross :
      hullSixThreeThreeUpperHeight P Q U1 m *
            hullSixThreeThreeLowerHeight P Q L2 m *
              (hullSixThreeThreeTGap P Q U1 U2 m +
                hullSixThreeThreeWGap P Q U2 L1 m +
                  hullSixThreeThreeZGap P Q L1 L2 m) =
        -(sig P U1 L2 / m) := by
    calc
      hullSixThreeThreeUpperHeight P Q U1 m *
              hullSixThreeThreeLowerHeight P Q L2 m *
                (hullSixThreeThreeTGap P Q U1 U2 m +
                  hullSixThreeThreeWGap P Q U2 L1 m +
                    hullSixThreeThreeZGap P Q L1 L2 m) =
          hullSixThreeThreeUpperHeight P Q U1 m +
              hullSixThreeThreeLowerHeight P Q L2 m -
            (hullSixThreeThreeUpperHeight P Q U1 m +
              hullSixThreeThreeLowerHeight P Q L2 m -
                hullSixThreeThreeUpperHeight P Q U1 m *
                  hullSixThreeThreeLowerHeight P Q L2 m *
                    (hullSixThreeThreeTGap P Q U1 U2 m +
                      hullSixThreeThreeWGap P Q U2 L1 m +
                        hullSixThreeThreeZGap P Q L1 L2 m)) := by ring
      _ = hullSixThreeThreeUpperHeight P Q U1 m +
            hullSixThreeThreeLowerHeight P Q L2 m -
              sig Q U1 L2 / m := by rw [hY12]
      _ = hullSixThreeThreeUpperHeight P Q U1 m +
            hullSixThreeThreeLowerHeight P Q L2 m -
              (sig P U1 L2 / m +
                hullSixThreeThreeUpperHeight P Q U1 m +
                  hullSixThreeThreeLowerHeight P Q L2 m) := by rw [hbase]
      _ = -(sig P U1 L2 / m) := by ring
  have hcocycle :
      sig L2 U0 U1 / m =
        sig P U0 U1 / m + sig P L2 U0 / m +
          sig P U1 L2 / m := by
    rw [sig_crossChord_base_change P L2 U0 U1,
      sig_swap P L2 U1]
    ring
  calc
    hullSixThreeThreeUpperHeight P Q U0 m *
            hullSixThreeThreeUpperHeight P Q U1 m *
              (hullSixThreeThreeRGap P Q U0 L0 m +
                hullSixThreeThreeSGap P Q U1 L0 m) +
          hullSixThreeThreeUpperHeight P Q U0 m *
            hullSixThreeThreeLowerHeight P Q L2 m *
              (hullSixThreeThreeRGap P Q U0 L0 m +
                hullSixThreeThreeSGap P Q U1 L0 m +
                  hullSixThreeThreeTGap P Q U1 U2 m +
                    hullSixThreeThreeWGap P Q U2 L1 m +
                      hullSixThreeThreeZGap P Q L1 L2 m) -
          hullSixThreeThreeUpperHeight P Q U1 m *
            hullSixThreeThreeLowerHeight P Q L2 m *
              (hullSixThreeThreeTGap P Q U1 U2 m +
                hullSixThreeThreeWGap P Q U2 L1 m +
                  hullSixThreeThreeZGap P Q L1 L2 m) =
        sig P U0 U1 / m + sig P L2 U0 / m +
          sig P U1 L2 / m := by
      rw [hUpper, hWrap, hCross]
      ring
    _ = sig L2 U0 U1 / m := hcocycle.symm

end Heilbronn8
