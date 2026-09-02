import Heilbronn8.Defs

/-!
# Normalized determinant coordinates for the q-blind `3 x 3` chambers

Fix two base points `P,Q`, upper vertices `U0,U1,U2`, lower vertices
`L0,L1,L2`, and a nonzero area scale `m`.  The six positive line heights
and the five successive slope gaps are defined invariantly from signed
areas.  This is the coordinate seam used by the scalar q-blind certificates;
no affine normalization is needed in their geometric adapters.

The first six identities reconstruct the six consecutive `P`-fan areas.
The remaining identities expose the cross-chord and `Q`-fan expressions
which occur as scalar hypotheses.  Every proof is a determinant identity.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Normalized positive-side line height. -/
noncomputable def hullSixThreeThreeUpperHeight
    (P Q U : ℝ × ℝ) (m : ℝ) : ℝ :=
  sig P Q U / m

/-- Normalized negative-side line height, with its sign reversed. -/
noncomputable def hullSixThreeThreeLowerHeight
    (P Q L : ℝ × ℝ) (m : ℝ) : ℝ :=
  (-sig P Q L) / m

/-- Gap between `U0` and `L0`, measured by the negative `X00` chord. -/
noncomputable def hullSixThreeThreeRGap
    (P Q U0 L0 : ℝ × ℝ) (m : ℝ) : ℝ :=
  ((-sig P U0 L0) / m) /
    (hullSixThreeThreeUpperHeight P Q U0 m *
      hullSixThreeThreeLowerHeight P Q L0 m)

/-- Gap between `L0` and `U1`, measured by the positive `X10` chord. -/
noncomputable def hullSixThreeThreeSGap
    (P Q U1 L0 : ℝ × ℝ) (m : ℝ) : ℝ :=
  (sig P U1 L0 / m) /
    (hullSixThreeThreeUpperHeight P Q U1 m *
      hullSixThreeThreeLowerHeight P Q L0 m)

/-- Consecutive upper gap, measured by the `P`-fan triangle `U1 U2`. -/
noncomputable def hullSixThreeThreeTGap
    (P Q U1 U2 : ℝ × ℝ) (m : ℝ) : ℝ :=
  (sig P U1 U2 / m) /
    (hullSixThreeThreeUpperHeight P Q U1 m *
      hullSixThreeThreeUpperHeight P Q U2 m)

/-- Gap between `U2` and `L1`, measured by the negative `X21` chord. -/
noncomputable def hullSixThreeThreeWGap
    (P Q U2 L1 : ℝ × ℝ) (m : ℝ) : ℝ :=
  ((-sig P U2 L1) / m) /
    (hullSixThreeThreeUpperHeight P Q U2 m *
      hullSixThreeThreeLowerHeight P Q L1 m)

/-- Consecutive lower gap, measured by the `P`-fan triangle `L1 L2`. -/
noncomputable def hullSixThreeThreeZGap
    (P Q L1 L2 : ℝ × ℝ) (m : ℝ) : ℝ :=
  (sig P L1 L2 / m) /
    (hullSixThreeThreeLowerHeight P Q L1 m *
      hullSixThreeThreeLowerHeight P Q L2 m)

/-! ## The six consecutive hull-fan identities -/

lemma sig_threeThree_qBlind_upper01_identity
    (P Q U0 U1 L0 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU0 : sig P Q U0 ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m *
        hullSixThreeThreeUpperHeight P Q U1 m *
          (hullSixThreeThreeRGap P Q U0 L0 m +
            hullSixThreeThreeSGap P Q U1 L0 m) =
      sig P U0 U1 / m := by
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight, hullSixThreeThreeRGap,
    hullSixThreeThreeSGap]
  field_simp [hm, hU0, hU1, hL0] <;>
    simp only [sig] <;> ring

lemma sig_threeThree_qBlind_upper12_identity
    (P Q U1 U2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hU2 : sig P Q U2 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U1 m *
        hullSixThreeThreeUpperHeight P Q U2 m *
          hullSixThreeThreeTGap P Q U1 U2 m =
      sig P U1 U2 / m := by
  simp only [hullSixThreeThreeUpperHeight, hullSixThreeThreeTGap]
  field_simp [hm, hU1, hU2] <;> ring

lemma sig_threeThree_qBlind_cross20_identity
    (P Q U1 U2 L0 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hU2 : sig P Q U2 ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U2 m *
        hullSixThreeThreeLowerHeight P Q L0 m *
          (hullSixThreeThreeSGap P Q U1 L0 m +
            hullSixThreeThreeTGap P Q U1 U2 m) =
      sig P U2 L0 / m := by
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight, hullSixThreeThreeSGap,
    hullSixThreeThreeTGap]
  field_simp [hm, hU1, hU2, hL0] <;>
    simp only [sig] <;> ring

lemma sig_threeThree_qBlind_lower01_identity
    (P Q U1 U2 L0 L1 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hU2 : sig P Q U2 ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) (hL1 : sig P Q L1 ≠ 0) :
    hullSixThreeThreeLowerHeight P Q L0 m *
        hullSixThreeThreeLowerHeight P Q L1 m *
          (hullSixThreeThreeSGap P Q U1 L0 m +
            hullSixThreeThreeTGap P Q U1 U2 m +
              hullSixThreeThreeWGap P Q U2 L1 m) =
      sig P L0 L1 / m := by
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight, hullSixThreeThreeSGap,
    hullSixThreeThreeTGap, hullSixThreeThreeWGap]
  field_simp [hm, hU1, hU2, hL0, hL1] <;>
    simp only [sig] <;> ring

lemma sig_threeThree_qBlind_lower12_identity
    (P Q L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeLowerHeight P Q L1 m *
        hullSixThreeThreeLowerHeight P Q L2 m *
          hullSixThreeThreeZGap P Q L1 L2 m =
      sig P L1 L2 / m := by
  simp only [hullSixThreeThreeLowerHeight, hullSixThreeThreeZGap]
  field_simp [hm, hL1, hL2] <;> ring

lemma sig_threeThree_qBlind_wrap_identity
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
                  hullSixThreeThreeZGap P Q L1 L2 m) =
      sig P L2 U0 / m := by
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight, hullSixThreeThreeRGap,
    hullSixThreeThreeSGap, hullSixThreeThreeTGap,
    hullSixThreeThreeWGap, hullSixThreeThreeZGap]
  field_simp [hm, hU0, hU1, hU2, hL0, hL1, hL2] <;>
    simp only [sig] <;> ring

/-! ## Cross-chord and base-change identities used by scalar hypotheses -/

lemma sig_threeThree_qBlind_rCross_identity
    (P Q U0 L0 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU0 : sig P Q U0 ≠ 0) (hL0 : sig P Q L0 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m *
        hullSixThreeThreeLowerHeight P Q L0 m *
          hullSixThreeThreeRGap P Q U0 L0 m =
      (-sig P U0 L0) / m := by
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight, hullSixThreeThreeRGap]
  field_simp [hm, hU0, hL0] <;> ring

lemma sig_threeThree_qBlind_sCross_identity
    (P Q U1 L0 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hL0 : sig P Q L0 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U1 m *
        hullSixThreeThreeLowerHeight P Q L0 m *
          hullSixThreeThreeSGap P Q U1 L0 m =
      sig P U1 L0 / m := by
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight, hullSixThreeThreeSGap]
  field_simp [hm, hU1, hL0] <;> ring

lemma sig_threeThree_qBlind_tFan_identity
    (P Q U1 U2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hU2 : sig P Q U2 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U1 m *
        hullSixThreeThreeUpperHeight P Q U2 m *
          hullSixThreeThreeTGap P Q U1 U2 m =
      sig P U1 U2 / m :=
  sig_threeThree_qBlind_upper12_identity P Q U1 U2 hm hU1 hU2

lemma sig_threeThree_qBlind_wCross_identity
    (P Q U2 L1 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU2 : sig P Q U2 ≠ 0) (hL1 : sig P Q L1 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U2 m *
        hullSixThreeThreeLowerHeight P Q L1 m *
          hullSixThreeThreeWGap P Q U2 L1 m =
      (-sig P U2 L1) / m := by
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight, hullSixThreeThreeWGap]
  field_simp [hm, hU2, hL1] <;> ring

lemma sig_threeThree_qBlind_zFan_identity
    (P Q L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeLowerHeight P Q L1 m *
        hullSixThreeThreeLowerHeight P Q L2 m *
          hullSixThreeThreeZGap P Q L1 L2 m =
      sig P L1 L2 / m :=
  sig_threeThree_qBlind_lower12_identity P Q L1 L2 hm hL1 hL2

/-- The primed lower fan `Q L1 L2`. -/
lemma sig_threeThree_qBlind_qLower12_identity
    (P Q L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeLowerHeight P Q L1 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            hullSixThreeThreeZGap P Q L1 L2 m +
        hullSixThreeThreeLowerHeight P Q L2 m -
          hullSixThreeThreeLowerHeight P Q L1 m =
      sig Q L1 L2 / m := by
  simp only [hullSixThreeThreeLowerHeight, hullSixThreeThreeZGap]
  field_simp [hm, hL1, hL2] <;>
    simp only [sig] <;> ring

/-- The negative `Y01` chord in successive-gap coordinates. -/
lemma sig_threeThree_qBlind_qY01Neg_identity
    (P Q U0 U1 U2 L0 L1 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU0 : sig P Q U0 ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hU2 : sig P Q U2 ≠ 0) (hL0 : sig P Q L0 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeTGap P Q U1 U2 m +
                  hullSixThreeThreeWGap P Q U2 L1 m) -
        hullSixThreeThreeUpperHeight P Q U0 m -
          hullSixThreeThreeLowerHeight P Q L1 m =
      (-sig Q U0 L1) / m := by
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight, hullSixThreeThreeRGap,
    hullSixThreeThreeSGap, hullSixThreeThreeTGap,
    hullSixThreeThreeWGap]
  field_simp [hm, hU0, hU1, hU2, hL0, hL1] <;>
    simp only [sig] <;> ring

/-- The positive `Y12` chord in successive-gap coordinates. -/
lemma sig_threeThree_qBlind_qY12Pos_identity
    (P Q U1 U2 L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hU2 : sig P Q U2 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U1 m +
          hullSixThreeThreeLowerHeight P Q L2 m -
        hullSixThreeThreeUpperHeight P Q U1 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            (hullSixThreeThreeTGap P Q U1 U2 m +
              hullSixThreeThreeWGap P Q U2 L1 m +
                hullSixThreeThreeZGap P Q L1 L2 m) =
      sig Q U1 L2 / m := by
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight, hullSixThreeThreeTGap,
    hullSixThreeThreeWGap, hullSixThreeThreeZGap]
  field_simp [hm, hU1, hU2, hL1, hL2] <;>
    simp only [sig] <;> ring

/-- The negative `Y21` chord used by the neighboring q-blind branch. -/
lemma sig_threeThree_qBlind_qY21Neg_identity
    (P Q U2 L1 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0)
    (hU2 : sig P Q U2 ≠ 0) (hL1 : sig P Q L1 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U2 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            hullSixThreeThreeWGap P Q U2 L1 m -
        hullSixThreeThreeUpperHeight P Q U2 m -
          hullSixThreeThreeLowerHeight P Q L1 m =
      (-sig Q U2 L1) / m := by
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight, hullSixThreeThreeWGap]
  field_simp [hm, hU2, hL1] <;>
    simp only [sig] <;> ring

end Heilbronn8
