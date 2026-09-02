import Heilbronn8.Survivors.Join.HullSixThreeThreeQBlindGeometryIdentities
import Heilbronn8.Survivors.Join.HullSixSemantic

/-!
# Normalized determinant identities for the q-blind `2 + 4` split

The `2 + 4` chamber uses the same invariant line heights and elementary
cross-gap quotients as the q-blind `3 + 3` chamber.  We deliberately reuse
that coordinate API rather than introduce a second copy.

For the cyclic order `U0,U1,L0,L1,L2,L3`, the five successive slope gaps are

* `RGap U0 L0`,
* `SGap U1 L0`,
* `WGap U1 L1`,
* `ZGap L1 L2`, and
* `ZGap L2 L3`.

The lemmas below expose the six consecutive `P`-fan areas, their six
base-changed `Q`-fan areas, the eight `Q` cross cells, and the two lower
hull ears.  Long path identities are assembled from the already proved
`3 + 3` identities and two small gap-concatenation seams; no eight-point
coordinate expansion is used.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-! ## Successive-gap concatenation -/

/-- A cross-to-lower gap followed by one lower gap is the longer cross gap. -/
lemma hullSixTwoFour_wzGap_concat
    (P Q U L0 L1 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU : sig P Q U ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) (hL1 : sig P Q L1 ≠ 0) :
    hullSixThreeThreeWGap P Q U L1 m =
      hullSixThreeThreeWGap P Q U L0 m +
        hullSixThreeThreeZGap P Q L0 L1 m := by
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight, hullSixThreeThreeWGap,
    hullSixThreeThreeZGap]
  field_simp [hm, hU, hL0, hL1] <;>
    simp only [sig] <;> ring

/-- Two consecutive lower gaps concatenate to the longer lower gap. -/
lemma hullSixTwoFour_zzGap_concat
    (P Q L0 L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hL0 : sig P Q L0 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeZGap P Q L0 L2 m =
      hullSixThreeThreeZGap P Q L0 L1 m +
        hullSixThreeThreeZGap P Q L1 L2 m := by
  simp only [hullSixThreeThreeLowerHeight, hullSixThreeThreeZGap]
  field_simp [hm, hL0, hL1, hL2] <;>
    simp only [sig] <;> ring

/-! ## The six consecutive `P`-fan identities -/

lemma sig_twoFour_qBlind_upper_identity
    (P Q U0 U1 L0 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU0 : sig P Q U0 ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hL0 : sig P Q L0 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m *
        hullSixThreeThreeUpperHeight P Q U1 m *
          (hullSixThreeThreeRGap P Q U0 L0 m +
            hullSixThreeThreeSGap P Q U1 L0 m) =
      sig P U0 U1 / m :=
  sig_threeThree_qBlind_upper01_identity
    P Q U0 U1 L0 hm hU0 hU1 hL0

lemma sig_twoFour_qBlind_cross_identity
    (P Q U1 L0 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U1 m *
        hullSixThreeThreeLowerHeight P Q L0 m *
          hullSixThreeThreeSGap P Q U1 L0 m =
      sig P U1 L0 / m :=
  sig_threeThree_qBlind_sCross_identity P Q U1 L0 hm hU1 hL0

lemma sig_twoFour_qBlind_lower01_identity
    (P Q U1 L0 L1 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) (hL1 : sig P Q L1 ≠ 0) :
    hullSixThreeThreeLowerHeight P Q L0 m *
        hullSixThreeThreeLowerHeight P Q L1 m *
          (hullSixThreeThreeSGap P Q U1 L0 m +
            hullSixThreeThreeWGap P Q U1 L1 m) =
      sig P L0 L1 / m := by
  have ht : hullSixThreeThreeTGap P Q U1 U1 m = 0 := by
    simp [hullSixThreeThreeTGap, sig]
  have hpath := sig_threeThree_qBlind_lower01_identity
    P Q U1 U1 L0 L1 hm hU1 hU1 hL0 hL1
  simpa only [ht, add_zero] using hpath

lemma sig_twoFour_qBlind_lower12_identity
    (P Q L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hL1 : sig P Q L1 ≠ 0)
    (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeLowerHeight P Q L1 m *
        hullSixThreeThreeLowerHeight P Q L2 m *
          hullSixThreeThreeZGap P Q L1 L2 m =
      sig P L1 L2 / m :=
  sig_threeThree_qBlind_lower12_identity P Q L1 L2 hm hL1 hL2

lemma sig_twoFour_qBlind_lower23_identity
    (P Q L2 L3 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hL2 : sig P Q L2 ≠ 0)
    (hL3 : sig P Q L3 ≠ 0) :
    hullSixThreeThreeLowerHeight P Q L2 m *
        hullSixThreeThreeLowerHeight P Q L3 m *
          hullSixThreeThreeZGap P Q L2 L3 m =
      sig P L2 L3 / m :=
  sig_threeThree_qBlind_lower12_identity P Q L2 L3 hm hL2 hL3

lemma sig_twoFour_qBlind_wrap_identity
    (P Q U0 U1 L0 L1 L2 L3 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU0 : sig P Q U0 ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hL0 : sig P Q L0 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0)
    (hL3 : sig P Q L3 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m *
        hullSixThreeThreeLowerHeight P Q L3 m *
          (hullSixThreeThreeRGap P Q U0 L0 m +
            hullSixThreeThreeSGap P Q U1 L0 m +
              hullSixThreeThreeWGap P Q U1 L1 m +
                hullSixThreeThreeZGap P Q L1 L2 m +
                  hullSixThreeThreeZGap P Q L2 L3 m) =
      sig P L3 U0 / m := by
  have ht : hullSixThreeThreeTGap P Q U1 U1 m = 0 := by
    simp [hullSixThreeThreeTGap, sig]
  have hz := hullSixTwoFour_zzGap_concat
    P Q L1 L2 L3 hm hL1 hL2 hL3
  have hpath := sig_threeThree_qBlind_wrap_identity
    P Q U0 U1 U1 L0 L1 L3 hm
      hU0 hU1 hU1 hL0 hL1 hL3
  rw [ht, add_zero, hz] at hpath
  simpa only [add_assoc] using hpath

/-! ## A shared normalized base-change seam -/

lemma sig_twoFour_qBlind_base_change
    (P Q A B : ℝ × ℝ) {m : ℝ} :
    sig Q A B / m =
      sig P A B / m + sig P Q A / m - sig P Q B / m := by
  rw [sig_crossChord_base_change P Q A B]
  ring

/-! ## The six consecutive `Q`-fan identities -/

lemma sig_twoFour_qBlind_qUpper_identity
    (P Q U0 U1 L0 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU0 : sig P Q U0 ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hL0 : sig P Q L0 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeUpperHeight P Q U1 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m) +
        hullSixThreeThreeUpperHeight P Q U0 m -
          hullSixThreeThreeUpperHeight P Q U1 m =
      sig Q U0 U1 / m := by
  rw [sig_twoFour_qBlind_upper_identity P Q U0 U1 L0 hm hU0 hU1 hL0,
    sig_twoFour_qBlind_base_change P Q U0 U1]
  simp only [hullSixThreeThreeUpperHeight]

lemma sig_twoFour_qBlind_qCross_identity
    (P Q U1 L0 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U1 m *
          hullSixThreeThreeLowerHeight P Q L0 m *
            hullSixThreeThreeSGap P Q U1 L0 m +
        hullSixThreeThreeUpperHeight P Q U1 m +
          hullSixThreeThreeLowerHeight P Q L0 m =
      sig Q U1 L0 / m := by
  rw [sig_twoFour_qBlind_cross_identity P Q U1 L0 hm hU1 hL0,
    sig_twoFour_qBlind_base_change P Q U1 L0]
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight]
  ring

lemma sig_twoFour_qBlind_qLower01_identity
    (P Q U1 L0 L1 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) (hL1 : sig P Q L1 ≠ 0) :
    hullSixThreeThreeLowerHeight P Q L0 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            (hullSixThreeThreeSGap P Q U1 L0 m +
              hullSixThreeThreeWGap P Q U1 L1 m) -
        hullSixThreeThreeLowerHeight P Q L0 m +
          hullSixThreeThreeLowerHeight P Q L1 m =
      sig Q L0 L1 / m := by
  rw [sig_twoFour_qBlind_lower01_identity P Q U1 L0 L1 hm hU1 hL0 hL1,
    sig_twoFour_qBlind_base_change P Q L0 L1]
  simp only [hullSixThreeThreeLowerHeight]
  ring

lemma sig_twoFour_qBlind_qLower12_identity
    (P Q L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hL1 : sig P Q L1 ≠ 0)
    (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeLowerHeight P Q L1 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            hullSixThreeThreeZGap P Q L1 L2 m -
        hullSixThreeThreeLowerHeight P Q L1 m +
          hullSixThreeThreeLowerHeight P Q L2 m =
      sig Q L1 L2 / m := by
  rw [sig_twoFour_qBlind_lower12_identity P Q L1 L2 hm hL1 hL2,
    sig_twoFour_qBlind_base_change P Q L1 L2]
  simp only [hullSixThreeThreeLowerHeight]
  ring

lemma sig_twoFour_qBlind_qLower23_identity
    (P Q L2 L3 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hL2 : sig P Q L2 ≠ 0)
    (hL3 : sig P Q L3 ≠ 0) :
    hullSixThreeThreeLowerHeight P Q L2 m *
          hullSixThreeThreeLowerHeight P Q L3 m *
            hullSixThreeThreeZGap P Q L2 L3 m -
        hullSixThreeThreeLowerHeight P Q L2 m +
          hullSixThreeThreeLowerHeight P Q L3 m =
      sig Q L2 L3 / m := by
  rw [sig_twoFour_qBlind_lower23_identity P Q L2 L3 hm hL2 hL3,
    sig_twoFour_qBlind_base_change P Q L2 L3]
  simp only [hullSixThreeThreeLowerHeight]
  ring

lemma sig_twoFour_qBlind_qWrap_identity
    (P Q U0 U1 L0 L1 L2 L3 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU0 : sig P Q U0 ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hL0 : sig P Q L0 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0)
    (hL3 : sig P Q L3 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeLowerHeight P Q L3 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeWGap P Q U1 L1 m +
                  hullSixThreeThreeZGap P Q L1 L2 m +
                    hullSixThreeThreeZGap P Q L2 L3 m) -
        hullSixThreeThreeUpperHeight P Q U0 m -
          hullSixThreeThreeLowerHeight P Q L3 m =
      sig Q L3 U0 / m := by
  rw [sig_twoFour_qBlind_wrap_identity
      P Q U0 U1 L0 L1 L2 L3 hm hU0 hU1 hL0 hL1 hL2 hL3,
    sig_twoFour_qBlind_base_change P Q L3 U0]
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight]
  ring

/-! ## The eight `Q` cross-cell identities -/

lemma sig_twoFour_qBlind_qY00_identity
    (P Q U0 L0 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU0 : sig P Q U0 ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m +
          hullSixThreeThreeLowerHeight P Q L0 m -
        hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeLowerHeight P Q L0 m *
            hullSixThreeThreeRGap P Q U0 L0 m =
      sig Q U0 L0 / m := by
  have hcross := sig_threeThree_qBlind_rCross_identity
    P Q U0 L0 hm hU0 hL0
  rw [sig_twoFour_qBlind_base_change P Q U0 L0]
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight] at hcross ⊢
  rw [hcross]
  ring

lemma sig_twoFour_qBlind_qY01_identity
    (P Q U0 U1 L0 L1 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU0 : sig P Q U0 ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hL0 : sig P Q L0 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m +
          hullSixThreeThreeLowerHeight P Q L1 m -
        hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeWGap P Q U1 L1 m) =
      sig Q U0 L1 / m := by
  have ht : hullSixThreeThreeTGap P Q U1 U1 m = 0 := by
    simp [hullSixThreeThreeTGap, sig]
  have hpath := sig_threeThree_qBlind_qY01Neg_identity
    P Q U0 U1 U1 L0 L1 hm hU0 hU1 hU1 hL0 hL1
  simp only [ht, add_zero] at hpath
  calc
    hullSixThreeThreeUpperHeight P Q U0 m +
            hullSixThreeThreeLowerHeight P Q L1 m -
          hullSixThreeThreeUpperHeight P Q U0 m *
            hullSixThreeThreeLowerHeight P Q L1 m *
              (hullSixThreeThreeRGap P Q U0 L0 m +
                hullSixThreeThreeSGap P Q U1 L0 m +
                  hullSixThreeThreeWGap P Q U1 L1 m) =
        -(hullSixThreeThreeUpperHeight P Q U0 m *
            hullSixThreeThreeLowerHeight P Q L1 m *
              (hullSixThreeThreeRGap P Q U0 L0 m +
                hullSixThreeThreeSGap P Q U1 L0 m +
                  hullSixThreeThreeWGap P Q U1 L1 m) -
          hullSixThreeThreeUpperHeight P Q U0 m -
            hullSixThreeThreeLowerHeight P Q L1 m) := by ring
    _ = -((-sig Q U0 L1) / m) := by rw [hpath]
    _ = sig Q U0 L1 / m := by ring

lemma sig_twoFour_qBlind_qY02_identity
    (P Q U0 U1 L0 L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU0 : sig P Q U0 ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hL0 : sig P Q L0 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m +
          hullSixThreeThreeLowerHeight P Q L2 m -
        hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeWGap P Q U1 L1 m +
                  hullSixThreeThreeZGap P Q L1 L2 m) =
      sig Q U0 L2 / m := by
  have ht : hullSixThreeThreeTGap P Q U1 U1 m = 0 := by
    simp [hullSixThreeThreeTGap, sig]
  have hw := hullSixTwoFour_wzGap_concat
    P Q U1 L1 L2 hm hU1 hL1 hL2
  have hpath := sig_threeThree_qBlind_qY01Neg_identity
    P Q U0 U1 U1 L0 L2 hm hU0 hU1 hU1 hL0 hL2
  rw [ht, add_zero, hw] at hpath
  have hpath' :
      hullSixThreeThreeUpperHeight P Q U0 m *
            hullSixThreeThreeLowerHeight P Q L2 m *
              (hullSixThreeThreeRGap P Q U0 L0 m +
                hullSixThreeThreeSGap P Q U1 L0 m +
                  hullSixThreeThreeWGap P Q U1 L1 m +
                    hullSixThreeThreeZGap P Q L1 L2 m) -
          hullSixThreeThreeUpperHeight P Q U0 m -
            hullSixThreeThreeLowerHeight P Q L2 m =
        (-sig Q U0 L2) / m := by
    nlinarith only [hpath]
  calc
    hullSixThreeThreeUpperHeight P Q U0 m +
            hullSixThreeThreeLowerHeight P Q L2 m -
          hullSixThreeThreeUpperHeight P Q U0 m *
            hullSixThreeThreeLowerHeight P Q L2 m *
              (hullSixThreeThreeRGap P Q U0 L0 m +
                hullSixThreeThreeSGap P Q U1 L0 m +
                  hullSixThreeThreeWGap P Q U1 L1 m +
                    hullSixThreeThreeZGap P Q L1 L2 m) =
        -(hullSixThreeThreeUpperHeight P Q U0 m *
            hullSixThreeThreeLowerHeight P Q L2 m *
              (hullSixThreeThreeRGap P Q U0 L0 m +
                hullSixThreeThreeSGap P Q U1 L0 m +
                  hullSixThreeThreeWGap P Q U1 L1 m +
                    hullSixThreeThreeZGap P Q L1 L2 m) -
          hullSixThreeThreeUpperHeight P Q U0 m -
            hullSixThreeThreeLowerHeight P Q L2 m) := by ring
    _ = -((-sig Q U0 L2) / m) := by rw [hpath']
    _ = sig Q U0 L2 / m := by ring

lemma sig_twoFour_qBlind_qY03_identity
    (P Q U0 U1 L0 L1 L2 L3 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU0 : sig P Q U0 ≠ 0)
    (hU1 : sig P Q U1 ≠ 0) (hL0 : sig P Q L0 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0)
    (hL3 : sig P Q L3 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U0 m +
          hullSixThreeThreeLowerHeight P Q L3 m -
        hullSixThreeThreeUpperHeight P Q U0 m *
          hullSixThreeThreeLowerHeight P Q L3 m *
            (hullSixThreeThreeRGap P Q U0 L0 m +
              hullSixThreeThreeSGap P Q U1 L0 m +
                hullSixThreeThreeWGap P Q U1 L1 m +
                  hullSixThreeThreeZGap P Q L1 L2 m +
                    hullSixThreeThreeZGap P Q L2 L3 m) =
      sig Q U0 L3 / m := by
  have ht : hullSixThreeThreeTGap P Q U1 U1 m = 0 := by
    simp [hullSixThreeThreeTGap, sig]
  have hw12 := hullSixTwoFour_wzGap_concat
    P Q U1 L1 L2 hm hU1 hL1 hL2
  have hw23 := hullSixTwoFour_wzGap_concat
    P Q U1 L2 L3 hm hU1 hL2 hL3
  have hpath := sig_threeThree_qBlind_qY01Neg_identity
    P Q U0 U1 U1 L0 L3 hm hU0 hU1 hU1 hL0 hL3
  rw [ht, add_zero, hw23, hw12] at hpath
  have hpath' :
      hullSixThreeThreeUpperHeight P Q U0 m *
            hullSixThreeThreeLowerHeight P Q L3 m *
              (hullSixThreeThreeRGap P Q U0 L0 m +
                hullSixThreeThreeSGap P Q U1 L0 m +
                  hullSixThreeThreeWGap P Q U1 L1 m +
                    hullSixThreeThreeZGap P Q L1 L2 m +
                      hullSixThreeThreeZGap P Q L2 L3 m) -
          hullSixThreeThreeUpperHeight P Q U0 m -
            hullSixThreeThreeLowerHeight P Q L3 m =
        (-sig Q U0 L3) / m := by
    nlinarith only [hpath]
  calc
    hullSixThreeThreeUpperHeight P Q U0 m +
            hullSixThreeThreeLowerHeight P Q L3 m -
          hullSixThreeThreeUpperHeight P Q U0 m *
            hullSixThreeThreeLowerHeight P Q L3 m *
              (hullSixThreeThreeRGap P Q U0 L0 m +
                hullSixThreeThreeSGap P Q U1 L0 m +
                  hullSixThreeThreeWGap P Q U1 L1 m +
                    hullSixThreeThreeZGap P Q L1 L2 m +
                      hullSixThreeThreeZGap P Q L2 L3 m) =
        -(hullSixThreeThreeUpperHeight P Q U0 m *
            hullSixThreeThreeLowerHeight P Q L3 m *
              (hullSixThreeThreeRGap P Q U0 L0 m +
                hullSixThreeThreeSGap P Q U1 L0 m +
                  hullSixThreeThreeWGap P Q U1 L1 m +
                    hullSixThreeThreeZGap P Q L1 L2 m +
                      hullSixThreeThreeZGap P Q L2 L3 m) -
          hullSixThreeThreeUpperHeight P Q U0 m -
            hullSixThreeThreeLowerHeight P Q L3 m) := by ring
    _ = -((-sig Q U0 L3) / m) := by rw [hpath']
    _ = sig Q U0 L3 / m := by ring

lemma sig_twoFour_qBlind_qY10_identity
    (P Q U1 L0 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U1 m *
          hullSixThreeThreeLowerHeight P Q L0 m *
            hullSixThreeThreeSGap P Q U1 L0 m +
        hullSixThreeThreeUpperHeight P Q U1 m +
          hullSixThreeThreeLowerHeight P Q L0 m =
      sig Q U1 L0 / m :=
  sig_twoFour_qBlind_qCross_identity P Q U1 L0 hm hU1 hL0

lemma sig_twoFour_qBlind_qY11_identity
    (P Q U1 L1 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U1 m +
          hullSixThreeThreeLowerHeight P Q L1 m -
        hullSixThreeThreeUpperHeight P Q U1 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            hullSixThreeThreeWGap P Q U1 L1 m =
      sig Q U1 L1 / m := by
  have hpath := sig_threeThree_qBlind_qY21Neg_identity
    P Q U1 L1 hm hU1 hL1
  calc
    hullSixThreeThreeUpperHeight P Q U1 m +
            hullSixThreeThreeLowerHeight P Q L1 m -
          hullSixThreeThreeUpperHeight P Q U1 m *
            hullSixThreeThreeLowerHeight P Q L1 m *
              hullSixThreeThreeWGap P Q U1 L1 m =
        -(hullSixThreeThreeUpperHeight P Q U1 m *
            hullSixThreeThreeLowerHeight P Q L1 m *
              hullSixThreeThreeWGap P Q U1 L1 m -
          hullSixThreeThreeUpperHeight P Q U1 m -
            hullSixThreeThreeLowerHeight P Q L1 m) := by ring
    _ = -((-sig Q U1 L1) / m) := by rw [hpath]
    _ = sig Q U1 L1 / m := by ring

lemma sig_twoFour_qBlind_qY12_identity
    (P Q U1 L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U1 m +
          hullSixThreeThreeLowerHeight P Q L2 m -
        hullSixThreeThreeUpperHeight P Q U1 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            (hullSixThreeThreeWGap P Q U1 L1 m +
              hullSixThreeThreeZGap P Q L1 L2 m) =
      sig Q U1 L2 / m := by
  have ht : hullSixThreeThreeTGap P Q U1 U1 m = 0 := by
    simp [hullSixThreeThreeTGap, sig]
  have hpath := sig_threeThree_qBlind_qY12Pos_identity
    P Q U1 U1 L1 L2 hm hU1 hU1 hL1 hL2
  simpa only [ht, zero_add] using hpath

lemma sig_twoFour_qBlind_qY13_identity
    (P Q U1 L1 L2 L3 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hL1 : sig P Q L1 ≠ 0) (hL2 : sig P Q L2 ≠ 0)
    (hL3 : sig P Q L3 ≠ 0) :
    hullSixThreeThreeUpperHeight P Q U1 m +
          hullSixThreeThreeLowerHeight P Q L3 m -
        hullSixThreeThreeUpperHeight P Q U1 m *
          hullSixThreeThreeLowerHeight P Q L3 m *
            (hullSixThreeThreeWGap P Q U1 L1 m +
              hullSixThreeThreeZGap P Q L1 L2 m +
                hullSixThreeThreeZGap P Q L2 L3 m) =
      sig Q U1 L3 / m := by
  have ht : hullSixThreeThreeTGap P Q U1 U1 m = 0 := by
    simp [hullSixThreeThreeTGap, sig]
  have hz := hullSixTwoFour_zzGap_concat
    P Q L1 L2 L3 hm hL1 hL2 hL3
  have hpath := sig_threeThree_qBlind_qY12Pos_identity
    P Q U1 U1 L1 L3 hm hU1 hU1 hL1 hL3
  rw [ht, zero_add, hz] at hpath
  simpa only [add_assoc] using hpath

/-! ## The two lower consecutive hull ears -/

lemma sig_twoFour_qBlind_lowerEar012_identity
    (P Q U1 L0 L1 L2 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hU1 : sig P Q U1 ≠ 0)
    (hL0 : sig P Q L0 ≠ 0) (hL1 : sig P Q L1 ≠ 0)
    (hL2 : sig P Q L2 ≠ 0) :
    (hullSixThreeThreeLowerHeight P Q L1 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            hullSixThreeThreeZGap P Q L1 L2 m) *
        (hullSixThreeThreeLowerHeight P Q L1 m -
          hullSixThreeThreeLowerHeight P Q L0 m) -
      (hullSixThreeThreeLowerHeight P Q L0 m *
          hullSixThreeThreeLowerHeight P Q L1 m *
            (hullSixThreeThreeSGap P Q U1 L0 m +
              hullSixThreeThreeWGap P Q U1 L1 m)) *
        (hullSixThreeThreeLowerHeight P Q L2 m -
          hullSixThreeThreeLowerHeight P Q L1 m) =
      hullSixThreeThreeLowerHeight P Q L1 m *
        (sig L0 L1 L2 / m) := by
  simp only [hullSixThreeThreeUpperHeight,
    hullSixThreeThreeLowerHeight, hullSixThreeThreeSGap,
    hullSixThreeThreeWGap, hullSixThreeThreeZGap]
  field_simp [hm, hU1, hL0, hL1, hL2] <;>
    simp only [sig] <;> ring

lemma sig_twoFour_qBlind_lowerEar123_identity
    (P Q L1 L2 L3 : ℝ × ℝ) {m : ℝ}
    (hm : m ≠ 0) (hL1 : sig P Q L1 ≠ 0)
    (hL2 : sig P Q L2 ≠ 0) (hL3 : sig P Q L3 ≠ 0) :
    (hullSixThreeThreeLowerHeight P Q L2 m *
          hullSixThreeThreeLowerHeight P Q L3 m *
            hullSixThreeThreeZGap P Q L2 L3 m) *
        (hullSixThreeThreeLowerHeight P Q L2 m -
          hullSixThreeThreeLowerHeight P Q L1 m) -
      (hullSixThreeThreeLowerHeight P Q L1 m *
          hullSixThreeThreeLowerHeight P Q L2 m *
            hullSixThreeThreeZGap P Q L1 L2 m) *
        (hullSixThreeThreeLowerHeight P Q L3 m -
          hullSixThreeThreeLowerHeight P Q L2 m) =
      hullSixThreeThreeLowerHeight P Q L2 m *
        (sig L1 L2 L3 / m) := by
  simp only [hullSixThreeThreeLowerHeight, hullSixThreeThreeZGap]
  field_simp [hm, hL1, hL2, hL3] <;>
    simp only [sig] <;> ring

end Heilbronn8
