import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadResiduals
import Heilbronn8.Defs

/-!
# Determinant identities for the broad `3 x 3` chamber

This file is the algebraic seam between an oriented geometric `3 + 3` view
and the positive ear residuals.  The upper vertices are `U0,U1,U2`, the
lower vertices are `L0,L1,L2`, and every displayed area is normalized by a
nonzero scale `m`.

The proofs expand `sig` and use only polynomial identities.  In particular,
they make no chamber or positivity assumption; those facts belong in the
geometric adapter.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Base change at the central cross chord.  In the scalar notation this is
`B + E = x + y`. -/
lemma sig_threeThree_broad_central_base_change
    (P Q U1 L1 : ℝ × ℝ) {m : ℝ} (hm : m ≠ 0) :
    let x := (-sig P U1 L1) / m - 1
    let y := sig Q U1 L1 / m - 1
    let B := sig P Q U1 / m - 1
    let E := (-sig P Q L1) / m - 1
    B + E = x + y := by
  dsimp
  simp only [sig]
  field_simp [hm]
  ring

/-- The `Q`-Plucker product used for the lower bound `y + 2 ≤ U*L`. -/
lemma sig_threeThree_broad_q_product_identity
    (P Q U0 U1 L1 L2 : ℝ × ℝ) {m : ℝ} (hm : m ≠ 0) :
    let y := sig Q U1 L1 / m - 1
    let U := sig Q U0 U1 / m
    let L := sig Q L1 L2 / m
    let W := y + 1
    let c := (-sig Q U0 L2) / m
    let y0 := sig Q U0 L1 / m
    let z0 := sig Q U1 L2 / m
    U * L = W * c + y0 * z0 := by
  dsimp
  simp only [sig]
  field_simp [hm]
  ring

/-- The `P`-Plucker product used for the lower bound `x + 2 ≤ v*ell`. -/
lemma sig_threeThree_broad_p_product_identity
    (P U1 U2 L0 L1 : ℝ × ℝ) {m : ℝ} (hm : m ≠ 0) :
    let x := (-sig P U1 L1) / m - 1
    let v := sig P U1 U2 / m
    let ell := sig P L0 L1 / m
    let T := x + 1
    let g := sig P U2 L0 / m
    let x0 := (-sig P U1 L0) / m
    let h0 := (-sig P U2 L1) / m
    v * ell = T * g + x0 * h0 := by
  dsimp
  simp only [sig]
  field_simp [hm]
  ring

/-- Exact upper-ear residual identity.  Its right-hand side is manifestly
nonnegative once the upper ear and the four staircase floors are supplied. -/
lemma sig_threeThree_broad_upper_earResidual_identity
    (P Q U0 U1 U2 L1 : ℝ × ℝ) {m : ℝ} (hm : m ≠ 0) :
    let x := (-sig P U1 L1) / m - 1
    let y := sig Q U1 L1 / m - 1
    let U := sig Q U0 U1 / m
    let v := sig P U1 U2 / m
    let B := sig P Q U1 / m - 1
    let E := (-sig P Q L1) / m - 1
    let TU := sig U0 U1 U2 / m
    let p0 := sig P U0 U1 / m
    let q0 := sig Q U1 U2 / m
    let y0 := sig Q U0 L1 / m
    let h0 := (-sig P U2 L1) / m
    (B + 1) * (x * y) - (x + 1) * (y + 1) +
          (B - x) * x * U + (B - y) * y * v - (E + 1) * U * v =
      (x + 1) * (y + 1) * (TU - 1) +
        (y + 1) * p0 * (h0 - 1) +
        (x + 1) * q0 * (y0 - 1) +
        (B + 1) * (y0 - 1) * (h0 - 1) := by
  dsimp
  simp only [sig]
  field_simp [hm]
  ring

/-- Exact lower-ear residual identity, the reflection of the preceding
upper identity. -/
lemma sig_threeThree_broad_lower_earResidual_identity
    (P Q U1 L0 L1 L2 : ℝ × ℝ) {m : ℝ} (hm : m ≠ 0) :
    let x := (-sig P U1 L1) / m - 1
    let y := sig Q U1 L1 / m - 1
    let L := sig Q L1 L2 / m
    let ell := sig P L0 L1 / m
    let B := sig P Q U1 / m - 1
    let E := (-sig P Q L1) / m - 1
    let TL := sig L0 L1 L2 / m
    let P0 := sig P L1 L2 / m
    let Q0 := sig Q L0 L1 / m
    let x0 := (-sig P U1 L0) / m
    let z0 := sig Q U1 L2 / m
    (E + 1) * (x * y) - (x + 1) * (y + 1) +
          (E - x) * x * L + (E - y) * y * ell - (B + 1) * L * ell =
      (x + 1) * (y + 1) * (TL - 1) +
        (y + 1) * P0 * (x0 - 1) +
        (x + 1) * Q0 * (z0 - 1) +
        (E + 1) * (z0 - 1) * (x0 - 1) := by
  dsimp
  simp only [sig]
  field_simp [hm]
  ring

end Heilbronn8
