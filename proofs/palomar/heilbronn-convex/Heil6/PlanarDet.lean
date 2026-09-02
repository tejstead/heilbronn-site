import Mathlib

set_option linter.style.header false

/-!
# Small determinant library for the source-only n=6 scratch proof

The active Palomar package calls this bracket `HullBridge.sig`.  The scratch
tree deliberately has no dependency on that package, so we keep the same
polynomial under a local name.  The eventual bridge is definitional (`rfl`).

Only the four identities used by the pentagon and hexagon adapters are kept
here.  They are coordinate-ring identities, not generated certificates.
-/

namespace N6Scratch
namespace PlanarDet

/-- Twice the oriented area of the triangle `p q r`. -/
def sig (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

theorem sig_rotate (p q r : ℝ × ℝ) :
    sig p q r = sig q r p := by
  simp only [sig]
  ring

theorem sig_swap (p q r : ℝ × ℝ) :
    sig p q r = -sig p r q := by
  simp only [sig]
  ring

/-- Four-point cocycle, in the form used to split polygonal areas. -/
theorem cocycle (p q r s : ℝ × ℝ) :
    sig p q s + sig q r s = sig p q r + sig p r s := by
  simp only [sig]
  ring

/-- The rank-two Grassmann--Pluecker relation for five planar points. -/
theorem plucker (p q r s t : ℝ × ℝ) :
    sig p q r * sig p s t - sig p q s * sig p r t
      + sig p q t * sig p r s = 0 := by
  simp only [sig]
  ring

/-- The coordinate in the direction of the linear functional `(a,b)`, based
at `A`. -/
def longitudinal (a b : ℝ) (A B : ℝ × ℝ) : ℝ :=
  a * (B.1 - A.1) + b * (B.2 - A.2)

/-- The positively oriented complementary coordinate to `longitudinal`. -/
def transverse (a b : ℝ) (A B : ℝ × ℝ) : ℝ :=
  -b * (B.1 - A.1) + a * (B.2 - A.2)

/-- A linear functional on the plane is its two coordinate coefficients.
This is the adapter from the Hahn--Banach separator to `longitudinal`. -/
theorem longitudinal_eq_linearMap_sub
    (f : (ℝ × ℝ) →ₗ[ℝ] ℝ) (A B : ℝ × ℝ) :
    longitudinal (f (1, 0)) (f (0, 1)) A B = f B - f A := by
  have hdecomp :
      B - A = (B.1 - A.1) • (1, 0) + (B.2 - A.2) • (0, 1) := by
    ext <;> simp
  calc
    longitudinal (f (1, 0)) (f (0, 1)) A B =
        (B.1 - A.1) * f (1, 0) + (B.2 - A.2) * f (0, 1) := by
      simp only [longitudinal]
      ring
    _ = f ((B.1 - A.1) • (1, 0) + (B.2 - A.2) • (0, 1)) := by
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul]
    _ = f (B - A) := by rw [hdecomp]
    _ = f B - f A := map_sub f B A

theorem sum_sq_pos_of_longitudinal_pos
    (a b : ℝ) (A B : ℝ × ℝ)
    (h : 0 < longitudinal a b A B) : 0 < a ^ 2 + b ^ 2 := by
  by_contra hn
  have hsum : a ^ 2 + b ^ 2 ≤ 0 := le_of_not_gt hn
  have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  simp [longitudinal, ha, hb] at h

/-- Sorting points in the open half-plane `longitudinal > 0` by transverse
slope gives positive orientation with the anchor. -/
theorem sig_pos_of_slope_lt
    (a b : ℝ) (A B C : ℝ × ℝ)
    (hdet : 0 < a ^ 2 + b ^ 2)
    (hB : 0 < longitudinal a b A B)
    (hC : 0 < longitudinal a b A C)
    (hslope : transverse a b A B / longitudinal a b A B <
      transverse a b A C / longitudinal a b A C) :
    0 < sig A B C := by
  have hcross :
      transverse a b A B * longitudinal a b A C <
        transverse a b A C * longitudinal a b A B :=
    (div_lt_div_iff₀ hB hC).mp hslope
  have hid :
      transverse a b A C * longitudinal a b A B -
          transverse a b A B * longitudinal a b A C =
        (a ^ 2 + b ^ 2) * sig A B C := by
    simp only [longitudinal, transverse, sig]
    ring
  have hmul : 0 < (a ^ 2 + b ^ 2) * sig A B C := by
    rw [← hid]
    linarith
  rcases (mul_pos_iff.mp hmul) with h | h
  · exact h.2
  · linarith

/-- General position makes the transverse slopes from the separated anchor
pairwise distinct. -/
theorem slope_ne_of_sig_ne
    (a b : ℝ) (A B C : ℝ × ℝ)
    (hdet : 0 < a ^ 2 + b ^ 2)
    (hB : longitudinal a b A B ≠ 0)
    (hC : longitudinal a b A C ≠ 0)
    (hsig : sig A B C ≠ 0) :
    transverse a b A B / longitudinal a b A B ≠
      transverse a b A C / longitudinal a b A C := by
  intro hslope
  have hcross :
      transverse a b A B * longitudinal a b A C =
        transverse a b A C * longitudinal a b A B :=
    (div_eq_div_iff hB hC).mp hslope
  have hid :
      transverse a b A C * longitudinal a b A B -
          transverse a b A B * longitudinal a b A C =
        (a ^ 2 + b ^ 2) * sig A B C := by
    simp only [longitudinal, transverse, sig]
    ring
  have hzero : (a ^ 2 + b ^ 2) * sig A B C = 0 := by
    rw [← hid]
    linarith
  rcases mul_eq_zero.mp hzero with h | h
  · linarith
  · exact hsig h

/-- Strict orientation inequalities give explicit positive barycentric
coordinates.  This is the small geometric lemma used by the slope-sorting
proof of cyclic hull order. -/
theorem strict_barycentric_of_orientations
    (A B C D : ℝ × ℝ)
    (hABD : 0 < sig A B D)
    (hABC : 0 < sig A B C)
    (hACD : 0 < sig A C D)
    (hBDC : 0 < sig B D C) :
    ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = 1 ∧
      C = x • A + y • B + z • D := by
  let Δ := sig A B D
  refine ⟨sig B D C / Δ, sig A C D / Δ, sig A B C / Δ,
    div_pos hBDC hABD, div_pos hACD hABD, div_pos hABC hABD, ?_, ?_⟩
  · dsimp [Δ]
    field_simp [ne_of_gt hABD]
    simp only [sig]
    ring
  · apply Prod.ext
    · dsimp [Δ]
      field_simp [ne_of_gt hABD]
      simp only [sig]
      ring
    · dsimp [Δ]
      field_simp [ne_of_gt hABD]
      simp only [sig]
      ring

/-- In a slope order around an anchor `A`, a clockwise turn at the middle
point puts that middle point strictly inside the anchor triangle. -/
theorem middle_barycentric_of_wrong_turn
    (A B C D : ℝ × ℝ)
    (hABD : 0 < sig A B D)
    (hABC : 0 < sig A B C)
    (hACD : 0 < sig A C D)
    (hBCD : sig B C D < 0) :
    ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = 1 ∧
      C = x • A + y • B + z • D := by
  apply strict_barycentric_of_orientations A B C D hABD hABC hACD
  have hswap := sig_swap B C D
  linarith

/-- Once the points seen from an anchor are in increasing slope order, convex
independence rules out every clockwise turn.  This packages the only genuinely
geometric step in the slope-sort construction of a cyclic hull order.

The last hypothesis is deliberately stated as the exact positive-barycentric
configuration that `middle_barycentric_of_wrong_turn` would produce.  An
extreme-point argument discharges it immediately: the middle point would lie
in the convex hull of the anchor and the two outer points. -/
theorem all_triples_pos_of_anchor_order
    {n : ℕ} (A : ℝ × ℝ) (B : Fin n → ℝ × ℝ)
    (hanchor : ∀ i j, i < j → 0 < sig A (B i) (B j))
    (hnondegenerate : ∀ i j k, i < j → j < k →
      sig (B i) (B j) (B k) ≠ 0)
    (hconvexIndependent : ∀ i j k, i < j → j < k →
      ¬ ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = 1 ∧
        B j = x • A + y • B i + z • B k) :
    ∀ i j k, i < j → j < k → 0 < sig (B i) (B j) (B k) := by
  intro i j k hij hjk
  rcases lt_or_gt_of_ne (hnondegenerate i j k hij hjk) with hneg | hpos
  · exfalso
    apply hconvexIndependent i j k hij hjk
    exact middle_barycentric_of_wrong_turn A (B i) (B j) (B k)
      (hanchor i k (lt_trans hij hjk)) (hanchor i j hij)
      (hanchor j k hjk) hneg
  · exact hpos

end PlanarDet
end N6Scratch
