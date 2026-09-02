import Heilbronn8.Ident
import Heilbronn8.Compose

namespace Heilbronn8.TriHull

/-- Strict barycentric membership in a triangle. -/
def InTriStrict (p a b c : ℝ × ℝ) : Prop :=
  ∃ x y z : ℝ,
    0 < x ∧ 0 < y ∧ 0 < z ∧
    x + y + z = 1 ∧
    p = x • a + y • b + z • c

lemma inTriStrict_inTri {p a b c : ℝ × ℝ}
    (hp : InTriStrict p a b c) : InTri p a b c := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, rfl⟩ := hp
  exact ⟨x, y, z, hx.le, hy.le, hz.le, hsum, rfl⟩

/-- The three signed fan cells sum to the signed containing triangle. -/
lemma fan_sum (p a b c : ℝ × ℝ) :
    sig p b c + sig p c a + sig p a b = sig a b c := by
  simp only [sig]
  ring

/-- Splitting the fan cell `pbc` at `q`. -/
lemma fan_cell_sum (p b c q : ℝ × ℝ) :
    sig p b q + sig p q c + sig q b c = sig p b c := by
  simp only [sig]
  ring

/-- A strict interior point has three positive fan cells in a CCW triangle. -/
lemma inTriStrict_fan_pos {p a b c : ℝ × ℝ}
    (habc : 0 < sig a b c) (hp : InTriStrict p a b c) :
    0 < sig p b c ∧ 0 < sig p c a ∧ 0 < sig p a b := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, rfl⟩ := hp
  have hpbc : sig (x • a + y • b + z • c) b c = x * sig a b c := by
    rw [sig_affine_fst a b c b c x y z hsum]
    simp only [sig_eq12, sig_eq13, mul_zero, add_zero]
  have hpca : sig (x • a + y • b + z • c) c a = y * sig a b c := by
    rw [sig_affine_fst a b c c a x y z hsum]
    have hrot : sig b c a = sig a b c := (sig_rotate a b c).symm
    rw [sig_eq13, sig_eq12, hrot]
    ring
  have hpab : sig (x • a + y • b + z • c) a b = z * sig a b c := by
    rw [sig_affine_fst a b c a b x y z hsum]
    have hrot₁ : sig b a b = 0 := sig_eq13 b a
    have hrot₂ : sig c a b = sig a b c := sig_rotate c a b
    rw [sig_eq12, hrot₁, hrot₂]
    ring
  constructor
  · rw [hpbc]
    exact mul_pos hx habc
  constructor
  · rw [hpca]
    exact mul_pos hy habc
  · rw [hpab]
    exact mul_pos hz habc

/-- Orientation-fixed two-point identity from QuadHull8 (4). -/
lemma two_point_product_identity (x y z p q : ℝ × ℝ) :
    sig p y z * sig x p q =
      sig p y q * sig p z x - sig p q z * sig p x y := by
  simp only [sig]
  ring

/-- Orientation-fixed adjacent-fan identity from QuadHull8 (5). -/
lemma adjacent_fan_product_identity (x y z p q r : ℝ × ℝ) :
    sig p y z * sig p z x * sig p q r =
      sig p y q * sig p z r * sig p z x +
      sig p q z * sig p r x * sig p y z -
      sig p q z * sig p z r * sig p x y := by
  simp only [sig]
  ring

lemma sqrt_three_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

lemma sqrt_three_nonneg : (0 : ℝ) ≤ Real.sqrt 3 :=
  Real.sqrt_nonneg 3

/-- The rational approximation used in QuadHull8, equation (22). -/
lemma sixty_nine_fortieths_lt_sqrt_three :
    (69 : ℝ) / 40 < Real.sqrt 3 := by
  by_contra h
  have hle : Real.sqrt 3 ≤ (69 : ℝ) / 40 := le_of_not_gt h
  have hprod : 0 ≤ ((69 : ℝ) / 40 - Real.sqrt 3) *
      ((69 : ℝ) / 40 + Real.sqrt 3) :=
    mul_nonneg (by nlinarith [sqrt_three_nonneg])
      (by nlinarith [sqrt_three_nonneg])
  nlinarith [sqrt_three_mul_self]

/-- Division-free AM-GM estimate in the exact scale used below. -/
lemma four_sqrt_three_le_add {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : 12 ≤ x * y) :
    4 * Real.sqrt 3 ≤ x + y := by
  have hsq : 48 ≤ (x + y) ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  by_contra h
  have hlt : x + y < 4 * Real.sqrt 3 := lt_of_not_ge h
  have hprod : 0 <
      (4 * Real.sqrt 3 - (x + y)) * (4 * Real.sqrt 3 + (x + y)) :=
    mul_pos (by linarith)
      (by nlinarith [sqrt_three_mul_self, sqrt_three_nonneg])
  nlinarith [sqrt_three_mul_self]

/--
All ten triangles on the labelled points `A B C P Q` have ordinary area
at least one. Since `sig` is doubled signed area, the lower bounds are two.
-/
def FivePointMinAreaOne (A B C P Q : ℝ × ℝ) : Prop :=
  2 ≤ |sig A B C| ∧
  2 ≤ |sig P B C| ∧
  2 ≤ |sig P C A| ∧
  2 ≤ |sig P A B| ∧
  2 ≤ |sig Q B C| ∧
  2 ≤ |sig Q C A| ∧
  2 ≤ |sig Q A B| ∧
  2 ≤ |sig A P Q| ∧
  2 ≤ |sig B P Q| ∧
  2 ≤ |sig C P Q|

/--
TH8 Lemma 1, in the paper normalization: every selected triangle has
ordinary area at least one. The conclusion divides `sig A B C` by two
because `sig` is doubled area.
-/
theorem th8_lemma1 {A B C P Q : ℝ × ℝ}
    (hABC : 0 < sig A B C)
    (hP : InTriStrict P A B C)
    (hQ : InTriStrict Q P B C)
    (hmin : FivePointMinAreaOne A B C P Q) :
    4 + 2 * Real.sqrt 3 ≤ sig A B C / 2 := by
  rcases hmin with
    ⟨_hABCmin, hPBCmin, hPCAmin, hPABmin, hQBCmin,
      _hQCAmin, _hQABmin, hAPQmin, hBPQmin, hCPQmin⟩
  obtain ⟨hPBCpos, hPCApos, hPABpos⟩ :=
    inTriStrict_fan_pos hABC hP
  obtain ⟨hQBCpos, hQCPpos, hQPBpos⟩ :=
    inTriStrict_fan_pos hPBCpos hQ

  let α : ℝ := sig P B C
  let β : ℝ := sig P C A
  let γ : ℝ := sig P A B
  let a : ℝ := sig P B Q
  let b : ℝ := sig P Q C
  let c : ℝ := sig Q B C

  have hα : 0 < α := by simpa [α] using hPBCpos
  have hβpos : 0 < β := by simpa [β] using hPCApos
  have hγpos : 0 < γ := by simpa [γ] using hPABpos
  have hapos : 0 < a := by
    have : 0 < sig P B Q := by
      rwa [sig_rotate Q P B] at hQPBpos
    simpa [a] using this
  have hbpos : 0 < b := by
    have hrot : sig Q C P = sig P Q C := by
      calc
        sig Q C P = sig C P Q := sig_rotate Q C P
        _ = sig P Q C := sig_rotate C P Q
    have : 0 < sig P Q C := by rwa [hrot] at hQCPpos
    simpa [b] using this
  have hcpos : 0 < c := by simpa [c] using hQBCpos

  have hβ : 2 ≤ β := by
    rw [abs_of_pos hPCApos] at hPCAmin
    simpa [β] using hPCAmin
  have hγ : 2 ≤ γ := by
    rw [abs_of_pos hPABpos] at hPABmin
    simpa [γ] using hPABmin
  have ha : 2 ≤ a := by
    have hperm : |sig B P Q| = |sig P B Q| := by
      have hs : sig B P Q = -sig P B Q := by
        simp only [sig]
        ring
      rw [hs, abs_neg]
    rw [hperm, abs_of_pos hapos] at hBPQmin
    simpa [a] using hBPQmin
  have hb : 2 ≤ b := by
    rw [sig_rotate C P Q, abs_of_pos hbpos] at hCPQmin
    simpa [b] using hCPQmin
  have hc : 2 ≤ c := by
    rw [abs_of_pos hQBCpos] at hQBCmin
    simpa [c] using hQBCmin

  have hfanP : α + β + γ = sig A B C := by
    simpa [α, β, γ] using fan_sum P A B C
  have hfanQ : a + b + c = α := by
    simpa [a, b, c, α] using fan_cell_sum P B C Q
  have hid : α * sig A P Q = a * β - b * γ := by
    simpa [α, a, b, β, γ] using
      two_point_product_identity A B C P Q

  by_cases hs : 0 ≤ sig A P Q
  · have hsmin : 2 ≤ sig A P Q := by
      rwa [abs_of_nonneg hs] at hAPQmin
    have hmul : 0 ≤ α * (sig A P Q - 2) :=
      mul_nonneg hα.le (by linarith)
    have hcase : 2 * α ≤ a * β - b * γ := by
      nlinarith [hid]
    have hbg : 0 ≤ (b - 2) * (γ - 2) :=
      mul_nonneg (by linarith) (by linarith)
    have hprod : 12 ≤ a * (β - 2) := by
      nlinarith [hfanQ]
    have hamgm : 4 * Real.sqrt 3 ≤ a + (β - 2) :=
      four_sqrt_three_le_add (by linarith) (by linarith) hprod
    nlinarith [hfanP, hfanQ]
  · have hsneg : sig A P Q < 0 := lt_of_not_ge hs
    have hsmin : 2 ≤ -sig A P Q := by
      rwa [abs_of_neg hsneg] at hAPQmin
    have hmul : 0 ≤ α * (-sig A P Q - 2) :=
      mul_nonneg hα.le (by linarith)
    have hcase : 2 * α ≤ b * γ - a * β := by
      nlinarith [hid]
    have hab : 0 ≤ (a - 2) * (β - 2) :=
      mul_nonneg (by linarith) (by linarith)
    have hprod : 12 ≤ b * (γ - 2) := by
      nlinarith [hfanQ]
    have hamgm : 4 * Real.sqrt 3 ≤ b + (γ - 2) :=
      four_sqrt_three_le_add (by linarith) (by linarith) hprod
    nlinarith [hfanP, hfanQ]

/-- Rational form used by later occupancy estimates (QuadHull8 (22)). -/
lemma th8_lemma1_gt_149_over_20 {A B C P Q : ℝ × ℝ}
    (hABC : 0 < sig A B C)
    (hP : InTriStrict P A B C)
    (hQ : InTriStrict Q P B C)
    (hmin : FivePointMinAreaOne A B C P Q) :
    (149 : ℝ) / 20 < sig A B C / 2 := by
  have hmain := th8_lemma1 hABC hP hQ hmin
  nlinarith [sixty_nine_fortieths_lt_sqrt_three]

end Heilbronn8.TriHull
