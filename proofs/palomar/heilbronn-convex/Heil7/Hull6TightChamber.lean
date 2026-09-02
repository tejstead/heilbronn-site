import Heil7.Hull6BracketRoute

/-!
# The tight hull-six radial chamber

This file closes the chamber containing the sharp `D₃` configuration.  Write

* `a i = b i (i+1)` for the six boundary sectors,
* `d i = b i (i+2)` for the six two-step brackets, and
* `c i = b i (i+3)` for the three pairs of opposite rays (with both
  orientations retained cyclically).

In the tight chamber all `d i` are positive and the signs of the `c i`
alternate.  The six consecutive Pluecker relations then compare the same
product `d 0 * ... * d 5` from below and above.  A three-variable polynomial
AM--GM argument forces the excess in the three large alternating sectors to
be at least `3m`, which is exactly the missing amount.

The proof is homogeneous and uses no square roots and no outer-triangle
floor.  Thus it is a strictly local consequence of the radial floors and the
rank-two identities.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- The canonical tight chamber.  The opposite alternating chamber is its
one-step cyclic rotation. -/
def H6TightChamber (b : Fin 6 → Fin 6 → ℝ) : Prop :=
  0 < b 0 2 ∧ 0 < b 1 3 ∧ 0 < b 2 4 ∧
  0 < b 3 5 ∧ 0 < b 4 0 ∧ 0 < b 5 1 ∧
  0 < b 0 3 ∧ b 1 4 < 0 ∧ 0 < b 2 5

private def pairR (m x y : ℝ) : ℝ := m * (x + y) + x * y

/-- The polynomial form of the two-variable estimate used in the cyclic
product argument. -/
private lemma four_pairR_sq_le
    {m x y : ℝ} (hm : 0 ≤ m) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    4 * pairR m x y ^ 2 ≤
      (x + y) ^ 2 * (2 * m + x) * (2 * m + y) := by
  have hfactor :
      0 ≤ (x - y) ^ 2 * (2 * m * (x + y) + x * y) := by
    apply mul_nonneg (sq_nonneg _)
    exact add_nonneg (mul_nonneg (mul_nonneg (by positivity) hm)
      (add_nonneg hx hy)) (mul_nonneg hx hy)
  calc
    4 * pairR m x y ^ 2 ≤
        4 * pairR m x y ^ 2 +
          (x - y) ^ 2 * (2 * m * (x + y) + x * y) :=
      le_add_of_nonneg_right hfactor
    _ = (x + y) ^ 2 * (2 * m + x) * (2 * m + y) := by
      simp only [pairR]
      ring

/-- Three-variable AM--GM in a form whose proof is purely polynomial. -/
private lemma twenty_seven_mul_le_sum_cube
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    27 * x * y * z ≤ (x + y + z) ^ 3 := by
  have hxy : 4 * x * y ≤ (x + y) ^ 2 := by
    nlinarith only [sq_nonneg (x - y)]
  have hscaled := mul_le_mul_of_nonneg_right hxy
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 27) hz)
  have hfactor :
      0 ≤ ((x + y) - 2 * z) ^ 2 * (4 * (x + y) + z) := by
    apply mul_nonneg (sq_nonneg _)
    positivity
  have hqz :
      27 * (x + y) ^ 2 * z ≤ 4 * ((x + y) + z) ^ 3 := by
    calc
      27 * (x + y) ^ 2 * z ≤
          27 * (x + y) ^ 2 * z +
            ((x + y) - 2 * z) ^ 2 * (4 * (x + y) + z) :=
        le_add_of_nonneg_right hfactor
      _ = 4 * ((x + y) + z) ^ 3 := by ring
  nlinarith only [hscaled, hqz]

set_option maxHeartbeats 1000000 in
/-- The analytic endpoint of the tight-chamber argument. -/
private lemma cyclic_product_forces_three
    {m u v w : ℝ} (hm : 0 < m)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hprod :
      m ^ 3 * ((2 * m + u) * (2 * m + v) * (2 * m + w)) ≤
        pairR m u v * pairR m v w * pairR m w u) :
    3 * m ≤ u + v + w := by
  have hsq_uv := four_pairR_sq_le hm.le hu hv
  have hsq_vw := four_pairR_sq_le hm.le hv hw
  have hsq_wu := four_pairR_sq_le hm.le hw hu
  have hmul_uv_vw :
      (4 * pairR m u v ^ 2) * (4 * pairR m v w ^ 2) ≤
        ((u + v) ^ 2 * (2 * m + u) * (2 * m + v)) *
          ((v + w) ^ 2 * (2 * m + v) * (2 * m + w)) := by
    exact mul_le_mul hsq_uv hsq_vw (by positivity) (by positivity)
  have hmul :
      (4 * pairR m u v ^ 2) * (4 * pairR m v w ^ 2) *
          (4 * pairR m w u ^ 2) ≤
        ((u + v) ^ 2 * (2 * m + u) * (2 * m + v)) *
          ((v + w) ^ 2 * (2 * m + v) * (2 * m + w)) *
            ((w + u) ^ 2 * (2 * m + w) * (2 * m + u)) := by
    exact mul_le_mul hmul_uv_vw hsq_wu (by positivity) (by positivity)
  let Q := pairR m u v * pairR m v w * pairR m w u
  let C := (u + v) * (v + w) * (w + u)
  let P := (2 * m + u) * (2 * m + v) * (2 * m + w)
  have hsquare : (8 * Q) ^ 2 ≤ (C * P) ^ 2 := by
    calc
      (8 * Q) ^ 2 =
          (4 * pairR m u v ^ 2) * (4 * pairR m v w ^ 2) *
            (4 * pairR m w u ^ 2) := by
        simp only [Q]
        ring
      _ ≤ ((u + v) ^ 2 * (2 * m + u) * (2 * m + v)) *
          ((v + w) ^ 2 * (2 * m + v) * (2 * m + w)) *
            ((w + u) ^ 2 * (2 * m + w) * (2 * m + u)) := hmul
      _ = (C * P) ^ 2 := by
        simp only [C, P]
        ring
  have hQ : 0 ≤ Q := by
    simp only [Q, pairR]
    positivity
  have hC : 0 ≤ C := by
    simp only [C]
    positivity
  have hP : 0 < P := by
    simp only [P]
    positivity
  have hroot : 8 * Q ≤ C * P := by
    exact (sq_le_sq₀ (mul_nonneg (by norm_num) hQ)
      (mul_nonneg hC hP.le)).mp hsquare
  have hscaled := mul_le_mul_of_nonneg_left hprod
    (by positivity : (0 : ℝ) ≤ 8)
  have hcancel_pre : (8 * m ^ 3) * P ≤ C * P := by
    calc
      (8 * m ^ 3) * P = 8 * (m ^ 3 * P) := by ring
      _ ≤ 8 * Q := by
        simpa only [P, Q] using hscaled
      _ ≤ C * P := hroot
  have hC_lower : 8 * m ^ 3 ≤ C :=
    le_of_mul_le_mul_right hcancel_pre hP
  have hamgm0 := twenty_seven_mul_le_sum_cube
    (add_nonneg hu hv) (add_nonneg hv hw) (add_nonneg hw hu)
  have hamgm : 27 * C ≤ 8 * (u + v + w) ^ 3 := by
    calc
      27 * C = 27 * (u + v) * (v + w) * (w + u) := by
        simp only [C]
        ring
      _ ≤ ((u + v) + (v + w) + (w + u)) ^ 3 := hamgm0
      _ = 8 * (u + v + w) ^ 3 := by ring
  have hcube : (3 * m) ^ 3 ≤ (u + v + w) ^ 3 := by
    calc
      (3 * m) ^ 3 = ((27 : ℝ) / 8) * (8 * m ^ 3) := by ring
      _ ≤ ((27 : ℝ) / 8) * C :=
        mul_le_mul_of_nonneg_left hC_lower (by norm_num)
      _ = (27 * C) / 8 := by ring
      _ ≤ (u + v + w) ^ 3 := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).2
        simpa only [mul_comm] using hamgm
  exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0)
    (by positivity : 0 ≤ u + v + w) hcube

/-- Six explicit consecutive GP relations in the tight sign chamber force the
sharp bound.  Keeping this scalar lemma separate makes the point/bracket
wrapper below routine. -/
private theorem tight_scalar
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd : ∀ i, m ≤ d i)
    (hc0 : m ≤ c 0) (hc1 : c 1 ≤ -m) (hc2 : m ≤ c 2)
    (hc3 : c 3 ≤ -m) (hc4 : m ≤ c 4) (hc5 : c 5 ≤ -m)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  have hanonneg : ∀ i, 0 ≤ a i := fun i => le_trans hm.le (ha i)
  have hdnonneg : ∀ i, 0 ≤ d i := fun i => le_trans hm.le (hd i)
  have haa (i j : Fin 6) : m * m ≤ a i * a j := by
    calc
      m * m ≤ m * a j := mul_le_mul_of_nonneg_left (ha j) hm.le
      _ ≤ a i * a j := mul_le_mul_of_nonneg_right (ha i) (hanonneg j)
  have lower_of_pos (i j k : Fin 6) (hc : m ≤ c i)
      (hr : d i * d (i + 1) = a i * a j + c i * a k) :
      m * (m + a k) ≤ d i * d (i + 1) := by
    have hca : m * a k ≤ c i * a k :=
      mul_le_mul_of_nonneg_right hc (hanonneg k)
    calc
      m * (m + a k) = m * m + m * a k := by ring
      _ ≤ a i * a j + c i * a k := add_le_add (haa i j) hca
      _ = d i * d (i + 1) := hr.symm
  have upper_of_neg (i j k : Fin 6) (hc : c i ≤ -m)
      (hr : d i * d (i + 1) = a i * a j + c i * a k) :
      d i * d (i + 1) ≤ a i * a j - m * m := by
    have hca0 : c i * a k ≤ (-m) * a k :=
      mul_le_mul_of_nonneg_right hc (hanonneg k)
    have hca1 : (-m) * a k ≤ (-m) * m :=
      mul_le_mul_of_nonpos_left (ha k) (by linarith)
    calc
      d i * d (i + 1) = a i * a j + c i * a k := hr
      _ ≤ a i * a j + (-m) * m := add_le_add_right (hca0.trans hca1) _
      _ = a i * a j - m * m := by ring
  have hlo0 : m * (m + a 1) ≤ d 0 * d 1 := by
    simpa using lower_of_pos 0 2 1 hc0 (by simpa using hrel 0)
  have hlo2 : m * (m + a 3) ≤ d 2 * d 3 := by
    simpa using lower_of_pos 2 4 3 hc2 (by simpa using hrel 2)
  have hlo4 : m * (m + a 5) ≤ d 4 * d 5 := by
    simpa using lower_of_pos 4 0 5 hc4 (by simpa using hrel 4)
  have hup1 : d 1 * d 2 ≤ a 1 * a 3 - m * m := by
    simpa using upper_of_neg 1 3 2 hc1 (by simpa using hrel 1)
  have hup3 : d 3 * d 4 ≤ a 3 * a 5 - m * m := by
    simpa using upper_of_neg 3 5 4 hc3 (by simpa using hrel 3)
  have hup5 : d 5 * d 0 ≤ a 5 * a 1 - m * m := by
    simpa using upper_of_neg 5 1 0 hc5 (by simpa using hrel 5)
  have hlo02 :
      (m * (m + a 1)) * (m * (m + a 3)) ≤
        (d 0 * d 1) * (d 2 * d 3) := by
    exact mul_le_mul hlo0 hlo2
      (mul_nonneg hm.le (add_nonneg hm.le (hanonneg 3)))
      (mul_nonneg (hdnonneg 0) (hdnonneg 1))
  have hlo :
      (m * (m + a 1)) * (m * (m + a 3)) * (m * (m + a 5)) ≤
        (d 0 * d 1) * (d 2 * d 3) * (d 4 * d 5) := by
    exact mul_le_mul hlo02 hlo4
      (mul_nonneg hm.le (add_nonneg hm.le (hanonneg 5)))
      (mul_nonneg (mul_nonneg (hdnonneg 0) (hdnonneg 1))
        (mul_nonneg (hdnonneg 2) (hdnonneg 3)))
  have hup12 :
      (d 1 * d 2) * (d 3 * d 4) ≤
        (a 1 * a 3 - m * m) * (a 3 * a 5 - m * m) := by
    exact mul_le_mul hup1 hup3 (mul_nonneg (hdnonneg 3) (hdnonneg 4))
      (le_trans (mul_nonneg (hdnonneg 1) (hdnonneg 2)) hup1)
  have hup :
      (d 1 * d 2) * (d 3 * d 4) * (d 5 * d 0) ≤
        (a 1 * a 3 - m * m) * (a 3 * a 5 - m * m) *
          (a 5 * a 1 - m * m) := by
    exact mul_le_mul hup12 hup5 (mul_nonneg (hdnonneg 5) (hdnonneg 0))
      (mul_nonneg
        (le_trans (mul_nonneg (hdnonneg 1) (hdnonneg 2)) hup1)
        (le_trans (mul_nonneg (hdnonneg 3) (hdnonneg 4)) hup3))
  have hparity :
      (d 0 * d 1) * (d 2 * d 3) * (d 4 * d 5) =
        (d 1 * d 2) * (d 3 * d 4) * (d 5 * d 0) := by ring
  have hraw :
      m ^ 3 * ((m + a 1) * (m + a 3) * (m + a 5)) ≤
        (a 1 * a 3 - m * m) * (a 3 * a 5 - m * m) *
          (a 5 * a 1 - m * m) := by
    calc
      m ^ 3 * ((m + a 1) * (m + a 3) * (m + a 5)) =
          (m * (m + a 1)) * (m * (m + a 3)) * (m * (m + a 5)) := by ring
      _ ≤ (d 0 * d 1) * (d 2 * d 3) * (d 4 * d 5) := hlo
      _ = (d 1 * d 2) * (d 3 * d 4) * (d 5 * d 0) := hparity
      _ ≤ (a 1 * a 3 - m * m) * (a 3 * a 5 - m * m) *
          (a 5 * a 1 - m * m) := hup
  have hu : 0 ≤ a 1 - m := sub_nonneg.mpr (ha 1)
  have hv : 0 ≤ a 3 - m := sub_nonneg.mpr (ha 3)
  have hw : 0 ≤ a 5 - m := sub_nonneg.mpr (ha 5)
  have hprod :
      m ^ 3 *
          ((2 * m + (a 1 - m)) * (2 * m + (a 3 - m)) *
            (2 * m + (a 5 - m))) ≤
        pairR m (a 1 - m) (a 3 - m) *
          pairR m (a 3 - m) (a 5 - m) *
            pairR m (a 5 - m) (a 1 - m) := by
    calc
      m ^ 3 *
          ((2 * m + (a 1 - m)) * (2 * m + (a 3 - m)) *
            (2 * m + (a 5 - m))) =
          m ^ 3 * ((m + a 1) * (m + a 3) * (m + a 5)) := by ring
      _ ≤ (a 1 * a 3 - m * m) * (a 3 * a 5 - m * m) *
          (a 5 * a 1 - m * m) := hraw
      _ = pairR m (a 1 - m) (a 3 - m) *
          pairR m (a 3 - m) (a 5 - m) *
            pairR m (a 5 - m) (a 1 - m) := by
        simp only [pairR]
        ring
  have hodd := cyclic_product_forces_three hm hu hv hw hprod
  linarith only [ha 0, ha 2, ha 4, hodd]

/-- Array-level form of the tight-chamber bound.  This is the relabeling seam
used by the final finite dispatcher; unlike the bracket wrapper below, it does
not tie the chamber to the literal indices `0,...,5`. -/
theorem h6_tight_array_bound
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd : ∀ i, m ≤ d i)
    (hc0 : m ≤ c 0) (hc1 : c 1 ≤ -m) (hc2 : m ≤ c 2)
    (hc3 : c 3 ≤ -m) (hc4 : m ≤ c 4) (hc5 : c 5 ≤ -m)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 :=
  tight_scalar m a d c hm ha hd hc0 hc1 hc2 hc3 hc4 hc5 hrel

/-- Sharp `9m` bound in the canonical all-two-step-positive,
opposite-alternating chamber. -/
theorem h6_tight_chamber_bound
    (m : ℝ) (b : Fin 6 → Fin 6 → ℝ)
    (hm : 0 < m)
    (hskew : ∀ i j, b i j = -b j i)
    (hgp : ∀ i j k l,
      b i j * b k l - b i k * b j l + b i l * b j k = 0)
    (hradial : ∀ i j, i ≠ j → m ≤ |b i j|)
    (hedge : ∀ i : Fin 6, 0 < b i (i + 1))
    (hchamber : H6TightChamber b) :
    9 * m ≤
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 := by
  rcases hchamber with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hc0pos, hc1neg, hc2pos⟩
  let a : Fin 6 → ℝ := fun i => b i (i + 1)
  let d : Fin 6 → ℝ := fun i => b i (i + 2)
  let c : Fin 6 → ℝ := fun i => b i (i + 3)
  have ha : ∀ i, m ≤ a i := by
    intro i
    have hp := hedge i
    have hn : i ≠ i + 1 := by fin_cases i <;> decide
    have hf := hradial i (i + 1) hn
    rw [abs_of_pos hp] at hf
    exact hf
  have hdpos : ∀ i, 0 < d i := by
    intro i
    fin_cases i
    · simpa [d] using hd0
    · simpa [d] using hd1
    · simpa [d] using hd2
    · simpa [d] using hd3
    · simpa [d] using hd4
    · simpa [d] using hd5
  have hd : ∀ i, m ≤ d i := by
    intro i
    have hn : i ≠ i + 2 := by fin_cases i <;> decide
    have hf := hradial i (i + 2) hn
    rw [abs_of_pos (hdpos i)] at hf
    exact hf
  have hc0 : m ≤ c 0 := by
    have hf := hradial 0 3 (by decide)
    simpa [c, abs_of_pos hc0pos] using hf
  have hc1 : c 1 ≤ -m := by
    have hf := hradial 1 4 (by decide)
    have habs : |b 1 4| = -b 1 4 := abs_of_neg hc1neg
    rw [habs] at hf
    change b 1 4 ≤ -m
    linarith
  have hc2 : m ≤ c 2 := by
    have hf := hradial 2 5 (by decide)
    simpa [c, abs_of_pos hc2pos] using hf
  have hc3 : c 3 ≤ -m := by
    have hsym := hskew 3 0
    have hf := hradial 0 3 (by decide)
    rw [abs_of_pos hc0pos] at hf
    change b 3 0 ≤ -m
    linarith
  have hc4 : m ≤ c 4 := by
    have hsym := hskew 4 1
    have hf := hradial 1 4 (by decide)
    rw [abs_of_neg hc1neg] at hf
    change m ≤ b 4 1
    linarith
  have hc5 : c 5 ≤ -m := by
    have hsym := hskew 5 2
    have hf := hradial 2 5 (by decide)
    rw [abs_of_pos hc2pos] at hf
    change b 5 2 ≤ -m
    linarith
  have hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1) := by
    intro i
    fin_cases i
    · have hp := hgp 0 1 2 3
      change b 0 2 * b 1 3 = b 0 1 * b 2 3 + b 0 3 * b 1 2
      linarith
    · have hp := hgp 1 2 3 4
      change b 1 3 * b 2 4 = b 1 2 * b 3 4 + b 1 4 * b 2 3
      linarith
    · have hp := hgp 2 3 4 5
      change b 2 4 * b 3 5 = b 2 3 * b 4 5 + b 2 5 * b 3 4
      linarith
    · have hp := hgp 3 4 5 0
      change b 3 5 * b 4 0 = b 3 4 * b 5 0 + b 3 0 * b 4 5
      linarith
    · have hp := hgp 4 5 0 1
      change b 4 0 * b 5 1 = b 4 5 * b 0 1 + b 4 1 * b 5 0
      linarith
    · have hp := hgp 5 0 1 2
      change b 5 1 * b 0 2 = b 5 0 * b 1 2 + b 5 2 * b 0 1
      linarith
  have hbound := tight_scalar m a d c hm ha hd
    hc0 hc1 hc2 hc3 hc4 hc5 hrel
  simpa [a] using hbound

end HeilbronnChallenge.N7Upper
