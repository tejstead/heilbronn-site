import Heil7.Hull6TightChamber
import Heil7.RationalOptimizerFamily

/-!
# Equality in the tight hull-six chamber

This module records the equality case of `h6_tight_array_bound`.  It is kept
separate from the bound itself because the upper-bound dispatcher only needs
the inequality, whereas the seven-point equality analysis needs the complete
rank-two packet.

At equality the six adjacent sectors are `m,2m,m,2m,m,2m`, the opposite
brackets are exactly `m,-m,m,-m,m,-m`, and the two-step brackets alternate
between `lambda*m` and `(3/lambda)*m`.  Radial floors alone give
`1 <= lambda <= 3`; the two outer-triangle floors `012` and `123` sharpen this
to the exact interval `3/2 <= lambda <= 2`.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

private def eqPairR (m x y : ℝ) : ℝ := m * (x + y) + x * y

private lemma four_eqPairR_sq_le
    {m x y : ℝ} (hm : 0 ≤ m) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    4 * eqPairR m x y ^ 2 ≤
      (x + y) ^ 2 * (2 * m + x) * (2 * m + y) := by
  have hfactor :
      0 ≤ (x - y) ^ 2 * (2 * m * (x + y) + x * y) := by
    apply mul_nonneg (sq_nonneg _)
    exact add_nonneg (mul_nonneg (mul_nonneg (by positivity) hm)
      (add_nonneg hx hy)) (mul_nonneg hx hy)
  calc
    4 * eqPairR m x y ^ 2 ≤
        4 * eqPairR m x y ^ 2 +
          (x - y) ^ 2 * (2 * m * (x + y) + x * y) :=
      le_add_of_nonneg_right hfactor
    _ = (x + y) ^ 2 * (2 * m + x) * (2 * m + y) := by
      simp only [eqPairR]
      ring

/-- Equality endpoint of the cyclic product argument.  The extra upper bound
on `u+v+w` is exactly what global equality supplies after the three other
adjacent sectors have been charged their radial floor. -/
private lemma cyclic_product_eq
    {m u v w : ℝ} (hm : 0 < m)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hsum : u + v + w ≤ 3 * m)
    (hprod :
      m ^ 3 * ((2 * m + u) * (2 * m + v) * (2 * m + w)) ≤
        eqPairR m u v * eqPairR m v w * eqPairR m w u) :
    u = m ∧ v = m ∧ w = m := by
  have hsq_uv := four_eqPairR_sq_le hm.le hu hv
  have hsq_vw := four_eqPairR_sq_le hm.le hv hw
  have hsq_wu := four_eqPairR_sq_le hm.le hw hu
  have hmul_uv_vw :
      (4 * eqPairR m u v ^ 2) * (4 * eqPairR m v w ^ 2) ≤
        ((u + v) ^ 2 * (2 * m + u) * (2 * m + v)) *
          ((v + w) ^ 2 * (2 * m + v) * (2 * m + w)) := by
    exact mul_le_mul hsq_uv hsq_vw (by positivity) (by positivity)
  have hmul :
      (4 * eqPairR m u v ^ 2) * (4 * eqPairR m v w ^ 2) *
          (4 * eqPairR m w u ^ 2) ≤
        ((u + v) ^ 2 * (2 * m + u) * (2 * m + v)) *
          ((v + w) ^ 2 * (2 * m + v) * (2 * m + w)) *
            ((w + u) ^ 2 * (2 * m + w) * (2 * m + u)) := by
    exact mul_le_mul hmul_uv_vw hsq_wu (by positivity) (by positivity)
  let Q := eqPairR m u v * eqPairR m v w * eqPairR m w u
  let C := (u + v) * (v + w) * (w + u)
  let P := (2 * m + u) * (2 * m + v) * (2 * m + w)
  let S := u + v + w
  have hsquare : (8 * Q) ^ 2 ≤ (C * P) ^ 2 := by
    calc
      (8 * Q) ^ 2 =
          (4 * eqPairR m u v ^ 2) * (4 * eqPairR m v w ^ 2) *
            (4 * eqPairR m w u ^ 2) := by
        simp only [Q]
        ring
      _ ≤ ((u + v) ^ 2 * (2 * m + u) * (2 * m + v)) *
          ((v + w) ^ 2 * (2 * m + v) * (2 * m + w)) *
            ((w + u) ^ 2 * (2 * m + w) * (2 * m + u)) := hmul
      _ = (C * P) ^ 2 := by
        simp only [C, P]
        ring
  have hQ : 0 ≤ Q := by
    simp only [Q, eqPairR]
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
  have hSnonneg : 0 ≤ S := by
    simp only [S]
    positivity
  have hcube_upper : S ^ 3 ≤ (3 * m) ^ 3 := by
    have hfac :
        0 ≤ (3 * m - S) * ((3 * m) ^ 2 + (3 * m) * S + S ^ 2) := by
      apply mul_nonneg (sub_nonneg.mpr (by simpa only [S] using hsum))
      positivity
    calc
      S ^ 3 ≤ S ^ 3 +
          (3 * m - S) * ((3 * m) ^ 2 + (3 * m) * S + S ^ 2) :=
        le_add_of_nonneg_right hfac
      _ = (3 * m) ^ 3 := by ring
  let x := u + v
  let y := v + w
  let z := w + u
  have hx : 0 ≤ x := by simp only [x]; positivity
  have hy : 0 ≤ y := by simp only [y]; positivity
  have hz : 0 ≤ z := by simp only [z]; positivity
  have hgap : 108 * x * y * z ≤ 4 * (x + y + z) ^ 3 := by
    have h1 :
        0 ≤ (x + y - 2 * z) ^ 2 * (4 * (x + y) + z) := by
      apply mul_nonneg (sq_nonneg _)
      positivity
    have h2 : 0 ≤ 27 * z * (x - y) ^ 2 := by positivity
    calc
      108 * x * y * z ≤
          108 * x * y * z +
            (x + y - 2 * z) ^ 2 * (4 * (x + y) + z) +
              27 * z * (x - y) ^ 2 := by linarith
      _ = 4 * (x + y + z) ^ 3 := by ring
  have hamgm : 27 * C ≤ 8 * S ^ 3 := by
    simp only [x, y, z, C, S] at hgap ⊢
    nlinarith only [hgap]
  have hC_upper : C ≤ 8 * m ^ 3 := by
    nlinarith only [hamgm, hcube_upper]
  have hCeq : C = 8 * m ^ 3 := le_antisymm hC_upper hC_lower
  have hcube_lower : (3 * m) ^ 3 ≤ S ^ 3 := by
    nlinarith only [hamgm, hCeq]
  have hS_lower : 3 * m ≤ S :=
    le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hSnonneg hcube_lower
  have hSeq : S = 3 * m :=
    le_antisymm (by simpa only [S] using hsum) hS_lower
  have hxyz : x * y * z = 8 * m ^ 3 := by
    simpa only [x, y, z, C] using hCeq
  have hxyzsum : x + y + z = 6 * m := by
    simp only [x, y, z, S] at hSeq ⊢
    linarith only [hSeq]
  have hleftzero : 4 * (x + y + z) ^ 3 - 108 * x * y * z = 0 := by
    rw [hxyzsum]
    nlinarith only [hxyz]
  have hgap_id :
      4 * (x + y + z) ^ 3 - 108 * x * y * z =
        (x + y - 2 * z) ^ 2 * (4 * (x + y) + z) +
          27 * z * (x - y) ^ 2 := by ring
  have hterms :
      (x + y - 2 * z) ^ 2 * (4 * (x + y) + z) +
          27 * z * (x - y) ^ 2 = 0 := by
    rw [← hgap_id, hleftzero]
  have hxyzpos : 0 < x * y * z := by rw [hxyz]; positivity
  have hzpos : 0 < z := by
    rcases eq_or_lt_of_le hz with hz0 | hzpos
    · rw [← hz0] at hxyzpos
      norm_num at hxyzpos
    · exact hzpos
  have hfacpos : 0 < 4 * (x + y) + z := by positivity
  have hterm1nonneg :
      0 ≤ (x + y - 2 * z) ^ 2 * (4 * (x + y) + z) := by positivity
  have hterm2nonneg : 0 ≤ 27 * z * (x - y) ^ 2 := by positivity
  have hterm1zero :
      (x + y - 2 * z) ^ 2 * (4 * (x + y) + z) = 0 := by
    nlinarith only [hterms, hterm1nonneg, hterm2nonneg]
  have hterm2zero : 27 * z * (x - y) ^ 2 = 0 := by
    nlinarith only [hterms, hterm1nonneg, hterm2nonneg]
  have hs1 : (x + y - 2 * z) ^ 2 = 0 :=
    (mul_eq_zero.mp hterm1zero).resolve_right (ne_of_gt hfacpos)
  have hs2 : (x - y) ^ 2 = 0 :=
    (mul_eq_zero.mp hterm2zero).resolve_left (by positivity)
  have hxy : x = y := by nlinarith only [hs2]
  have hxy2z : x + y = 2 * z := by nlinarith only [hs1]
  simp only [x, y, z, S] at hxy hxy2z hSeq
  constructor
  · nlinarith only [hxy, hxy2z, hSeq]
  constructor <;> nlinarith only [hxy, hxy2z, hSeq]

private lemma three_eq_of_lower_mul
    {L x y z : ℝ} (hL : 0 < L)
    (hx : L ≤ x) (hy : L ≤ y) (hz : L ≤ z)
    (hxyz : x * y * z = L ^ 3) :
    x = L ∧ y = L ∧ z = L := by
  have xpos : 0 < x := hL.trans_le hx
  have ypos : 0 < y := hL.trans_le hy
  have zpos : 0 < z := hL.trans_le hz
  have one (p q r : ℝ) (ppos : 0 < p) (qpos : 0 < q) (rpos : 0 < r)
      (ha : L ≤ p) (hb : L ≤ q) (hc : L ≤ r)
      (heq : p * q * r = L ^ 3) : p ≤ L := by
    by_contra hn
    have hlt : L < p := lt_of_not_ge hn
    have hqr : L * L ≤ q * r :=
      mul_le_mul hb hc hL.le qpos.le
    have hcontra : L ^ 3 < L ^ 3 := by
      calc
        L ^ 3 = L * (L * L) := by ring
        _ ≤ L * (q * r) := mul_le_mul_of_nonneg_left hqr hL.le
        _ < p * (q * r) := mul_lt_mul_of_pos_right hlt (mul_pos qpos rpos)
        _ = p * q * r := by ring
        _ = L ^ 3 := heq
    exact (lt_irrefl _ hcontra)
  have hxle := one x y z xpos ypos zpos hx hy hz hxyz
  have hyle : y ≤ L := by
    have heq : y * z * x = L ^ 3 := by rw [← hxyz]; ring
    exact one y z x ypos zpos xpos hy hz hx heq
  have hzle : z ≤ L := by
    have heq : z * x * y = L ^ 3 := by rw [← hxyz]; ring
    exact one z x y zpos xpos ypos hz hx hy heq
  exact ⟨le_antisymm hxle hx, le_antisymm hyle hy, le_antisymm hzle hz⟩

private lemma three_eq_of_upper_mul
    {L x y z : ℝ} (hL : 0 < L)
    (xpos : 0 < x) (ypos : 0 < y) (zpos : 0 < z)
    (hx : x ≤ L) (hy : y ≤ L) (hz : z ≤ L)
    (hxyz : x * y * z = L ^ 3) :
    x = L ∧ y = L ∧ z = L := by
  have one (p q r : ℝ) (ppos : 0 < p) (qpos : 0 < q) (rpos : 0 < r)
      (ha : p ≤ L) (hb : q ≤ L) (hc : r ≤ L)
      (heq : p * q * r = L ^ 3) : L ≤ p := by
    by_contra hn
    have hlt : p < L := lt_of_not_ge hn
    have hqr : q * r ≤ L * L :=
      mul_le_mul hb hc rpos.le hL.le
    have hcontra : L ^ 3 < L ^ 3 := by
      calc
        L ^ 3 = p * q * r := heq.symm
        _ = p * (q * r) := by ring
        _ < L * (q * r) := mul_lt_mul_of_pos_right hlt (mul_pos qpos rpos)
        _ ≤ L * (L * L) := mul_le_mul_of_nonneg_left hqr hL.le
        _ = L ^ 3 := by ring
    exact (lt_irrefl _ hcontra)
  have hxlo := one x y z xpos ypos zpos hx hy hz hxyz
  have hylo : L ≤ y := by
    have heq : y * z * x = L ^ 3 := by rw [← hxyz]; ring
    exact one y z x ypos zpos xpos hy hz hx heq
  have hzlo : L ≤ z := by
    have heq : z * x * y = L ^ 3 := by rw [← hxyz]; ring
    exact one z x y zpos xpos ypos hz hx hy heq
  exact ⟨le_antisymm hx hxlo, le_antisymm hy hylo, le_antisymm hz hzlo⟩

/-- The exact labeled packet in the canonical alternating chamber. -/
def H6TightPacket (m lambda : ℝ)
    (a d c : Fin 6 → ℝ) : Prop :=
  a 0 = m ∧ a 1 = 2 * m ∧ a 2 = m ∧
  a 3 = 2 * m ∧ a 4 = m ∧ a 5 = 2 * m ∧
  c 0 = m ∧ c 1 = -m ∧ c 2 = m ∧
  c 3 = -m ∧ c 4 = m ∧ c 5 = -m ∧
  d 0 = lambda * m ∧ d 1 = (3 / lambda) * m ∧
  d 2 = lambda * m ∧ d 3 = (3 / lambda) * m ∧
  d 4 = lambda * m ∧ d 5 = (3 / lambda) * m

/-- Equality classification using only the radial floors and the six
consecutive Pluecker rows.  The wider interval `[1,3]` is sharp for this
local scalar system; outer-triangle floors are added below. -/
theorem h6_tight_array_equality_normal_form
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd : ∀ i, m ≤ d i)
    (hc0 : m ≤ c 0) (hc1 : c 1 ≤ -m) (hc2 : m ≤ c 2)
    (hc3 : c 3 ≤ -m) (hc4 : m ≤ c 4) (hc5 : c 5 ≤ -m)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (heq : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 = 9 * m) :
    ∃ lambda : ℝ, 1 ≤ lambda ∧ lambda ≤ 3 ∧
      H6TightPacket m lambda a d c := by
  have hanonneg : ∀ i, 0 ≤ a i := fun i => le_trans hm.le (ha i)
  have hdpos : ∀ i, 0 < d i := fun i => hm.trans_le (hd i)
  have hdnonneg : ∀ i, 0 ≤ d i := fun i => (hdpos i).le
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
      _ ≤ a i * a j + (-m) * m :=
        add_le_add_right (hca0.trans hca1) (a i * a j)
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
  let u := a 1 - m
  let v := a 3 - m
  let w := a 5 - m
  have hu : 0 ≤ u := by simp only [u]; exact sub_nonneg.mpr (ha 1)
  have hv : 0 ≤ v := by simp only [v]; exact sub_nonneg.mpr (ha 3)
  have hw : 0 ≤ w := by simp only [w]; exact sub_nonneg.mpr (ha 5)
  have huvwsum : u + v + w ≤ 3 * m := by
    simp only [u, v, w]
    linarith only [heq, ha 0, ha 2, ha 4]
  have hprod :
      m ^ 3 * ((2 * m + u) * (2 * m + v) * (2 * m + w)) ≤
        eqPairR m u v * eqPairR m v w * eqPairR m w u := by
    simp only [u, v, w]
    calc
      m ^ 3 *
          ((2 * m + (a 1 - m)) * (2 * m + (a 3 - m)) *
            (2 * m + (a 5 - m))) =
          m ^ 3 * ((m + a 1) * (m + a 3) * (m + a 5)) := by ring
      _ ≤ (a 1 * a 3 - m * m) * (a 3 * a 5 - m * m) *
          (a 5 * a 1 - m * m) := hraw
      _ = eqPairR m (a 1 - m) (a 3 - m) *
          eqPairR m (a 3 - m) (a 5 - m) *
            eqPairR m (a 5 - m) (a 1 - m) := by
        simp only [eqPairR]
        ring
  obtain ⟨hu_eq, hv_eq, hw_eq⟩ :=
    cyclic_product_eq hm hu hv hw huvwsum hprod
  have ha1 : a 1 = 2 * m := by simp only [u] at hu_eq; linarith
  have ha3 : a 3 = 2 * m := by simp only [v] at hv_eq; linarith
  have ha5 : a 5 = 2 * m := by simp only [w] at hw_eq; linarith
  have ha0 : a 0 = m := by linarith only [heq, ha 0, ha 2, ha 4, ha1, ha3, ha5]
  have ha2 : a 2 = m := by linarith only [heq, ha 0, ha 2, ha 4, ha1, ha3, ha5]
  have ha4 : a 4 = m := by linarith only [heq, ha 0, ha 2, ha 4, ha1, ha3, ha5]
  let L : ℝ := 3 * m ^ 2
  have hL : 0 < L := by simp only [L]; positivity
  have hD01lo : L ≤ d 0 * d 1 := by
    simp only [L, ha1] at hlo0 ⊢
    nlinarith only [hlo0]
  have hD23lo : L ≤ d 2 * d 3 := by
    simp only [L, ha3] at hlo2 ⊢
    nlinarith only [hlo2]
  have hD45lo : L ≤ d 4 * d 5 := by
    simp only [L, ha5] at hlo4 ⊢
    nlinarith only [hlo4]
  have hD12up : d 1 * d 2 ≤ L := by
    simp only [L, ha1, ha3] at hup1 ⊢
    nlinarith only [hup1]
  have hD34up : d 3 * d 4 ≤ L := by
    simp only [L, ha3, ha5] at hup3 ⊢
    nlinarith only [hup3]
  have hD50up : d 5 * d 0 ≤ L := by
    simp only [L, ha5, ha1] at hup5 ⊢
    nlinarith only [hup5]
  have heven_lower : L ^ 3 ≤
      (d 0 * d 1) * (d 2 * d 3) * (d 4 * d 5) := by
    have h01_23 := mul_le_mul hD01lo hD23lo hL.le
      (le_trans hL.le hD01lo)
    have hall := mul_le_mul h01_23 hD45lo hL.le
      (mul_nonneg (mul_nonneg (hdnonneg 0) (hdnonneg 1))
        (mul_nonneg (hdnonneg 2) (hdnonneg 3)))
    calc
      L ^ 3 = (L * L) * L := by ring
      _ ≤ (d 0 * d 1) * (d 2 * d 3) * (d 4 * d 5) := by
        simpa only [mul_assoc] using hall
  have hodd_upper :
      (d 1 * d 2) * (d 3 * d 4) * (d 5 * d 0) ≤ L ^ 3 := by
    have h12_34 := mul_le_mul hD12up hD34up
      (mul_nonneg (hdnonneg 3) (hdnonneg 4)) hL.le
    have hall := mul_le_mul h12_34 hD50up
      (mul_nonneg (hdnonneg 5) (hdnonneg 0))
      (mul_nonneg hL.le hL.le)
    calc
      (d 1 * d 2) * (d 3 * d 4) * (d 5 * d 0) ≤
          (L * L) * L := by simpa only [mul_assoc] using hall
      _ = L ^ 3 := by ring
  have heven_eq :
      (d 0 * d 1) * (d 2 * d 3) * (d 4 * d 5) = L ^ 3 := by
    apply le_antisymm
    · rw [hparity]
      exact hodd_upper
    · exact heven_lower
  obtain ⟨hD01, hD23, hD45⟩ :=
    three_eq_of_lower_mul hL hD01lo hD23lo hD45lo heven_eq
  have hodd_eq :
      (d 1 * d 2) * (d 3 * d 4) * (d 5 * d 0) = L ^ 3 := by
    rw [← hparity]
    exact heven_eq
  obtain ⟨hD12, hD34, hD50⟩ :=
    three_eq_of_upper_mul hL
      (mul_pos (hdpos 1) (hdpos 2))
      (mul_pos (hdpos 3) (hdpos 4))
      (mul_pos (hdpos 5) (hdpos 0))
      hD12up hD34up hD50up hodd_eq
  have hc0eq : c 0 = m := by
    have hr : d 0 * d 1 = a 0 * a 2 + c 0 * a 1 := by
      simpa using hrel 0
    simp only [ha0, ha1, ha2, L] at hr hD01
    have hfac : (2 * m) * (c 0 - m) = 0 := by nlinarith only [hr, hD01]
    rcases mul_eq_zero.mp hfac with hm0 | hc
    · nlinarith only [hm, hm0]
    · linarith
  have hc1eq : c 1 = -m := by
    have hr : d 1 * d 2 = a 1 * a 3 + c 1 * a 2 := by
      simpa using hrel 1
    simp only [ha1, ha2, ha3, L] at hr hD12
    have hfac : m * (c 1 + m) = 0 := by nlinarith only [hr, hD12]
    rcases mul_eq_zero.mp hfac with hm0 | hc
    · exact (ne_of_gt hm hm0).elim
    · linarith
  have hc2eq : c 2 = m := by
    have hr : d 2 * d 3 = a 2 * a 4 + c 2 * a 3 := by
      simpa using hrel 2
    simp only [ha2, ha3, ha4, L] at hr hD23
    have hfac : (2 * m) * (c 2 - m) = 0 := by nlinarith only [hr, hD23]
    rcases mul_eq_zero.mp hfac with hm0 | hc
    · nlinarith only [hm, hm0]
    · linarith
  have hc3eq : c 3 = -m := by
    have hr : d 3 * d 4 = a 3 * a 5 + c 3 * a 4 := by
      simpa using hrel 3
    simp only [ha3, ha4, ha5, L] at hr hD34
    have hfac : m * (c 3 + m) = 0 := by nlinarith only [hr, hD34]
    rcases mul_eq_zero.mp hfac with hm0 | hc
    · exact (ne_of_gt hm hm0).elim
    · linarith
  have hc4eq : c 4 = m := by
    have hr : d 4 * d 5 = a 4 * a 0 + c 4 * a 5 := by
      simpa using hrel 4
    simp only [ha4, ha5, ha0, L] at hr hD45
    have hfac : (2 * m) * (c 4 - m) = 0 := by nlinarith only [hr, hD45]
    rcases mul_eq_zero.mp hfac with hm0 | hc
    · nlinarith only [hm, hm0]
    · linarith
  have hc5eq : c 5 = -m := by
    have hr : d 5 * d 0 = a 5 * a 1 + c 5 * a 0 := by
      simpa using hrel 5
    simp only [ha5, ha0, ha1, L] at hr hD50
    have hfac : m * (c 5 + m) = 0 := by nlinarith only [hr, hD50]
    rcases mul_eq_zero.mp hfac with hm0 | hc
    · exact (ne_of_gt hm hm0).elim
    · linarith
  let lambda := d 0 / m
  have hlambda_pos : 0 < lambda := by
    simp only [lambda]
    exact div_pos (hdpos 0) hm
  have hlambda_one : 1 ≤ lambda := by
    apply (le_div_iff₀ hm).2
    simpa only [one_mul] using hd 0
  have hd0eq : d 0 = lambda * m := by
    simp only [lambda]
    field_simp [ne_of_gt hm]
  have hlambda_d1 : lambda * d 1 = 3 * m := by
    have hfac : m * (lambda * d 1 - 3 * m) = 0 := by
      calc
        m * (lambda * d 1 - 3 * m) =
            (lambda * m) * d 1 - m * (3 * m) := by ring
        _ = d 0 * d 1 - L := by rw [hd0eq]; simp only [L]; ring
        _ = 0 := by rw [hD01]; ring
    rcases mul_eq_zero.mp hfac with hm0 | hrest
    · exact (ne_of_gt hm hm0).elim
    · linarith only [hrest]
  have hlambda_three : lambda ≤ 3 := by
    have hmul := mul_le_mul_of_nonneg_left (hd 1) hlambda_pos.le
    rw [hlambda_d1] at hmul
    exact le_of_mul_le_mul_right hmul hm
  have hodd_value (i : Fin 6) (hi : d 0 * d i = L) :
      d i = (3 / lambda) * m := by
    have hli : lambda * d i = 3 * m := by
      have hfac : m * (lambda * d i - 3 * m) = 0 := by
        calc
          m * (lambda * d i - 3 * m) =
              (lambda * m) * d i - m * (3 * m) := by ring
          _ = d 0 * d i - L := by rw [hd0eq]; simp only [L]; ring
          _ = 0 := by rw [hi]; ring
      rcases mul_eq_zero.mp hfac with hm0 | hrest
      · exact (ne_of_gt hm hm0).elim
      · linarith only [hrest]
    have hdiv : d i = (3 * m) / lambda := by
      apply (eq_div_iff (ne_of_gt hlambda_pos)).2
      calc
        d i * lambda = lambda * d i := mul_comm _ _
        _ = 3 * m := hli
    calc
      d i = (3 * m) / lambda := hdiv
      _ = (3 / lambda) * m := by
        field_simp [ne_of_gt hlambda_pos]
        <;> ring
  have hd1eq : d 1 = (3 / lambda) * m :=
    hodd_value 1 hD01
  have hd2eq : d 2 = lambda * m := by
    have hd2pos := hdpos 2
    have hd1pos := hdpos 1
    have hfac : d 1 * (d 2 - d 0) = 0 := by
      simp only [L] at hD12 hD01
      nlinarith only [hD12, hD01]
    rcases mul_eq_zero.mp hfac with hbad | hgood
    · exact (ne_of_gt hd1pos hbad).elim
    · rw [sub_eq_zero.mp hgood, hd0eq]
  have hd3eq : d 3 = (3 / lambda) * m := by
    have hprod03 : d 0 * d 3 = L := by
      calc
        d 0 * d 3 = d 2 * d 3 := by rw [hd2eq, hd0eq]
        _ = L := hD23
    exact hodd_value 3 hprod03
  have hd4eq : d 4 = lambda * m := by
    have hfac : d 3 * (d 4 - d 0) = 0 := by
      have hprod30 : d 3 * d 0 = L := by
        calc
          d 3 * d 0 = d 3 * d 2 := by rw [hd2eq, hd0eq]
          _ = L := by rw [mul_comm]; exact hD23
      simp only [L] at hD34 hprod30
      nlinarith only [hD34, hprod30]
    rcases mul_eq_zero.mp hfac with hbad | hgood
    · exact (ne_of_gt (hdpos 3) hbad).elim
    · rw [sub_eq_zero.mp hgood, hd0eq]
  have hd5eq : d 5 = (3 / lambda) * m := by
    have hprod05 : d 0 * d 5 = L := by rw [mul_comm]; exact hD50
    exact hodd_value 5 hprod05
  refine ⟨lambda, hlambda_one, hlambda_three, ?_⟩
  exact ⟨ha0, ha1, ha2, ha3, ha4, ha5,
    hc0eq, hc1eq, hc2eq, hc3eq, hc4eq, hc5eq,
    hd0eq, hd1eq, hd2eq, hd3eq, hd4eq, hd5eq⟩

/-- A `sum ≤ 9m` hypothesis is already equality in the tight chamber,
because `h6_tight_array_bound` supplies the reverse inequality. -/
theorem h6_tight_array_normal_form_of_le
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd : ∀ i, m ≤ d i)
    (hc0 : m ≤ c 0) (hc1 : c 1 ≤ -m) (hc2 : m ≤ c 2)
    (hc3 : c 3 ≤ -m) (hc4 : m ≤ c 4) (hc5 : c 5 ≤ -m)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (hle : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 ≤ 9 * m) :
    ∃ lambda : ℝ, 1 ≤ lambda ∧ lambda ≤ 3 ∧
      H6TightPacket m lambda a d c := by
  have hge := h6_tight_array_bound m a d c hm ha hd
    hc0 hc1 hc2 hc3 hc4 hc5 hrel
  have heq : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 = 9 * m :=
    le_antisymm hle hge
  exact h6_tight_array_equality_normal_form m a d c hm ha hd
    hc0 hc1 hc2 hc3 hc4 hc5 hrel heq

/-- Two consecutive outer-triangle floors cut the scalar equality interval
from `[1,3]` to the realizable convex interval `[3/2,2]`. -/
theorem h6_tight_array_equality_with_outer_floors
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd : ∀ i, m ≤ d i)
    (hc0 : m ≤ c 0) (hc1 : c 1 ≤ -m) (hc2 : m ≤ c 2)
    (hc3 : c 3 ≤ -m) (hc4 : m ≤ c 4) (hc5 : c 5 ≤ -m)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (h012 : m ≤ a 0 + a 1 - d 0)
    (h123 : m ≤ a 1 + a 2 - d 1)
    (heq : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 = 9 * m) :
    ∃ lambda : ℝ, (3 : ℝ) / 2 ≤ lambda ∧ lambda ≤ 2 ∧
      H6TightPacket m lambda a d c := by
  obtain ⟨lambda, hl1, hl3, hp⟩ :=
    h6_tight_array_equality_normal_form m a d c hm ha hd
      hc0 hc1 hc2 hc3 hc4 hc5 hrel heq
  rcases hp with ⟨ha0, ha1, ha2, ha3, ha4, ha5,
    hc0eq, hc1eq, hc2eq, hc3eq, hc4eq, hc5eq,
    hd0eq, hd1eq, hd2eq, hd3eq, hd4eq, hd5eq⟩
  have hlpos : 0 < lambda := lt_of_lt_of_le (by norm_num) hl1
  have hl2 : lambda ≤ 2 := by
    rw [ha0, ha1, hd0eq] at h012
    have hmul : lambda * m ≤ 2 * m := by linarith only [h012]
    exact le_of_mul_le_mul_right hmul hm
  have hthree_div_le : 3 / lambda ≤ 2 := by
    rw [ha1, ha2, hd1eq] at h123
    have hmul : (3 / lambda) * m ≤ 2 * m := by linarith only [h123]
    exact le_of_mul_le_mul_right hmul hm
  have hl32 : (3 : ℝ) / 2 ≤ lambda := by
    have hthree : (3 : ℝ) ≤ 2 * lambda :=
      (div_le_iff₀ hlpos).1 hthree_div_le
    nlinarith only [hthree]
  refine ⟨lambda, hl32, hl2, ?_⟩
  exact ⟨ha0, ha1, ha2, ha3, ha4, ha5,
    hc0eq, hc1eq, hc2eq, hc3eq, hc4eq, hc5eq,
    hd0eq, hd1eq, hd2eq, hd3eq, hd4eq, hd5eq⟩

/-- The canonical equality theorem in the form used by a global sharpness
audit: an a priori upper bound on the adjacent sum, together with the two
outer floors, pins the full packet and its exact parameter interval. -/
theorem h6_tight_array_normal_form_of_le_with_outer_floors
    (m : ℝ) (a d c : Fin 6 → ℝ)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i)
    (hd : ∀ i, m ≤ d i)
    (hc0 : m ≤ c 0) (hc1 : c 1 ≤ -m) (hc2 : m ≤ c 2)
    (hc3 : c 3 ≤ -m) (hc4 : m ≤ c 4) (hc5 : c 5 ≤ -m)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (h012 : m ≤ a 0 + a 1 - d 0)
    (h123 : m ≤ a 1 + a 2 - d 1)
    (hle : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 ≤ 9 * m) :
    ∃ lambda : ℝ, (3 : ℝ) / 2 ≤ lambda ∧ lambda ≤ 2 ∧
      H6TightPacket m lambda a d c := by
  have hge := h6_tight_array_bound m a d c hm ha hd
    hc0 hc1 hc2 hc3 hc4 hc5 hrel
  have heq : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 = 9 * m :=
    le_antisymm hle hge
  exact h6_tight_array_equality_with_outer_floors m a d c hm ha hd
    hc0 hc1 hc2 hc3 hc4 hc5 hrel h012 h123 heq

/-- Bracket-level equality normal form in the literal canonical chamber. -/
theorem h6_tight_chamber_equality_normal_form
    (m : ℝ) (b : Fin 6 → Fin 6 → ℝ)
    (hm : 0 < m)
    (hskew : ∀ i j, b i j = -b j i)
    (hgp : ∀ i j k l,
      b i j * b k l - b i k * b j l + b i l * b j k = 0)
    (hradial : ∀ i j, i ≠ j → m ≤ |b i j|)
    (hhull : ∀ i j k, i < j → j < k →
      m ≤ b i j + b j k - b i k)
    (hedge : ∀ i : Fin 6, 0 < b i (i + 1))
    (hchamber : H6TightChamber b)
    (heq : b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 = 9 * m) :
    ∃ lambda : ℝ, (3 : ℝ) / 2 ≤ lambda ∧ lambda ≤ 2 ∧
      H6TightPacket m lambda
        (fun i => b i (i + 1)) (fun i => b i (i + 2))
          (fun i => b i (i + 3)) := by
  rcases hchamber with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hc0pos, hc1neg, hc2pos⟩
  let a : Fin 6 → ℝ := fun i => b i (i + 1)
  let d : Fin 6 → ℝ := fun i => b i (i + 2)
  let c : Fin 6 → ℝ := fun i => b i (i + 3)
  have ha : ∀ i, m ≤ a i := by
    intro i
    have hf := hradial i (i + 1) (by fin_cases i <;> decide)
    rw [abs_of_pos (hedge i)] at hf
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
    have hf := hradial i (i + 2) (by fin_cases i <;> decide)
    rw [abs_of_pos (hdpos i)] at hf
    exact hf
  have hc0 : m ≤ c 0 := by
    have hf := hradial 0 3 (by decide)
    simpa [c, abs_of_pos hc0pos] using hf
  have hc1 : c 1 ≤ -m := by
    have hf := hradial 1 4 (by decide)
    rw [abs_of_neg hc1neg] at hf
    change b 1 4 ≤ -m
    linarith
  have hc2 : m ≤ c 2 := by
    have hf := hradial 2 5 (by decide)
    simpa [c, abs_of_pos hc2pos] using hf
  have hc3 : c 3 ≤ -m := by
    have hs := hskew 3 0
    have hf := hradial 0 3 (by decide)
    rw [abs_of_pos hc0pos] at hf
    change b 3 0 ≤ -m
    linarith
  have hc4 : m ≤ c 4 := by
    have hs := hskew 4 1
    have hf := hradial 1 4 (by decide)
    rw [abs_of_neg hc1neg] at hf
    change m ≤ b 4 1
    linarith
  have hc5 : c 5 ≤ -m := by
    have hs := hskew 5 2
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
  have h012 : m ≤ a 0 + a 1 - d 0 := by
    simpa [a, d] using hhull 0 1 2 (by decide) (by decide)
  have h123 : m ≤ a 1 + a 2 - d 1 := by
    simpa [a, d] using hhull 1 2 3 (by decide) (by decide)
  have heq' : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 = 9 * m := by
    simpa [a] using heq
  simpa [a, d, c] using
    h6_tight_array_equality_with_outer_floors m a d c hm ha hd
      hc0 hc1 hc2 hc3 hc4 hc5 hrel h012 h123 heq'

/-- Determinant of two coordinate pairs. -/
def h6Det (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- A determinant-one gauge representative of every canonical tight equality
packet.  Its first two rays have bracket `m`. -/
noncomputable def h6TightGauge (m lambda : ℝ) : Fin 6 → ℝ × ℝ :=
  ![(1, 0), (0, m), (-2, lambda * m), (-3 / lambda, m),
    (1, -lambda * m), (3 / lambda, -2 * m)]

/-- The explicit gauge realizes precisely the canonical packet.  This is the
forward half of the coordinate reconstruction interface; the converse follows
from the two reference-bracket identities below. -/
theorem h6TightGauge_packet
    (m lambda : ℝ) (hm : 0 < m) (hlambda : 0 < lambda) :
    H6TightPacket m lambda
      (fun i => h6Det (h6TightGauge m lambda i)
        (h6TightGauge m lambda (i + 1)))
      (fun i => h6Det (h6TightGauge m lambda i)
        (h6TightGauge m lambda (i + 2)))
      (fun i => h6Det (h6TightGauge m lambda i)
        (h6TightGauge m lambda (i + 3))) := by
  unfold H6TightPacket
  repeat' apply And.intro
  all_goals
    simp [h6TightGauge, h6Det] <;>
      field_simp [ne_of_gt hlambda] <;> ring

/-- Once two reference rays have been put at `(1,0)` and `(0,m)`, their
brackets recover every remaining coordinate. -/
theorem h6_coordinates_from_reference_brackets
    (m : ℝ) (x y : Fin 6 → ℝ)
    (hx0 : x 0 = 1) (hy0 : y 0 = 0)
    (hx1 : x 1 = 0) (hy1 : y 1 = m) :
    (∀ j, h6Det (x 0, y 0) (x j, y j) = y j) ∧
    (∀ j, h6Det (x 1, y 1) (x j, y j) = -m * x j) := by
  constructor
  · intro j
    simp only [h6Det]
    rw [hx0, hy0]
    ring
  · intro j
    simp only [h6Det]
    rw [hx1, hy1]
    ring

/-! ## Comparison with the rational optimizer family -/

/-- The fixed determinant-one linear map taking the reference gauge above to
the coordinates used by `rationalOptimizerHex`. -/
noncomputable def h6TightGaugeToRational (u : ℝ × ℝ) : ℝ × ℝ :=
  (2 * u.1 + u.2, u.2 / 2)

theorem h6Det_tightGaugeToRational (u v : ℝ × ℝ) :
    h6Det (h6TightGaugeToRational u) (h6TightGaugeToRational v) =
      h6Det u v := by
  rcases u with ⟨ux, uy⟩
  rcases v with ⟨vx, vy⟩
  simp only [h6TightGaugeToRational, h6Det, Prod.fst, Prod.snd]
  ring

/-- If `tau > 0`, the optimizer coordinates are the tight gauge with
`m = 2*tau` and `lambda = 2/tau`, followed by the determinant-one map above.
Thus this is an exact affine/Pluecker identification, not merely agreement of
the six adjacent brackets. -/
theorem rationalOptimizerHex_eq_tightGauge (tau : ℝ) (htau : 0 < tau) :
    ∀ i : Fin 6,
      rationalOptimizerHex tau i =
        h6TightGaugeToRational
          (h6TightGauge (2 * tau) (2 / tau) i) := by
  intro i
  fin_cases i <;>
    simp [rationalOptimizerHex, h6TightGauge,
      h6TightGaugeToRational] <;>
    field_simp [ne_of_gt htau] <;> ring <;> simp

/-- The exact packet carried by the rational coordinate family.  In
particular its equality parameter is `lambda = 2/tau`. -/
theorem rationalOptimizerHex_tightPacket (tau : ℝ) (htau : 0 < tau) :
    H6TightPacket (2 * tau) (2 / tau)
      (fun i => h6Det (rationalOptimizerHex tau i)
        (rationalOptimizerHex tau (i + 1)))
      (fun i => h6Det (rationalOptimizerHex tau i)
        (rationalOptimizerHex tau (i + 2)))
      (fun i => h6Det (rationalOptimizerHex tau i)
        (rationalOptimizerHex tau (i + 3))) := by
  have hm : 0 < 2 * tau := mul_pos (by norm_num) htau
  have hlambda : 0 < 2 / tau := div_pos (by norm_num) htau
  have hp := h6TightGauge_packet (2 * tau) (2 / tau) hm hlambda
  have hbracket (i j : Fin 6) :
      h6Det (rationalOptimizerHex tau i) (rationalOptimizerHex tau j) =
        h6Det (h6TightGauge (2 * tau) (2 / tau) i)
          (h6TightGauge (2 * tau) (2 / tau) j) := by
    rw [rationalOptimizerHex_eq_tightGauge tau htau i,
      rationalOptimizerHex_eq_tightGauge tau htau j,
      h6Det_tightGaugeToRational]
  simpa only [hbracket] using hp

/-- The maximal optimizer-coordinate interval `1 <= tau <= 4/3` is exactly
the tight bracket interval `3/2 <= lambda <= 2` under
`lambda = 2/tau`. -/
theorem rationalOptimizer_tau_lambda_iff (tau : ℝ) (htau : 0 < tau) :
    ((1 : ℝ) ≤ tau ∧ tau ≤ 4 / 3) ↔
      (3 / 2 ≤ 2 / tau ∧ 2 / tau ≤ 2) := by
  constructor
  · rintro ⟨htau1, htau4⟩
    constructor
    · apply (le_div_iff₀ htau).2
      nlinarith only [htau4]
    · apply (div_le_iff₀ htau).2
      nlinarith only [htau1]
  · rintro ⟨hlambda3, hlambda2⟩
    constructor
    · have h := (div_le_iff₀ htau).1 hlambda2
      nlinarith only [h]
    · have h := (le_div_iff₀ htau).1 hlambda3
      nlinarith only [h]

/-- Every point of the maximal `tau` interval realizes a full tight packet
in the exact outer-floor parameter interval. -/
theorem rationalOptimizerHex_maximal_tightPacket
    (tau : ℝ) (htau1 : (1 : ℝ) ≤ tau) (htau4 : tau ≤ 4 / 3) :
    (3 : ℝ) / 2 ≤ 2 / tau ∧ 2 / tau ≤ 2 ∧
      H6TightPacket (2 * tau) (2 / tau)
        (fun i => h6Det (rationalOptimizerHex tau i)
          (rationalOptimizerHex tau (i + 1)))
        (fun i => h6Det (rationalOptimizerHex tau i)
          (rationalOptimizerHex tau (i + 2)))
        (fun i => h6Det (rationalOptimizerHex tau i)
          (rationalOptimizerHex tau (i + 3))) := by
  have htau : 0 < tau := lt_of_lt_of_le (by norm_num) htau1
  have hinter :=
    (rationalOptimizer_tau_lambda_iff tau htau).1 ⟨htau1, htau4⟩
  exact ⟨hinter.1, hinter.2,
    rationalOptimizerHex_tightPacket tau htau⟩

end HeilbronnChallenge.N7Upper
