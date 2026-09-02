import Heil7.Hull6OneNegativeCertificate

/-!
# The normalized one-negative scalar endpoint

This file separates the mathematical reduction from the finite polynomial
certificate.  The three hypotheses `P`, `I`, and `K` are exactly the compact
necessary system extracted from the canonical one-negative two-step-bracket
chamber.  The conclusion supplies the missing three units of adjacent-sector
excess.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

set_option maxHeartbeats 800000 in
/-- The exact normalized `P/I/K` contradiction used by the one-negative
chamber. -/
theorem h6OneNegativePIK
    {p q r s t : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hP : 1 ≤ r * (1 + q + r + s))
    (hI : (1 + s) * (2 + q) ≤
      (1 + p) * s * (2 + r + s + t))
    (hK :
      (1 + s) * (1 + q) + (1 + t) * (2 + p + r + p * r) ≤
        (p + t + p * t) * (1 + s + t) * (1 + q)) :
    3 ≤ p + q + r + s + t := by
  by_contra hnot
  have hsum : p + q + r + s + t < 3 := lt_of_not_ge hnot
  let w : ℝ := 4 - p - t
  let d : ℝ := 3 + 4 * p - p ^ 2
  let R : ℝ := 1 / w
  let h : ℝ := 2 / d
  let A : ℝ := p + t + p * t
  let D : ℝ := A * (1 + s + t) - (1 + s)
  let C : ℝ → ℝ := fun x => (1 + t) * (2 + p + x + p * x)
  let smax : ℝ := 3 - p - t - R

  have hw1 : 1 < w := by
    simp only [w]
    linarith
  have hw : 0 < w := lt_trans (by norm_num) hw1
  have hrpos : 0 < r := by
    by_contra hn
    have hrle : r ≤ 0 := le_of_not_gt hn
    have hfactor : 0 < 1 + q + r + s := by
      nlinarith only [hq, hr, hs]
    have hprod : r * (1 + q + r + s) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hrle hfactor.le
    linarith
  have hradialFactor : 1 + q + r + s < w := by
    simp only [w]
    linarith
  have hrwStrict : r * (1 + q + r + s) < r * w :=
    mul_lt_mul_of_pos_left hradialFactor hrpos
  have hrw : 1 < r * w := hP.trans_lt hrwStrict
  have hRr : R < r := by
    simp only [R]
    exact (div_lt_iff₀ hw).2 (by simpa [mul_comm] using hrw)

  have hspos : 0 < s := by
    by_contra hn
    have hsle : s ≤ 0 := le_of_not_gt hn
    have hright : 0 < (1 + s) * (2 + q) := by
      have hsone : 0 < 1 + s := by nlinarith only [hs]
      positivity
    have htail : 0 < 2 + r + s + t := by positivity
    have hpone : 0 ≤ 1 + p := by positivity
    have hps : (1 + p) * s ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hpone hsle
    have hleft : (1 + p) * s * (2 + r + s + t) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg hps htail.le
    linarith only [hI, hright, hleft]
  have hIright : 2 * (1 + s) ≤ (1 + s) * (2 + q) := by
    have hqterm : 0 ≤ (1 + s) * q := by positivity
    nlinarith only [hqterm]
  have hItail : 2 + r + s + t < 5 - p := by
    linarith
  have hIcoef : 0 < (1 + p) * s := by positivity
  have hIupper :
      (1 + p) * s * (2 + r + s + t) <
        (1 + p) * s * (5 - p) := by
    exact mul_lt_mul_of_pos_left hItail hIcoef
  have hIchained : 2 * (1 + s) < (1 + p) * s * (5 - p) :=
    hIright.trans_lt (hI.trans_lt hIupper)
  have hsd : 2 < s * d := by
    simp only [d]
    nlinarith only [hIchained]
  have hd : 0 < d := by
    by_contra hn
    have hdle : d ≤ 0 := le_of_not_gt hn
    have hsdl : s * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs hdle
    linarith
  have hhs : h < s := by
    simp only [h]
    exact (div_lt_iff₀ hd).2 hsd

  have hKD : C r ≤ (1 + q) * D := by
    simp only [C, D, A]
    nlinarith only [hK]
  have hCpos : 0 < C r := by
    simp only [C]
    positivity
  have hqDpos : 0 < (1 + q) * D := hCpos.trans_le hKD
  have hDpos : 0 < D := by
    by_contra hn
    have hDle : D ≤ 0 := le_of_not_gt hn
    have hprod : (1 + q) * D ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hDle
    linarith
  have hbudget : 1 + q < w - r - s := by
    simp only [w]
    linarith
  have hbudgetMul : (1 + q) * D < (w - r - s) * D :=
    mul_lt_mul_of_pos_right hbudget hDpos
  have hFold : 0 < (w - r - s) * D - C r := by
    linarith only [hKD, hbudgetMul]
  have hfirst : (w - r - s) * D < (w - R - s) * D := by
    apply mul_lt_mul_of_pos_right _ hDpos
    linarith only [hRr]
  have hCR : C R < C r := by
    have hinner : 2 + p + R + p * R < 2 + p + r + p * r := by
      have hmul : p * R ≤ p * r :=
        mul_le_mul_of_nonneg_left hRr.le hp
      linarith only [hRr, hmul]
    simp only [C]
    exact mul_lt_mul_of_pos_left hinner (by positivity)
  have hG0 : 0 < (w - R - s) * D - C R := by
    linarith only [hFold, hfirst, hCR]

  have hsmax : s < smax := by
    simp only [smax]
    linarith only [hsum, hq, hRr]
  have hgap : 0 < smax - h := by linarith only [hhs, hsmax]
  let z : ℝ := (s - h) / (smax - h)
  have hz0 : 0 < z := by
    simp only [z]
    exact div_pos (sub_pos.mpr hhs) hgap
  have hz1 : z < 1 := by
    simp only [z]
    apply (div_lt_iff₀ hgap).2
    linarith only [hsmax]
  have hsz : s = h + z * (smax - h) := by
    simp only [z]
    field_simp [ne_of_gt hgap]
    <;> ring

  have hpt : p + t ≤ 3 := by linarith only [hsum, hq, hr, hs]
  have hNpos := h6OneNegativeNumerator_pos hp ht hpt hz0.le hz1.le
  have hNid :
      h6OneNegativeNumerator p t z =
        -(w * d) ^ 2 * ((w - R - s) * D - C R) := by
    let wd : ℝ := w * d
    let B : ℝ := A - 1
    let spanNum : ℝ := (w - 1) * wd - d - 2 * w
    let sNum : ℝ := 2 * w + z * spanNum
    let lNum : ℝ := (w ^ 2 - 1) * d - sNum
    let dNum : ℝ := B * ((1 + t) * wd + sNum) + t * wd
    let cNum : ℝ := (2 + p) * w + (1 + p)
    have hRw : R * w = 1 := by
      simp only [R]
      field_simp [ne_of_gt hw]
    have hhd : h * d = 2 := by
      simp only [h]
      field_simp [ne_of_gt hd]
    have hRwd : R * wd = d := by
      calc
        R * wd = (R * w) * d := by simp only [wd]; ring
        _ = d := by rw [hRw]; ring
    have hhwd : h * wd = 2 * w := by
      calc
        h * wd = (h * d) * w := by simp only [wd]; ring
        _ = 2 * w := by rw [hhd]
    have hsmax' : smax = w - 1 - R := by
      simp only [smax, w]
      ring
    have hspan : (smax - h) * wd = spanNum := by
      rw [hsmax']
      calc
        (w - 1 - R - h) * wd =
            (w - 1) * wd - R * wd - h * wd := by ring
        _ = spanNum := by rw [hRwd, hhwd]
    have hsNum : sNum = s * wd := by
      simp only [sNum]
      rw [hsz]
      calc
        2 * w + z * spanNum =
            h * wd + z * ((smax - h) * wd) := by rw [hhwd, hspan]
        _ = (h + z * (smax - h)) * wd := by ring
    have hbase : (w ^ 2 - 1) * d = (w - R) * wd := by
      calc
        (w ^ 2 - 1) * d = w * wd - d := by simp only [wd]; ring
        _ = w * wd - R * wd := by rw [hRwd]
        _ = (w - R) * wd := by ring
    have hlNum : lNum = (w - R - s) * wd := by
      simp only [lNum]
      rw [hsNum, hbase]
      ring
    have hdNum : dNum = wd * D := by
      simp only [dNum]
      rw [hsNum]
      simp only [B, D, A]
      ring
    have hfirstNum :
        (1 + t) * cNum * w * d ^ 2 = wd ^ 2 * C R := by
      symm
      calc
        wd ^ 2 * C R =
            (1 + t) * ((2 + p) * w + (1 + p) * (R * w)) *
              w * d ^ 2 := by simp only [C, wd]; ring
        _ = (1 + t) * cNum * w * d ^ 2 := by
          rw [hRw]
          simp only [cNum]
          ring
    change (1 + t) * cNum * w * d ^ 2 - lNum * dNum =
      -wd ^ 2 * ((w - R - s) * D - C R)
    rw [hfirstNum, hlNum, hdNum]
    ring
  have hwd : 0 < (w * d) ^ 2 := sq_pos_of_pos (mul_pos hw hd)
  have hNneg : h6OneNegativeNumerator p t z < 0 := by
    rw [hNid]
    have hprod := mul_pos hwd hG0
    nlinarith only [hprod]
  linarith only [hNpos, hNneg]

end HeilbronnChallenge.N7Upper
