import Mathlib

/-!
# Exact scalar certificates for the reverse q22 chamber

This file contains the one-variable Bernstein and homogeneous-cone
certificates used by the reverse-height half of the coincident q22 chamber.
All constants are rational and all displayed identities are checked by
`ring`; no approximate arithmetic or external certificate is used.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8.HullSixTwoFourQ22Reverse

noncomputable section

def dOf (q h : ℝ) : ℝ :=
  (h + 1) * (q + 1) / q

def a0Q (q h : ℝ) : ℝ :=
  ((q + 2) * h + 2 * (q + 1)) / (q * (q + 1))

def TQ (q h : ℝ) : ℝ :=
  q + 1 + h

def DQ (q h d M : ℝ) : ℝ :=
  q + h + (h / d) * M

def UQ (q h d M : ℝ) : ℝ :=
  TQ q h / DQ q h d M

def a0S (s d : ℝ) : ℝ :=
  1 / s + (s + 1) * d / s ^ 2

def TS (s d : ℝ) : ℝ :=
  (s - 1) * (s + d) / s

def kS (s d : ℝ) : ℝ :=
  (d * (s - 1) - s) / (s * d)

def MS (a s d : ℝ) : ℝ :=
  (17 : ℝ) / 2 - a - s - d

private noncomputable def bernsteinTwo
    (t c0 c1 c2 : ℝ) : ℝ :=
  c0 * (1 - t) ^ 2 +
    2 * c1 * t * (1 - t) +
    c2 * t ^ 2

private noncomputable def bernsteinThree
    (t c0 c1 c2 c3 : ℝ) : ℝ :=
  c0 * (1 - t) ^ 3 +
    3 * c1 * t * (1 - t) ^ 2 +
    3 * c2 * t ^ 2 * (1 - t) +
    c3 * t ^ 3

private noncomputable def bernsteinFive
    (t c0 c1 c2 c3 c4 c5 : ℝ) : ℝ :=
  c0 * (1 - t) ^ 5 +
    5 * c1 * t * (1 - t) ^ 4 +
    10 * c2 * t ^ 2 * (1 - t) ^ 3 +
    10 * c3 * t ^ 3 * (1 - t) ^ 2 +
    5 * c4 * t ^ 4 * (1 - t) +
    c5 * t ^ 5

private noncomputable def bernsteinSix
    (t c0 c1 c2 c3 c4 c5 c6 : ℝ) : ℝ :=
  c0 * (1 - t) ^ 6 +
    6 * c1 * t * (1 - t) ^ 5 +
    15 * c2 * t ^ 2 * (1 - t) ^ 4 +
    20 * c3 * t ^ 3 * (1 - t) ^ 3 +
    15 * c4 * t ^ 4 * (1 - t) ^ 2 +
    6 * c5 * t ^ 5 * (1 - t) +
    c6 * t ^ 6

private lemma bernsteinTwo_pos
    {t c0 c1 c2 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hc0 : 0 < c0) (hc1 : 0 ≤ c1) (hc2 : 0 < c2) :
    0 < bernsteinTwo t c0 c1 c2 := by
  by_cases ht : t = 0
  · subst t
    simpa [bernsteinTwo] using hc0
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have homt : 0 ≤ 1 - t := by linarith
    unfold bernsteinTwo
    positivity

private lemma bernsteinThree_pos
    {t c0 c1 c2 c3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hc0 : 0 < c0) (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) (hc3 : 0 < c3) :
    0 < bernsteinThree t c0 c1 c2 c3 := by
  by_cases ht : t = 0
  · subst t
    simpa [bernsteinThree] using hc0
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have homt : 0 ≤ 1 - t := by linarith
    unfold bernsteinThree
    positivity

private lemma bernsteinThree_pos_right
    {t c0 c1 c2 c3 : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) (hc3 : 0 < c3) :
    0 < bernsteinThree t c0 c1 c2 c3 := by
  have homt : 0 ≤ 1 - t := by linarith
  unfold bernsteinThree
  positivity

private lemma bernsteinFive_pos
    {t c0 c1 c2 c3 c4 c5 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hc0 : 0 < c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4) (hc5 : 0 < c5) :
    0 < bernsteinFive t c0 c1 c2 c3 c4 c5 := by
  by_cases ht : t = 0
  · subst t
    simpa [bernsteinFive] using hc0
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have homt : 0 ≤ 1 - t := by linarith
    unfold bernsteinFive
    positivity

private lemma bernsteinSix_pos
    {t c0 c1 c2 c3 c4 c5 c6 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hc0 : 0 < c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4) (hc5 : 0 ≤ c5)
    (hc6 : 0 < c6) :
    0 < bernsteinSix t c0 c1 c2 c3 c4 c5 c6 := by
  by_cases ht : t = 0
  · subst t
    simpa [bernsteinSix] using hc0
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have homt : 0 ≤ 1 - t := by linarith
    unfold bernsteinSix
    positivity

private def cubicP (q : ℝ) : ℝ :=
  -256 * q ^ 3 + 2656 * q ^ 2 - 7825 * q + 7488

private lemma cubicP_pos
    {q : ℝ} (hq0 : 0 ≤ q) (hq9 : q ≤ (9 : ℝ) / 2) :
    0 < cubicP q := by
  by_cases hq : q ≤ (9 : ℝ) / 4
  · let t : ℝ := 4 * q / 9
    have ht0 : 0 ≤ t := by dsimp [t]; positivity
    have ht1 : t ≤ 1 := by dsimp [t]; linarith
    have hpos := bernsteinThree_pos ht0 ht1
      (show (0 : ℝ) < 7488 by norm_num)
      (show (0 : ℝ) ≤ 6477 / 4 by norm_num)
      (show (0 : ℝ) ≤ 465 / 2 by norm_num)
      (show (0 : ℝ) < 1647 / 4 by norm_num)
    have hid :
        cubicP q = bernsteinThree t
          7488 (6477 / 4) (465 / 2) (1647 / 4) := by
      dsimp [cubicP, t, bernsteinThree]
      ring
    rw [hid]
    exact hpos
  · let t : ℝ := (4 * q - 9) / 9
    have hqmid : (9 : ℝ) / 4 < q := lt_of_not_ge hq
    have ht0 : 0 ≤ t := by dsimp [t]; linarith
    have ht1 : t ≤ 1 := by dsimp [t]; linarith
    have hpos := bernsteinThree_pos ht0 ht1
      (show (0 : ℝ) < 1647 / 4 by norm_num)
      (show (0 : ℝ) ≤ 591 by norm_num)
      (show (0 : ℝ) ≤ 9345 / 4 by norm_num)
      (show (0 : ℝ) < 5463 / 2 by norm_num)
    have hid :
        cubicP q = bernsteinThree t
          (1647 / 4) 591 (9345 / 4) (5463 / 2) := by
      dsimp [cubicP, t, bernsteinThree]
      ring
    rw [hid]
    exact hpos

private def numeratorN (q h : ℝ) : ℝ :=
  16 * (q + 1) * h ^ 2 +
    (16 * q ^ 2 - 87 * q + 32) * h -
    2 * q ^ 2 + 14 * q + 16

private lemma numeratorN_pos
    {q h : ℝ} (hq0 : 0 < q) (hq9 : q < (9 : ℝ) / 2) :
    0 < numeratorN q h := by
  have hp : 0 < cubicP q := cubicP_pos (le_of_lt hq0) (le_of_lt hq9)
  have hqp : 0 < q * cubicP q := mul_pos hq0 hp
  have hid :
      64 * (q + 1) * numeratorN q h =
        (32 * (q + 1) * h + (16 * q ^ 2 - 87 * q + 32)) ^ 2 +
          q * cubicP q := by
    simp [numeratorN, cubicP]
    ring
  have hrhs :
      0 < (32 * (q + 1) * h + (16 * q ^ 2 - 87 * q + 32)) ^ 2 +
        q * cubicP q := add_pos_of_nonneg_of_pos (sq_nonneg _) hqp
  have hscaled : 0 < 64 * (q + 1) * numeratorN q h := by
    rw [hid]
    exact hrhs
  have hscale : 0 < (64 : ℝ) * (q + 1) := by positivity
  by_contra hnot
  have hnle : numeratorN q h ≤ 0 := le_of_not_gt hnot
  have hmul : (64 * (q + 1)) * numeratorN q h ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hscale) hnle
  exact (not_lt_of_ge hmul) hscaled

private def hZero (q : ℝ) : ℝ :=
  (q - 2) * (q + 1) / (q + 2)

private def hMax (q : ℝ) : ℝ :=
  -((q + 1) * (2 * q ^ 2 - 11 * q + 6)) /
    (2 * (q ^ 2 + 3 * q + 3))

private def hMin (q : ℝ) : ℝ :=
  (q - 2) * (q + 1) / (q + 2)

private def numeratorOne (q h : ℝ) : ℝ :=
  30 * (q + 1) * h ^ 2 +
    (34 * q ^ 2 - 93 * q + 34) * h +
    4 * q ^ 3 - 6 * q ^ 2 - 6 * q + 4

private lemma numeratorOne_pos
    {q h : ℝ} (hq2 : 2 < q)
    (hh0 : 0 ≤ h) (hhH : h ≤ hZero q) :
    0 < numeratorOne q h := by
  have hq2p : 0 < q + 2 := by linarith
  have hq1p : 0 < q + 1 := by linarith
  have hH : 0 < hZero q := by
    dsimp [hZero]
    positivity
  let t : ℝ := h / hZero q
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hH).2 hhH
  let b0 : ℝ := 2 * (q - 2) * (q + 1) * (2 * q - 1)
  let b1 : ℝ :=
    (q - 2) * (q + 1) * (42 * q ^ 2 - 81 * q + 26) /
      (2 * (q + 2))
  let b2 : ℝ :=
    q * (q - 2) * (q + 1) * (68 * q ^ 2 - 11 * q - 234) /
      (q + 2) ^ 2
  have hcore1 : 0 < 42 * q ^ 2 - 81 * q + 26 := by
    have hp : 0 < (q - 2) * (42 * q + 3) := by positivity
    nlinarith
  have hcore2 : 0 < 68 * q ^ 2 - 11 * q - 234 := by
    have hp : 0 < (q - 2) * (68 * q + 125) := by positivity
    nlinarith
  have h2q1 : 0 < 2 * q - 1 := by linarith
  have hb0 : 0 < b0 := by dsimp [b0]; positivity
  have hb1 : 0 ≤ b1 := by dsimp [b1]; positivity
  have hb2 : 0 < b2 := by dsimp [b2]; positivity
  have hpos := bernsteinTwo_pos ht0 ht1 hb0 hb1 hb2
  have hid : numeratorOne q h = bernsteinTwo t b0 b1 b2 := by
    dsimp only [t, b0, b1, b2]
    unfold numeratorOne bernsteinTwo
    field_simp [ne_of_gt hq2p, ne_of_gt hH]
    unfold hZero
    field_simp [ne_of_gt hq2p]
    ring
  rw [hid]
  exact hpos

private def polynomialP1 (q : ℝ) : ℝ :=
  52 * q ^ 5 - 672 * q ^ 4 + 2287 * q ^ 3 -
    2780 * q ^ 2 + 900 * q - 144

private def polynomialP2 (q : ℝ) : ℝ :=
  68 * q ^ 6 - 552 * q ^ 5 + 667 * q ^ 4 + 328 * q ^ 3 -
    3529 * q ^ 2 - 1584 * q + 468

private def polynomialP3 (q : ℝ) : ℝ :=
  64 * q ^ 5 + 616 * q ^ 4 + 497 * q ^ 3 -
    3264 * q ^ 2 - 2604 * q + 3408

private def polynomialP4 (q : ℝ) : ℝ :=
  136 * q ^ 6 - 730 * q ^ 5 - 1947 * q ^ 4 + 1030 * q ^ 3 +
    1901 * q ^ 2 - 1604 * q - 492

private lemma neg_polynomialP1_pos
    {q : ℝ} (hq0 : (1 : ℝ) / 2 ≤ q) (hq2 : q ≤ 2) :
    0 < -polynomialP1 q := by
  let t : ℝ := (2 * q - 1) / 3
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hpos := bernsteinFive_pos ht0 ht1
    (show (0 : ℝ) < 287 / 2 by norm_num)
    (show (0 : ℝ) ≤ 5777 / 20 by norm_num)
    (show (0 : ℝ) ≤ 40001 / 80 by norm_num)
    (show (0 : ℝ) ≤ 8297 / 20 by norm_num)
    (show (0 : ℝ) ≤ 220 by norm_num)
    (show (0 : ℝ) < 256 by norm_num)
  have hid :
      -polynomialP1 q = bernsteinFive t
        (287 / 2) (5777 / 20) (40001 / 80) (8297 / 20) 220 256 := by
    dsimp [polynomialP1, t, bernsteinFive]
    ring
  rw [hid]
  exact hpos

private lemma neg_polynomialP2_pos
    {q : ℝ} (hq0 : (1 : ℝ) / 2 ≤ q) (hq2 : q ≤ 2) :
    0 < -polynomialP2 q := by
  let t : ℝ := (2 * q - 1) / 3
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hpos := bernsteinSix_pos ht0 ht1
    (show (0 : ℝ) < 4559 / 4 by norm_num)
    (show (0 : ℝ) ≤ 37009 / 16 by norm_num)
    (show (0 : ℝ) ≤ 310863 / 80 by norm_num)
    (show (0 : ℝ) ≤ 115633 / 20 by norm_num)
    (show (0 : ℝ) ≤ 161579 / 20 by norm_num)
    (show (0 : ℝ) ≤ 11451 by norm_num)
    (show (0 : ℝ) < 16832 by norm_num)
  have hid :
      -polynomialP2 q = bernsteinSix t
        (4559 / 4) (37009 / 16) (310863 / 80) (115633 / 20)
        (161579 / 20) 11451 16832 := by
    dsimp [polynomialP2, t, bernsteinSix]
    ring
  rw [hid]
  exact hpos

private lemma polynomialP3_pos
    {q : ℝ} (hq2 : 2 ≤ q) (hq9 : q ≤ (9 : ℝ) / 2) :
    0 < polynomialP3 q := by
  let t : ℝ := (2 * q - 4) / 5
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hpos := bernsteinFive_pos ht0 ht1
    (show (0 : ℝ) < 1024 by norm_num)
    (show (0 : ℝ) ≤ 8592 by norm_num)
    (show (0 : ℝ) ≤ 113695 / 4 by norm_num)
    (show (0 : ℝ) ≤ 1167933 / 16 by norm_num)
    (show (0 : ℝ) ≤ 658389 / 4 by norm_num)
    (show (0 : ℝ) < 2732637 / 8 by norm_num)
  have hid :
      polynomialP3 q = bernsteinFive t
        1024 8592 (113695 / 4) (1167933 / 16)
        (658389 / 4) (2732637 / 8) := by
    dsimp [polynomialP3, t, bernsteinFive]
    ring
  rw [hid]
  exact hpos

private lemma neg_polynomialP4_pos
    {q : ℝ} (hq2 : 2 ≤ q) (hq9 : q ≤ (9 : ℝ) / 2) :
    0 < -polynomialP4 q := by
  let t : ℝ := (2 * q - 4) / 5
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hpos := bernsteinSix_pos ht0 ht1
    (show (0 : ℝ) < 33664 by norm_num)
    (show (0 : ℝ) ≤ 196282 / 3 by norm_num)
    (show (0 : ℝ) ≤ 1488323 / 12 by norm_num)
    (show (0 : ℝ) ≤ 3626229 / 16 by norm_num)
    (show (0 : ℝ) ≤ 6292349 / 16 by norm_num)
    (show (0 : ℝ) ≤ 60679819 / 96 by norm_num)
    (show (0 : ℝ) < 7131927 / 8 by norm_num)
  have hid :
      -polynomialP4 q = bernsteinSix t
        33664 (196282 / 3) (1488323 / 12) (3626229 / 16)
        (6292349 / 16) (60679819 / 96) (7131927 / 8) := by
    dsimp [polynomialP4, t, bernsteinSix]
    ring
  rw [hid]
  exact hpos

private def numeratorZero (q h : ℝ) : ℝ :=
  -4 * h ^ 3 * q ^ 3 - 20 * h ^ 3 * q ^ 2 - 36 * h ^ 3 * q -
    24 * h ^ 3 + 30 * h ^ 2 * q ^ 4 + 138 * h ^ 2 * q ^ 3 +
    218 * h ^ 2 * q ^ 2 + 62 * h ^ 2 * q - 48 * h ^ 2 +
    38 * h * q ^ 5 - 69 * h * q ^ 4 - 86 * h * q ^ 3 +
    163 * h * q ^ 2 + 118 * h * q - 24 * h +
    4 * q ^ 6 - 6 * q ^ 5 - 22 * q ^ 4 + 10 * q ^ 3 +
    42 * q ^ 2 + 20 * q

private lemma denominatorQ_pos (q : ℝ) :
    0 < q ^ 2 + 3 * q + 3 := by
  nlinarith [sq_nonneg (q + (3 : ℝ) / 2)]

private lemma numeratorZero_pos_low
    {q h : ℝ}
    (hq0 : (1 : ℝ) / 2 ≤ q) (hq2 : q ≤ 2)
    (hh0 : 0 < h) (hhH : h ≤ hMax q) :
    0 < numeratorZero q h := by
  have hD : 0 < q ^ 2 + 3 * q + 3 := denominatorQ_pos q
  have hHp : 0 < hMax q := lt_of_lt_of_le hh0 hhH
  let t : ℝ := h / hMax q
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hHp).2 hhH
  let c0 : ℝ :=
    2 * q * (2 - q) * (q + 1) ^ 3 * (5 - 2 * q)
  let c1 : ℝ :=
    (q + 1) ^ 3 * (-polynomialP1 q) /
      (6 * (q ^ 2 + 3 * q + 3))
  let c2 : ℝ :=
    q * (q + 1) ^ 3 * (-polynomialP2 q) /
      (6 * (q ^ 2 + 3 * q + 3) ^ 2)
  let c3 : ℝ :=
    17 * q ^ 2 * (q + 1) ^ 3 * (-2 * q ^ 2 + 13 * q - 2) /
      (q ^ 2 + 3 * q + 3)
  have hqpos : 0 < q := by linarith
  have hP1 : 0 < -polynomialP1 q := neg_polynomialP1_pos hq0 hq2
  have hP2 : 0 < -polynomialP2 q := neg_polynomialP2_pos hq0 hq2
  have hlast : 0 < -2 * q ^ 2 + 13 * q - 2 := by
    have hleft : 0 ≤ q - (1 : ℝ) / 2 := by linarith
    have hright : 0 ≤ 12 - 2 * q := by linarith
    have hp : 0 ≤ (q - (1 : ℝ) / 2) * (12 - 2 * q) :=
      mul_nonneg hleft hright
    nlinarith
  have h2q : 0 ≤ 2 - q := by linarith
  have h5q : 0 ≤ 5 - 2 * q := by linarith
  have hc0 : 0 ≤ c0 := by dsimp [c0]; positivity
  have hc1 : 0 ≤ c1 := by dsimp [c1]; positivity
  have hc2 : 0 ≤ c2 := by dsimp [c2]; positivity
  have hc3 : 0 < c3 := by dsimp [c3]; positivity
  have hpos := bernsteinThree_pos_right ht0 ht1 hc0 hc1 hc2 hc3
  have hid :
      numeratorZero q h = bernsteinThree t c0 c1 c2 c3 := by
    dsimp only [t, c0, c1, c2, c3]
    unfold numeratorZero polynomialP1 polynomialP2 bernsteinThree
    field_simp [ne_of_gt hD, ne_of_gt hHp]
    unfold hMax
    field_simp [ne_of_gt hD]
    ring
  rw [hid]
  exact hpos

private lemma numeratorZero_pos_high
    {q h : ℝ}
    (hq2 : 2 ≤ q) (hq9 : q ≤ (9 : ℝ) / 2)
    (hhL : hMin q < h) (hhH : h ≤ hMax q) :
    0 < numeratorZero q h := by
  have hD : 0 < q ^ 2 + 3 * q + 3 := denominatorQ_pos q
  have hq2p : 0 < q + 2 := by linarith
  have hwidth : 0 < hMax q - hMin q := by linarith
  let t : ℝ := (h - hMin q) / (hMax q - hMin q)
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_one hwidth).2
    linarith
  let d0 : ℝ :=
    q ^ 2 * (q - 2) * (q + 1) ^ 3 *
      (68 * q ^ 2 - 11 * q - 234) / (q + 2) ^ 2
  let d1 : ℝ :=
    q ^ 2 * (q + 1) ^ 3 * polynomialP3 q /
      (6 * (q + 2) ^ 2 * (q ^ 2 + 3 * q + 3))
  let d2 : ℝ :=
    q ^ 2 * (q + 1) ^ 3 * (-polynomialP4 q) /
      (6 * (q + 2) * (q ^ 2 + 3 * q + 3) ^ 2)
  let d3 : ℝ :=
    17 * q ^ 2 * (q + 1) ^ 3 * (-2 * q ^ 2 + 13 * q - 2) /
      (q ^ 2 + 3 * q + 3)
  have hcore0 : 0 < 68 * q ^ 2 - 11 * q - 234 := by
    have hp : 0 ≤ (q - 2) * (68 * q + 125) := by positivity
    nlinarith
  have hP3 : 0 < polynomialP3 q := polynomialP3_pos hq2 hq9
  have hP4 : 0 < -polynomialP4 q := neg_polynomialP4_pos hq2 hq9
  have hlast : 0 < -2 * q ^ 2 + 13 * q - 2 := by
    have hp : 0 ≤ 2 * (q - 2) * ((9 : ℝ) / 2 - q) := by positivity
    nlinarith
  have hd0 : 0 ≤ d0 := by dsimp [d0]; positivity
  have hd1 : 0 ≤ d1 := by dsimp [d1]; positivity
  have hd2 : 0 ≤ d2 := by dsimp [d2]; positivity
  have hd3 : 0 < d3 := by dsimp [d3]; positivity
  have hpos := bernsteinThree_pos_right ht0 ht1 hd0 hd1 hd2 hd3
  have hid :
      numeratorZero q h = bernsteinThree t d0 d1 d2 d3 := by
    dsimp only [t, d0, d1, d2, d3]
    unfold numeratorZero polynomialP3 polynomialP4 bernsteinThree
    field_simp [ne_of_gt hD, ne_of_gt hq2p, ne_of_gt hwidth]
    unfold hMin hMax
    field_simp [ne_of_gt hD, ne_of_gt hq2p]
    ring
  rw [hid]
  exact hpos

/-- The rational upper quotient in the reverse q22 reduction is strictly
larger than `9/8`. -/
theorem u_gt_nine_eighths
    {q h d M : ℝ}
    (hq0 : 0 < q) (hq9 : q < (9 : ℝ) / 2) (hh : 0 < h)
    (hd : d = dOf q h)
    (hM : M ≤ (13 : ℝ) / 2 - q - d)
    (hD : 0 < DQ q h d M) :
    (9 : ℝ) / 8 < UQ q h d M := by
  rcases hd with rfl
  have hdpos : 0 < dOf q h := by
    dsimp [dOf]
    positivity
  let M0 : ℝ := (13 : ℝ) / 2 - q - dOf q h
  have hk : 0 < h / dOf q h := div_pos hh hdpos
  have hDle : DQ q h (dOf q h) M ≤ DQ q h (dOf q h) M0 := by
    have hmul := mul_le_mul_of_nonneg_left hM (le_of_lt hk)
    dsimp [DQ, M0] at hmul ⊢
    linarith
  have hN : 0 < numeratorN q h := numeratorN_pos hq0 hq9
  have hden : 0 < 2 * (h + 1) * (q + 1) := by positivity
  have hid :
      8 * TQ q h - 9 * DQ q h (dOf q h) M0 =
        numeratorN q h / (2 * (h + 1) * (q + 1)) := by
    dsimp [TQ, DQ, dOf, M0, numeratorN]
    field_simp [ne_of_gt hq0]
    ring
  have hgap0 : 0 < 8 * TQ q h - 9 * DQ q h (dOf q h) M0 := by
    rw [hid]
    exact div_pos hN hden
  have hgap :
      9 * DQ q h (dOf q h) M < 8 * TQ q h := by
    nlinarith
  dsimp [UQ]
  apply (lt_div_iff₀ hD).2
  nlinarith

private def coreQ (q h d a : ℝ) : ℝ :=
  a + (q + 1) + d +
    (a / d) * UQ q h d ((17 : ℝ) / 2 - (a + (q + 1) + d))

private lemma coreQ_mono
    {q h d x a : ℝ}
    (hq : 0 < q) (hh : 0 < h) (hd : 0 < d)
    (hx : 0 < x) (hxa : x ≤ a)
    (hDa : 0 < DQ q h d ((17 : ℝ) / 2 - (a + (q + 1) + d))) :
    coreQ q h d x ≤ coreQ q h d a := by
  let Mx : ℝ := (17 : ℝ) / 2 - (x + (q + 1) + d)
  let Ma : ℝ := (17 : ℝ) / 2 - (a + (q + 1) + d)
  have hM : Ma ≤ Mx := by dsimp [Ma, Mx]; linarith
  have hk : 0 < h / d := div_pos hh hd
  have hDord : DQ q h d Ma ≤ DQ q h d Mx := by
    have hmul := mul_le_mul_of_nonneg_left hM (le_of_lt hk)
    dsimp [DQ] at hmul ⊢
    linarith
  have hDx : 0 < DQ q h d Mx :=
    lt_of_lt_of_le (by simpa [Ma] using hDa) hDord
  have hT : 0 < TQ q h := by dsimp [TQ]; linarith
  have hUord : UQ q h d Mx ≤ UQ q h d Ma := by
    dsimp [UQ]
    apply (div_le_div_iff₀ hDx (by simpa [Ma] using hDa)).2
    exact mul_le_mul_of_nonneg_left hDord (le_of_lt hT)
  have hUx : 0 < UQ q h d Mx := by
    dsimp [UQ]
    exact div_pos hT hDx
  have hcoef : x / d ≤ a / d :=
    (div_le_div_iff_of_pos_right hd).2 hxa
  have hfirst : (x / d) * UQ q h d Mx ≤
      (a / d) * UQ q h d Mx :=
    mul_le_mul_of_nonneg_right hcoef (le_of_lt hUx)
  have hapos : 0 < a := lt_of_lt_of_le hx hxa
  have hsecond : (a / d) * UQ q h d Mx ≤
      (a / d) * UQ q h d Ma :=
    mul_le_mul_of_nonneg_left hUord (by positivity)
  dsimp [coreQ, Mx, Ma] at hfirst hsecond ⊢
  linarith

/-- The central core at any admissible `a` is strictly larger than `13/2`. -/
theorem core_gt_thirteen_halves
    {q h d a : ℝ}
    (hq0 : 0 < q) (hq9 : q < (9 : ℝ) / 2) (hh : 0 < h)
    (hd : d = dOf q h)
    (ha1 : 1 ≤ a) (ha0 : a0Q q h ≤ a)
    (hB : a + (q + 1) + d ≤ (15 : ℝ) / 2)
    (hD : 0 < DQ q h d
      ((17 : ℝ) / 2 - (a + (q + 1) + d))) :
    (13 : ℝ) / 2 <
      a + (q + 1) + d +
        (a / d) * UQ q h d
          ((17 : ℝ) / 2 - (a + (q + 1) + d)) := by
  rcases hd with rfl
  have hdpos : 0 < dOf q h := by
    dsimp [dOf]
    positivity
  have hdenQ : 0 < q * (q + 1) := by positivity
  by_cases hsmall : a0Q q h ≤ 1
  · have hmono : coreQ q h (dOf q h) 1 ≤
        coreQ q h (dOf q h) a :=
      coreQ_mono hq0 hh hdpos (by norm_num) ha1 hD
    have hMord :
        (17 : ℝ) / 2 - (a + (q + 1) + dOf q h) ≤
          (17 : ℝ) / 2 - (1 + (q + 1) + dOf q h) := by
      linarith
    have hk : 0 < h / dOf q h := div_pos hh hdpos
    have hDord :
        DQ q h (dOf q h)
            ((17 : ℝ) / 2 - (a + (q + 1) + dOf q h)) ≤
          DQ q h (dOf q h)
            ((17 : ℝ) / 2 - (1 + (q + 1) + dOf q h)) := by
      have hmul := mul_le_mul_of_nonneg_left hMord (le_of_lt hk)
      dsimp [DQ] at hmul ⊢
      linarith
    have hD1 : 0 < DQ q h (dOf q h)
        ((17 : ℝ) / 2 - (1 + (q + 1) + dOf q h)) :=
      lt_of_lt_of_le hD hDord
    have hraw :
        (q + 2) * h + 2 * (q + 1) ≤ q * (q + 1) := by
      exact (div_le_one hdenQ).1 (by simpa [a0Q] using hsmall)
    have hgap : 0 < (q - 2) * (q + 1) := by
      have hp : 0 < (q + 2) * h := by positivity
      nlinarith
    have hq2 : 2 < q := by
      by_contra hnot
      have hqle : q ≤ 2 := le_of_not_gt hnot
      have hnonpos : (q - 2) * (q + 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hqle) (by linarith)
      linarith
    have hhH : h ≤ hZero q := by
      dsimp [hZero]
      apply (le_div_iff₀ (by linarith : 0 < q + 2)).2
      nlinarith
    have hN : 0 < numeratorOne q h :=
      numeratorOne_pos hq2 (le_of_lt hh) hhH
    have hid :
        numeratorOne q h =
          4 * (h + 1) * (q + 1) *
            DQ q h (dOf q h)
              ((17 : ℝ) / 2 - (1 + (q + 1) + dOf q h)) *
            (coreQ q h (dOf q h) 1 - (13 : ℝ) / 2) := by
      calc
        numeratorOne q h =
            4 * (h + 1) * (q + 1) *
              (DQ q h (dOf q h)
                  ((17 : ℝ) / 2 - (1 + (q + 1) + dOf q h)) *
                    (1 + (q + 1) + dOf q h - (13 : ℝ) / 2) +
                (1 / dOf q h) * TQ q h) := by
          unfold numeratorOne DQ TQ
          field_simp [ne_of_gt hdpos]
          unfold dOf
          field_simp [ne_of_gt hq0]
          ring
        _ = 4 * (h + 1) * (q + 1) *
              DQ q h (dOf q h)
                ((17 : ℝ) / 2 - (1 + (q + 1) + dOf q h)) *
              (coreQ q h (dOf q h) 1 - (13 : ℝ) / 2) := by
          have hcancel :
              DQ q h (dOf q h)
                    ((17 : ℝ) / 2 - (1 + (q + 1) + dOf q h)) *
                  ((1 / dOf q h) *
                    (TQ q h /
                      DQ q h (dOf q h)
                        ((17 : ℝ) / 2 -
                          (1 + (q + 1) + dOf q h)))) =
                (1 / dOf q h) * TQ q h := by
            have hDfs :
                0 < DQ q h (dOf q h)
                  ((17 - 2 * (1 + (q + 1) + dOf q h)) / 2) := by
              rw [show
                ((17 : ℝ) - 2 * (1 + (q + 1) + dOf q h)) / 2 =
                  (17 : ℝ) / 2 - (1 + (q + 1) + dOf q h) by ring]
              exact hD1
            field_simp [ne_of_gt hdpos]
          unfold coreQ UQ
          rw [← hcancel]
          ring
    have hscale : 0 < 4 * (h + 1) * (q + 1) *
        DQ q h (dOf q h)
          ((17 : ℝ) / 2 - (1 + (q + 1) + dOf q h)) := by
      positivity
    have hboundary : (13 : ℝ) / 2 < coreQ q h (dOf q h) 1 := by
      rw [hid] at hN
      by_contra hnot
      have hle : coreQ q h (dOf q h) 1 - (13 : ℝ) / 2 ≤ 0 := by
        linarith
      have hmul := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hscale) hle
      exact (not_lt_of_ge hmul) hN
    exact hboundary.trans_le hmono
  · have hlarge : 1 < a0Q q h := lt_of_not_ge hsmall
    have ha0pos : 0 < a0Q q h := lt_trans zero_lt_one hlarge
    have hmono : coreQ q h (dOf q h) (a0Q q h) ≤
        coreQ q h (dOf q h) a :=
      coreQ_mono hq0 hh hdpos ha0pos ha0 hD
    have hMord :
        (17 : ℝ) / 2 - (a + (q + 1) + dOf q h) ≤
          (17 : ℝ) / 2 - (a0Q q h + (q + 1) + dOf q h) := by
      linarith
    have hk : 0 < h / dOf q h := div_pos hh hdpos
    have hDord :
        DQ q h (dOf q h)
            ((17 : ℝ) / 2 - (a + (q + 1) + dOf q h)) ≤
          DQ q h (dOf q h)
            ((17 : ℝ) / 2 - (a0Q q h + (q + 1) + dOf q h)) := by
      have hmul := mul_le_mul_of_nonneg_left hMord (le_of_lt hk)
      dsimp [DQ] at hmul ⊢
      linarith
    have hD0 : 0 < DQ q h (dOf q h)
        ((17 : ℝ) / 2 - (a0Q q h + (q + 1) + dOf q h)) :=
      lt_of_lt_of_le hD hDord
    have hB0 : a0Q q h + (q + 1) + dOf q h ≤ (15 : ℝ) / 2 :=
      by linarith
    have hcapMul :
        (a0Q q h + (q + 1) + dOf q h - (15 : ℝ) / 2) *
            (2 * q * (q + 1)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have hcapId :
        (a0Q q h + (q + 1) + dOf q h - (15 : ℝ) / 2) *
            (2 * q * (q + 1)) =
          2 * (q ^ 2 + 3 * q + 3) * h +
            (q + 1) * (2 * q ^ 2 - 11 * q + 6) := by
      dsimp [a0Q, dOf]
      field_simp [ne_of_gt hq0]
      ring
    rw [hcapId] at hcapMul
    have hpolyDen : 0 < 2 * (q ^ 2 + 3 * q + 3) := by
      have := denominatorQ_pos q
      positivity
    have hhH : h ≤ hMax q := by
      dsimp [hMax]
      apply (le_div_iff₀ hpolyDen).2
      nlinarith
    have hHp : 0 < hMax q := lt_of_lt_of_le hh hhH
    have hnumPos : 0 < -((q + 1) * (2 * q ^ 2 - 11 * q + 6)) := by
      have hquot :
          0 < -((q + 1) * (2 * q ^ 2 - 11 * q + 6)) /
            (2 * (q ^ 2 + 3 * q + 3)) := by
        simpa [hMax] using hHp
      have hmul := mul_pos hquot hpolyDen
      have hidMul :
          (-((q + 1) * (2 * q ^ 2 - 11 * q + 6)) /
              (2 * (q ^ 2 + 3 * q + 3))) *
              (2 * (q ^ 2 + 3 * q + 3)) =
            -((q + 1) * (2 * q ^ 2 - 11 * q + 6)) := by
        field_simp [ne_of_gt hpolyDen]
      rwa [hidMul] at hmul
    have hpolyNeg : 2 * q ^ 2 - 11 * q + 6 < 0 := by
      by_contra hnot
      have hpnonneg : 0 ≤ 2 * q ^ 2 - 11 * q + 6 := le_of_not_gt hnot
      have hprod : 0 ≤ (q + 1) * (2 * q ^ 2 - 11 * q + 6) := by
        positivity
      linarith
    have hqhalf : (1 : ℝ) / 2 < q := by
      by_contra hnot
      have hqle : q ≤ (1 : ℝ) / 2 := le_of_not_gt hnot
      nlinarith [sq_nonneg q]
    have hN : 0 < numeratorZero q h := by
      by_cases hq2 : q ≤ 2
      · exact numeratorZero_pos_low (le_of_lt hqhalf) hq2 hh hhH
      · have hq2' : 2 < q := lt_of_not_ge hq2
        have hrawLarge :
            q * (q + 1) < (q + 2) * h + 2 * (q + 1) := by
          have hraw :=
            (lt_div_iff₀ hdenQ).1 (by simpa [a0Q] using hlarge)
          nlinarith
        have hhL : hMin q < h := by
          dsimp [hMin]
          apply (div_lt_iff₀ (by linarith : 0 < q + 2)).2
          nlinarith
        exact numeratorZero_pos_high (le_of_lt hq2') (le_of_lt hq9) hhL hhH
    have hid :
        numeratorZero q h =
          4 * q * (h + 1) * (q + 1) ^ 3 *
            DQ q h (dOf q h)
              ((17 : ℝ) / 2 - (a0Q q h + (q + 1) + dOf q h)) *
            (coreQ q h (dOf q h) (a0Q q h) - (13 : ℝ) / 2) := by
      calc
        numeratorZero q h =
            4 * q * (h + 1) * (q + 1) ^ 3 *
              (DQ q h (dOf q h)
                  ((17 : ℝ) / 2 -
                    (a0Q q h + (q + 1) + dOf q h)) *
                    (a0Q q h + (q + 1) + dOf q h - (13 : ℝ) / 2) +
                (a0Q q h / dOf q h) * TQ q h) := by
          unfold numeratorZero DQ TQ
          field_simp [ne_of_gt hdpos]
          unfold dOf a0Q
          field_simp [ne_of_gt hq0, ne_of_gt hdenQ]
          ring
        _ = 4 * q * (h + 1) * (q + 1) ^ 3 *
              DQ q h (dOf q h)
                ((17 : ℝ) / 2 -
                  (a0Q q h + (q + 1) + dOf q h)) *
              (coreQ q h (dOf q h) (a0Q q h) - (13 : ℝ) / 2) := by
          have hcancel :
              DQ q h (dOf q h)
                    ((17 : ℝ) / 2 -
                      (a0Q q h + (q + 1) + dOf q h)) *
                  ((a0Q q h / dOf q h) *
                    (TQ q h /
                      DQ q h (dOf q h)
                        ((17 : ℝ) / 2 -
                          (a0Q q h + (q + 1) + dOf q h)))) =
                (a0Q q h / dOf q h) * TQ q h := by
            have hDfs :
                0 < DQ q h (dOf q h)
                  ((17 - 2 * (a0Q q h + (q + 1) + dOf q h)) / 2) := by
              rw [show
                ((17 : ℝ) -
                    2 * (a0Q q h + (q + 1) + dOf q h)) / 2 =
                  (17 : ℝ) / 2 -
                    (a0Q q h + (q + 1) + dOf q h) by ring]
              exact hD0
            field_simp [ne_of_gt hdpos]
          unfold coreQ UQ
          rw [← hcancel]
          ring
    have hscale : 0 < 4 * q * (h + 1) * (q + 1) ^ 3 *
        DQ q h (dOf q h)
          ((17 : ℝ) / 2 - (a0Q q h + (q + 1) + dOf q h)) := by
      positivity
    have hboundary :
        (13 : ℝ) / 2 < coreQ q h (dOf q h) (a0Q q h) := by
      rw [hid] at hN
      by_contra hnot
      have hle : coreQ q h (dOf q h) (a0Q q h) - (13 : ℝ) / 2 ≤ 0 := by
        linarith
      have hmul := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hscale) hle
      exact (not_lt_of_ge hmul) hN
    exact hboundary.trans_le hmono

private def dCap (s : ℝ) : ℝ :=
  s * (s - 1) / (s + 1)

private def pOne (s d : ℝ) : ℝ :=
  -8 * d ^ 2 * s + 8 * d ^ 2 - 8 * d * s ^ 2 +
    83 * d * s - 75 * d + 10 * s ^ 2 - 75 * s

private def pOneD (s d : ℝ) : ℝ :=
  -(s - 1) * (16 * d + 8 * s - 75)

private def phiOne (s d : ℝ) : ℝ :=
  1 + s + d + (9 / 8) * (1 / d)

private lemma pOne_le_of_le
    {s d r : ℝ} (hs : 1 < s) (hdr : d ≤ r)
    (hder : 0 < pOneD s r) :
    pOne s d ≤ pOne s r := by
  have hA : -8 * (s - 1) < 0 := by linarith
  have hbonus : 0 ≤ (-8 * (s - 1)) * (d - r) :=
    mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA) (by linarith)
  have hbracket : 0 < pOneD s r + (-8 * (s - 1)) * (d - r) := by
    linarith
  have hid :
      pOne s d - pOne s r =
        (d - r) * (pOneD s r + (-8 * (s - 1)) * (d - r)) := by
    simp [pOne, pOneD]
    ring
  have hmul :
      (d - r) * (pOneD s r + (-8 * (s - 1)) * (d - r)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hbracket)
  linarith

private lemma pOneD_pos_of_upper
    {s r : ℝ} (hs : 1 < s) (hs7 : s < (7 : ℝ) / 2)
    (hr2 : r < 2) :
    0 < pOneD s r := by
  have hinner : 16 * r + 8 * s - 75 < 0 := by linarith
  have hp := mul_pos (sub_pos.mpr hs) (neg_pos.mpr hinner)
  dsimp [pOneD]
  nlinarith

private lemma phiOne_mono
    {s d r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hrd : r ≤ d) (hprod : (9 : ℝ) / 8 ≤ d * r) :
    phiOne s r ≤ phiOne s d := by
  have hden : 0 < 8 * d * r := by positivity
  have hnum : 0 ≤ (d - r) * (8 * d * r - 9) :=
    mul_nonneg (sub_nonneg.mpr hrd) (by linarith)
  have hid :
      phiOne s d - phiOne s r =
        ((d - r) * (8 * d * r - 9)) / (8 * d * r) := by
    dsimp [phiOne]
    field_simp [ne_of_gt hd, ne_of_gt hr]
    ring
  have hdiff : 0 ≤ phiOne s d - phiOne s r := by
    rw [hid]
    exact div_nonneg hnum (le_of_lt hden)
  exact sub_nonneg.mp hdiff

private def smallF (s : ℝ) : ℝ :=
  16 * s ^ 3 - 117 * s ^ 2 + 146 * s + 215

private lemma smallF_pos
    {s : ℝ} (hs0 : 3 ≤ s) (hs1 : s ≤ (327 : ℝ) / 100) :
    0 < smallF s := by
  let t : ℝ := (100 * s - 300) / 27
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hpos := bernsteinThree_pos ht0 ht1
    (show (0 : ℝ) < 32 by norm_num)
    (show (0 : ℝ) ≤ 521 / 25 by norm_num)
    (show (0 : ℝ) ≤ 103361 / 10000 by norm_num)
    (show (0 : ℝ) < 200807 / 250000 by norm_num)
  have hid :
      smallF s = bernsteinThree t
        32 (521 / 25) (103361 / 10000) (200807 / 250000) := by
    dsimp [smallF, t, bernsteinThree]
    ring
  rw [hid]
  exact hpos

private def bandQ1 (s : ℝ) : ℝ :=
  180 * s ^ 2 - 2149 * s + 5219

private lemma bandQ1_pos
    {s : ℝ}
    (hs0 : (327 : ℝ) / 100 ≤ s)
    (hs1 : s ≤ (339 : ℝ) / 100) :
    0 < bandQ1 s := by
  let t : ℝ := (100 * s - 327) / 12
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hpos := bernsteinTwo_pos ht0 ht1
    (show (0 : ℝ) < 29123 / 250 by norm_num)
    (show (0 : ℝ) ≤ 7273 / 125 by norm_num)
    (show (0 : ℝ) < 617 / 250 by norm_num)
  have hid :
      bandQ1 s = bernsteinTwo t
        (29123 / 250) (7273 / 125) (617 / 250) := by
    dsimp [bandQ1, t, bernsteinTwo]
    ring
  rw [hid]
  exact hpos

private def bandQ2 (s : ℝ) : ℝ :=
  70 * s ^ 2 - 933 * s + 2488

private lemma bandQ2_pos
    {s : ℝ}
    (hs0 : (339 : ℝ) / 100 ≤ s)
    (hs1 : s ≤ (7 : ℝ) / 2) :
    0 < bandQ2 s := by
  let t : ℝ := (100 * s - 339) / 11
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hpos := bernsteinTwo_pos ht0 ht1
    (show (0 : ℝ) < 129577 / 1000 by norm_num)
    (show (0 : ℝ) ≤ 20873 / 200 by norm_num)
    (show (0 : ℝ) < 80 by norm_num)
  have hid :
      bandQ2 s = bernsteinTwo t
        (129577 / 1000) (20873 / 200) 80 := by
    dsimp [bandQ2, t, bernsteinTwo]
    ring
  rw [hid]
  exact hpos

/-- Low-`U` estimate when the maximizing lower endpoint is `a = 1`. -/
theorem low_phi_one
    {s d : ℝ}
    (hs : 1 < s) (hd : s / (s - 1) < d)
    (ha0 : a0S s d ≤ 1)
    (hM : 1 ≤ MS 1 s d)
    (hR : 0 ≤ TS s d + 5 * kS s d * MS 1 s d - 5) :
    (53 : ℝ) / 8 ≤ 1 + s + d + (9 / 8) * (1 / d) := by
  have hspos : 0 < s := lt_trans zero_lt_one hs
  have hs1pos : 0 < s - 1 := sub_pos.mpr hs
  have hlowerPos : 0 < s / (s - 1) := div_pos hspos hs1pos
  have hdpos : 0 < d := lt_trans hlowerPos hd
  have hsp1 : 0 < s + 1 := by linarith
  have hAId :
      (a0S s d - 1) * s ^ 2 = (s + 1) * d - s * (s - 1) := by
    dsimp [a0S]
    field_simp [ne_of_gt hspos]
    ring
  have hAprod : (a0S s d - 1) * s ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg s)
  rw [hAId] at hAprod
  have hdCap : d ≤ dCap s := by
    dsimp [dCap]
    exact (le_div_iff₀ hsp1).2 (by linarith)
  have hcompare : s / (s - 1) < dCap s := hd.trans_le hdCap
  have hcross : s * (s + 1) < (s * (s - 1)) * (s - 1) := by
    dsimp [dCap] at hcompare
    exact (div_lt_div_iff₀ hs1pos hsp1).1 hcompare
  have hsquare : s + 1 < (s - 1) ^ 2 := by
    have hcross' : s * (s + 1) < s * ((s - 1) ^ 2) := by
      simpa [pow_two, mul_assoc] using hcross
    by_contra hnot
    have hle : (s - 1) ^ 2 ≤ s + 1 := le_of_not_gt hnot
    have hmul : s * ((s - 1) ^ 2) ≤ s * (s + 1) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hspos)
    exact (not_lt_of_ge hmul) hcross'
  have hs3 : 3 < s := by nlinarith
  have hRId :
      TS s d + 5 * kS s d * MS 1 s d - 5 =
        pOne s d / (2 * d * s) := by
    dsimp [TS, kS, MS, pOne]
    field_simp [ne_of_gt hspos, ne_of_gt hdpos]
    ring
  rw [hRId] at hR
  have hRden : 0 < 2 * d * s := by positivity
  have hPnonneg : 0 ≤ pOne s d := by
    have hmul := mul_nonneg hR (le_of_lt hRden)
    have hidMul : (pOne s d / (2 * d * s)) * (2 * d * s) = pOne s d := by
      field_simp [ne_of_gt hRden]
    rwa [hidMul] at hmul
  have hs327 : (327 : ℝ) / 100 < s := by
    by_contra hnot
    have hsle : s ≤ (327 : ℝ) / 100 := le_of_not_gt hnot
    have hF : 0 < smallF s := smallF_pos (le_of_lt hs3) hsle
    have hs7 : s < (7 : ℝ) / 2 := by linarith
    have hsSq : s ^ 2 < ((7 : ℝ) / 2) * s := by
      simpa [pow_two] using mul_lt_mul_of_pos_right hs7 hspos
    have hcap2 : dCap s < 2 := by
      dsimp [dCap]
      apply (div_lt_iff₀ hsp1).2
      nlinarith
    have hder : 0 < pOneD s (dCap s) :=
      pOneD_pos_of_upper hs hs7 hcap2
    have hPcap : pOne s (dCap s) < 0 := by
      have hid :
          pOne s (dCap s) =
            -(s ^ 2 * smallF s) / (s + 1) ^ 2 := by
        dsimp [pOne, dCap, smallF]
        field_simp [ne_of_gt hsp1]
        ring
      rw [hid]
      exact div_neg_of_neg_of_pos
        (neg_neg_of_pos (mul_pos (sq_pos_of_pos hspos) hF))
        (sq_pos_of_pos hsp1)
    have hPle : pOne s d ≤ pOne s (dCap s) :=
      pOne_le_of_le hs hdCap hder
    linarith
  by_cases hs7 : s < (7 : ℝ) / 2
  · by_cases hs339 : s ≤ (339 : ℝ) / 100
    · have hQ : 0 < bandQ1 s := bandQ1_pos (le_of_lt hs327) hs339
      have hPfix : pOne s ((17 : ℝ) / 10) < 0 := by
        have hid : pOne s ((17 : ℝ) / 10) = -bandQ1 s / 50 := by
          dsimp [pOne, bandQ1]
          ring
        rw [hid]
        exact div_neg_of_neg_of_pos (neg_neg_of_pos hQ) (by norm_num)
      have hder : 0 < pOneD s ((17 : ℝ) / 10) :=
        pOneD_pos_of_upper hs hs7 (by norm_num)
      have hd17 : (17 : ℝ) / 10 < d := by
        by_contra hnot
        have hle : d ≤ (17 : ℝ) / 10 := le_of_not_gt hnot
        have := pOne_le_of_le hs hle hder
        linarith
      have hprod : (9 : ℝ) / 8 ≤ d * ((17 : ℝ) / 10) := by
        nlinarith [mul_pos (sub_pos.mpr hd17) (by norm_num : (0 : ℝ) < 17 / 10)]
      have hmono := phiOne_mono (s := s) hdpos
        (by norm_num : (0 : ℝ) < 17 / 10)
        (le_of_lt hd17) hprod
      have hbase : (53 : ℝ) / 8 <
          phiOne ((327 : ℝ) / 100) ((17 : ℝ) / 10) := by
        norm_num [phiOne]
      have hsmono :
          phiOne ((327 : ℝ) / 100) ((17 : ℝ) / 10) <
            phiOne s ((17 : ℝ) / 10) := by
        dsimp [phiOne]
        linarith
      exact le_of_lt (hbase.trans (hsmono.trans_le hmono))
    · have hs339' : (339 : ℝ) / 100 < s := lt_of_not_ge hs339
      have hQ : 0 < bandQ2 s :=
        bandQ2_pos (le_of_lt hs339') (le_of_lt hs7)
      have hPfix : pOne s ((8 : ℝ) / 5) < 0 := by
        have hid : pOne s ((8 : ℝ) / 5) = -bandQ2 s / 25 := by
          dsimp [pOne, bandQ2]
          ring
        rw [hid]
        exact div_neg_of_neg_of_pos (neg_neg_of_pos hQ) (by norm_num)
      have hder : 0 < pOneD s ((8 : ℝ) / 5) :=
        pOneD_pos_of_upper hs hs7 (by norm_num)
      have hd8 : (8 : ℝ) / 5 < d := by
        by_contra hnot
        have hle : d ≤ (8 : ℝ) / 5 := le_of_not_gt hnot
        have := pOne_le_of_le hs hle hder
        linarith
      have hprod : (9 : ℝ) / 8 ≤ d * ((8 : ℝ) / 5) := by
        nlinarith [mul_pos (sub_pos.mpr hd8) (by norm_num : (0 : ℝ) < 8 / 5)]
      have hmono := phiOne_mono (s := s) hdpos
        (by norm_num : (0 : ℝ) < 8 / 5)
        (le_of_lt hd8) hprod
      have hbase : (53 : ℝ) / 8 <
          phiOne ((339 : ℝ) / 100) ((8 : ℝ) / 5) := by
        norm_num [phiOne]
      have hsmono :
          phiOne ((339 : ℝ) / 100) ((8 : ℝ) / 5) <
            phiOne s ((8 : ℝ) / 5) := by
        dsimp [phiOne]
        linarith
      exact le_of_lt (hbase.trans (hsmono.trans_le hmono))
  · have hs7' : (7 : ℝ) / 2 ≤ s := le_of_not_gt hs7
    have hsum : s + d ≤ (13 : ℝ) / 2 := by
      dsimp [MS] at hM
      linarith
    have hd1 : 1 < d := by
      have hlower1 : 1 < s / (s - 1) := by
        apply (lt_div_iff₀ hs1pos).2
        linarith
      exact hlower1.trans hd
    have hs6 : s < 6 := by linarith
    let r : ℝ := s / (s - 1)
    have hrpos : 0 < r := by dsimp [r]; positivity
    have hr6 : (6 : ℝ) / 5 < r := by
      dsimp [r]
      apply (lt_div_iff₀ hs1pos).2
      linarith
    have hdr : r < d := by simpa [r] using hd
    have hprod : (9 : ℝ) / 8 ≤ d * r := by
      have hp0 : ((6 : ℝ) / 5) ^ 2 < ((6 : ℝ) / 5) * r := by
        nlinarith [mul_pos (by norm_num : (0 : ℝ) < 6 / 5)
          (sub_pos.mpr hr6)]
      have hp1 : ((6 : ℝ) / 5) * r < d * r :=
        mul_lt_mul_of_pos_right (hr6.trans hdr) hrpos
      have hp : ((6 : ℝ) / 5) ^ 2 < d * r := hp0.trans hp1
      nlinarith
    have hmono := phiOne_mono (s := s) hdpos hrpos (le_of_lt hdr) hprod
    have hquad : 0 < 140 * s ^ 2 - 151 * s - 45 := by
      have hsSq : ((7 : ℝ) / 2) * s ≤ s ^ 2 := by
        simpa [pow_two] using mul_le_mul_of_nonneg_right hs7' (le_of_lt hspos)
      nlinarith
    have hbase : (53 : ℝ) / 8 < phiOne s r := by
      have hid :
          phiOne s r - (53 : ℝ) / 8 =
            (2 * s - 7) * (140 * s ^ 2 - 151 * s - 45) /
                (280 * s * (s - 1)) + 11 / 140 := by
        dsimp [phiOne, r]
        field_simp [ne_of_gt hspos, ne_of_gt hs1pos]
        ring
      have hdiff : 0 < phiOne s r - (53 : ℝ) / 8 := by
        rw [hid]
        have hleft : 0 ≤ 2 * s - 7 := by linarith
        have hdenpos : 0 < 280 * s * (s - 1) := by positivity
        have hfirst : 0 ≤
            (2 * s - 7) * (140 * s ^ 2 - 151 * s - 45) /
              (280 * s * (s - 1)) :=
          div_nonneg (mul_nonneg hleft (le_of_lt hquad)) (le_of_lt hdenpos)
        linarith
      linarith
    exact le_of_lt (hbase.trans_le hmono)

private noncomputable def coneThree
    (u v c0 c1 c2 c3 : ℝ) : ℝ :=
  c0 * v ^ 3 + c1 * u * v ^ 2 + c2 * u ^ 2 * v + c3 * u ^ 3

private noncomputable def coneFour
    (u v c0 c1 c2 c3 c4 : ℝ) : ℝ :=
  c0 * v ^ 4 + c1 * u * v ^ 3 + c2 * u ^ 2 * v ^ 2 +
    c3 * u ^ 3 * v + c4 * u ^ 4

private lemma coneThree_pos
    {u v c0 c1 c2 c3 : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : 0 < u + v)
    (hc0 : 0 < c0) (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) (hc3 : 0 < c3) :
    0 < coneThree u v c0 c1 c2 c3 := by
  by_cases hz : u = 0
  · subst u
    have hvpos : 0 < v := by simpa using huv
    dsimp [coneThree]
    positivity
  · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    dsimp [coneThree]
    positivity

private lemma coneFour_pos
    {u v c0 c1 c2 c3 c4 : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : 0 < u + v)
    (hc0 : 0 < c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hc3 : 0 ≤ c3) (hc4 : 0 < c4) :
    0 < coneFour u v c0 c1 c2 c3 c4 := by
  by_cases hz : u = 0
  · subst u
    have hvpos : 0 < v := by simpa using huv
    dsimp [coneFour]
    positivity
  · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    dsimp [coneFour]
    positivity

private lemma positive_of_scaled_positive
    {scale x : ℝ} (hs : 0 < scale) (hx : 0 < scale * x) :
    0 < x := by
  by_contra hnot
  have hxle : x ≤ 0 := le_of_not_gt hnot
  have hmul := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs) hxle
  exact (not_lt_of_ge hmul) hx

private def pA (s d : ℝ) : ℝ :=
  -8 * d ^ 2 * s ^ 3 - 2 * d ^ 2 * s ^ 2 + 10 * d ^ 2 -
    8 * d * s ^ 4 + 93 * d * s ^ 3 - 85 * d * s ^ 2 +
    20 * d * s + 10 * s ^ 4 - 85 * s ^ 3 + 10 * s ^ 2

private def pAD (s d : ℝ) : ℝ :=
  -16 * d * s ^ 3 - 4 * d * s ^ 2 + 20 * d -
    8 * s ^ 4 + 93 * s ^ 3 - 85 * s ^ 2 + 20 * s

private def nA (s d : ℝ) : ℝ :=
  8 * d ^ 2 * s ^ 2 + 8 * d ^ 2 * s + 8 * d ^ 2 +
    8 * d * s ^ 3 - 53 * d * s ^ 2 + 17 * d * s +
    9 * d + 9 * s

private def phiA (s d : ℝ) : ℝ :=
  a0S s d + s + d + (9 / 8) * (a0S s d / d)

private lemma pA_le_of_le
    {s d r : ℝ} (hs : 1 < s) (hdr : d ≤ r)
    (hder : 0 < pAD s r) :
    pA s d ≤ pA s r := by
  let A : ℝ := -8 * s ^ 3 - 2 * s ^ 2 + 10
  have hAId : A = -2 * (s - 1) * (4 * s ^ 2 + 5 * s + 5) := by
    dsimp [A]
    ring
  have hquad : 0 < 4 * s ^ 2 + 5 * s + 5 := by
    nlinarith [sq_nonneg s]
  have hA : A < 0 := by
    rw [hAId]
    have hsSub : 0 < s - 1 := by linarith
    have hprod : 0 < (s - 1) * (4 * s ^ 2 + 5 * s + 5) :=
      mul_pos hsSub hquad
    nlinarith
  have hbonus : 0 ≤ A * (d - r) :=
    mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA) (by linarith)
  have hbracket : 0 < pAD s r + A * (d - r) := by linarith
  have hid :
      pA s d - pA s r =
        (d - r) * (pAD s r + A * (d - r)) := by
    dsimp [pA, pAD, A]
    ring
  have hmul : (d - r) * (pAD s r + A * (d - r)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hbracket)
  linarith

private lemma phiA_lt_of_lt
    {s d r : ℝ} (hs : 1 < s) (hd1 : 1 < d)
    (hr : (3 : ℝ) / 8 < r) (hrd : r < d) :
    phiA s r < phiA s d := by
  have hspos : 0 < s := lt_trans zero_lt_one hs
  have hdpos : 0 < d := lt_trans zero_lt_one hd1
  have hrpos : 0 < r := lt_trans (by norm_num) hr
  let P : ℝ := s ^ 2 + s + 1
  have hP : 0 < P := by dsimp [P]; nlinarith [sq_nonneg s]
  have hP3 : 3 * s ≤ P := by
    dsimp [P]
    nlinarith [sq_nonneg (s - 1)]
  have hdrBase : r < d * r := by
    have := mul_lt_mul_of_pos_right hd1 hrpos
    simpa using this
  have hdr38 : (3 : ℝ) / 8 < d * r := hr.trans hdrBase
  have hfirst : 0 < (d * r - (3 : ℝ) / 8) * P := by positivity
  have hsecond : 0 ≤ ((3 : ℝ) / 8) * (P - 3 * s) := by positivity
  have hcoef : 0 < 8 * d * r * P - 9 * s := by nlinarith
  have hden : 0 < 8 * d * r * s ^ 2 := by positivity
  have hid :
      phiA s d - phiA s r =
        (d - r) * (8 * d * r * (s ^ 2 + s + 1) - 9 * s) /
          (8 * d * r * s ^ 2) := by
    dsimp [phiA, a0S]
    field_simp [ne_of_gt hspos, ne_of_gt hdpos, ne_of_gt hrpos]
    ring
  have hdiff : 0 < phiA s d - phiA s r := by
    rw [hid]
    exact div_pos
      (mul_pos (sub_pos.mpr hrd) (by simpa [P] using hcoef)) hden
  linarith

private lemma phiA_gt_of_nA_pos
    {s d : ℝ} (hs : 0 < s) (hd : 0 < d) (hN : 0 < nA s d) :
    (53 : ℝ) / 8 < phiA s d := by
  have hid :
      phiA s d - (53 : ℝ) / 8 = nA s d / (8 * d * s ^ 2) := by
    dsimp [phiA, a0S, nA]
    field_simp [ne_of_gt hs, ne_of_gt hd]
    ring
  have hdiff : 0 < phiA s d - (53 : ℝ) / 8 := by
    rw [hid]
    positivity
  linarith

private lemma pA_band1
    {s : ℝ} (hs0 : 1 ≤ s) (hs1 : s ≤ (14 : ℝ) / 5) :
    pA s 2 < 0 ∧ 0 < pAD s 2 := by
  let u : ℝ := s - 1
  let v : ℝ := (14 : ℝ) / 5 - s
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have huv : 0 < u + v := by dsimp [u, v]; norm_num
  have hpCone := coneFour_pos hu hv huv
    (show (0 : ℝ) < 15625 by norm_num)
    (show (0 : ℝ) ≤ 189625 by norm_num)
    (show (0 : ℝ) ≤ 469050 by norm_num)
    (show (0 : ℝ) ≤ 267700 by norm_num)
    (show (0 : ℝ) < 12016 by norm_num)
  have hpId :
      (6561 : ℝ) * (-pA s 2) =
        coneFour u v 15625 189625 469050 267700 12016 := by
    dsimp [pA, coneFour, u, v]
    ring
  rw [← hpId] at hpCone
  have hpNeg : pA s 2 < 0 := by
    have := positive_of_scaled_positive (show (0 : ℝ) < 6561 by norm_num) hpCone
    linarith
  have hdCone := coneFour_pos hu hv huv
    (show (0 : ℝ) < 12500 by norm_num)
    (show (0 : ℝ) ≤ 33125 by norm_num)
    (show (0 : ℝ) ≤ 109425 by norm_num)
    (show (0 : ℝ) ≤ 275180 by norm_num)
    (show (0 : ℝ) < 133892 by norm_num)
  have hdId :
      (6561 : ℝ) * pAD s 2 =
        coneFour u v 12500 33125 109425 275180 133892 := by
    dsimp [pAD, coneFour, u, v]
    ring
  rw [← hdId] at hdCone
  exact ⟨hpNeg, positive_of_scaled_positive (by norm_num) hdCone⟩

private lemma pA_band2
    {s : ℝ} (hs0 : (14 : ℝ) / 5 ≤ s) (hs1 : s ≤ 3) :
    pA s ((19 : ℝ) / 10) < 0 ∧ 0 < pAD s ((19 : ℝ) / 10) := by
  let u : ℝ := s - (14 : ℝ) / 5
  let v : ℝ := 3 - s
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have huv : 0 < u + v := by dsimp [u, v]; norm_num
  have hpCone := coneFour_pos hu hv huv
    (show (0 : ℝ) < 265383 by norm_num)
    (show (0 : ℝ) ≤ 848916 by norm_num)
    (show (0 : ℝ) ≤ 923360 by norm_num)
    (show (0 : ℝ) ≤ 361275 by norm_num)
    (show (0 : ℝ) < 21500 by norm_num)
  have hpId :
      (10 : ℝ) * (-pA s ((19 : ℝ) / 10)) =
        coneFour u v 265383 848916 923360 361275 21500 := by
    dsimp [pA, coneFour, u, v]
    ring
  rw [← hpId] at hpCone
  have hpNeg : pA s ((19 : ℝ) / 10) < 0 := by
    have := positive_of_scaled_positive (show (0 : ℝ) < 10 by norm_num) hpCone
    linarith
  have hdCone := coneFour_pos hu hv huv
    (show (0 : ℝ) < 156554 by norm_num)
    (show (0 : ℝ) ≤ 660132 by norm_num)
    (show (0 : ℝ) ≤ 1042495 by norm_num)
    (show (0 : ℝ) ≤ 730675 by norm_num)
    (show (0 : ℝ) < 191750 by norm_num)
  have hdId :
      pAD s ((19 : ℝ) / 10) =
        coneFour u v 156554 660132 1042495 730675 191750 := by
    dsimp [pAD, coneFour, u, v]
    ring
  rw [hdId]
  exact ⟨hpNeg, hdCone⟩

private lemma pA_band3
    {s : ℝ} (hs0 : 3 ≤ s) (hs1 : s ≤ (79 : ℝ) / 25) :
    pA s ((9 : ℝ) / 5) < 0 ∧ 0 < pAD s ((9 : ℝ) / 5) := by
  let u : ℝ := s - 3
  let v : ℝ := (79 : ℝ) / 25 - s
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have huv : 0 < u + v := by dsimp [u, v]; norm_num
  have hpCone := coneFour_pos hu hv huv
    (show (0 : ℝ) < 71015625 by norm_num)
    (show (0 : ℝ) ≤ 225037500 by norm_num)
    (show (0 : ℝ) ≤ 242956750 by norm_num)
    (show (0 : ℝ) ≤ 94834060 by norm_num)
    (show (0 : ℝ) < 5904817 by norm_num)
  have hpId :
      (1280 : ℝ) * (-pA s ((9 : ℝ) / 5)) =
        coneFour u v 71015625 225037500 242956750 94834060 5904817 := by
    dsimp [pA, coneFour, u, v]
    ring
  rw [← hpId] at hpCone
  have hpNeg : pA s ((9 : ℝ) / 5) < 0 := by
    have := positive_of_scaled_positive (show (0 : ℝ) < 1280 by norm_num) hpCone
    linarith
  have hdCone := coneFour_pos hu hv huv
    (show (0 : ℝ) < 68671875 by norm_num)
    (show (0 : ℝ) ≤ 285193750 by norm_num)
    (show (0 : ℝ) ≤ 443818000 by norm_num)
    (show (0 : ℝ) ≤ 306716810 by norm_num)
    (show (0 : ℝ) < 79419661 by norm_num)
  have hdId :
      (128 : ℝ) * pAD s ((9 : ℝ) / 5) =
        coneFour u v 68671875 285193750 443818000 306716810 79419661 := by
    dsimp [pAD, coneFour, u, v]
    ring
  rw [← hdId] at hdCone
  exact ⟨hpNeg, positive_of_scaled_positive (by norm_num) hdCone⟩

private lemma pA_band4
    {s : ℝ}
    (hs0 : (79 : ℝ) / 25 ≤ s)
    (hs1 : s ≤ (163 : ℝ) / 50) :
    pA s ((7 : ℝ) / 4) < 0 ∧ 0 < pAD s ((7 : ℝ) / 4) := by
  let u : ℝ := s - (79 : ℝ) / 25
  let v : ℝ := (163 : ℝ) / 50 - s
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have huv : 0 < u + v := by dsimp [u, v]; norm_num
  have hpCone := coneFour_pos hu hv huv
    (show (0 : ℝ) < 300133968 by norm_num)
    (show (0 : ℝ) ≤ 938388792 by norm_num)
    (show (0 : ℝ) ≤ 999327493 by norm_num)
    (show (0 : ℝ) ≤ 383990857 by norm_num)
    (show (0 : ℝ) < 22923188 by norm_num)
  have hpId :
      (1250 : ℝ) * (-pA s ((7 : ℝ) / 4)) =
        coneFour u v 300133968 938388792 999327493 383990857 22923188 := by
    dsimp [pA, coneFour, u, v]
    ring
  rw [← hpId] at hpCone
  have hpNeg : pA s ((7 : ℝ) / 4) < 0 := by
    have := positive_of_scaled_positive (show (0 : ℝ) < 1250 by norm_num) hpCone
    linarith
  have hdCone := coneFour_pos hu hv huv
    (show (0 : ℝ) < 1352716816 by norm_num)
    (show (0 : ℝ) ≤ 5528369804 by norm_num)
    (show (0 : ℝ) ≤ 8470211366 by norm_num)
    (show (0 : ℝ) ≤ 5766067709 by norm_num)
    (show (0 : ℝ) < 1471506831 by norm_num)
  have hdId :
      ((625 : ℝ) / 2) * pAD s ((7 : ℝ) / 4) =
        coneFour u v
          1352716816 5528369804 8470211366 5766067709 1471506831 := by
    dsimp [pAD, coneFour, u, v]
    ring
  rw [← hdId] at hdCone
  exact ⟨hpNeg, positive_of_scaled_positive (by norm_num) hdCone⟩

private lemma nA_band1_pos
    {s : ℝ} (hs0 : 1 ≤ s) (hs1 : s ≤ (14 : ℝ) / 5) :
    0 < nA s 2 := by
  let u : ℝ := s - 1
  let v : ℝ := (14 : ℝ) / 5 - s
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have huv : 0 < u + v := by dsimp [u, v]; norm_num
  have hcone := coneThree_pos hu hv huv
    (show (0 : ℝ) < 8375 by norm_num)
    (show (0 : ℝ) ≤ 19500 by norm_num)
    (show (0 : ℝ) ≤ 3345 by norm_num)
    (show (0 : ℝ) < 3884 by norm_num)
  have hid :
      (729 : ℝ) * nA s 2 =
        coneThree u v 8375 19500 3345 3884 := by
    dsimp [nA, coneThree, u, v]
    ring
  rw [← hid] at hcone
  exact positive_of_scaled_positive (by norm_num) hcone

private lemma nA_band2_pos
    {s : ℝ} (hs : (14 : ℝ) / 5 ≤ s) :
    0 < nA s ((19 : ℝ) / 10) := by
  let u : ℝ := s - (14 : ℝ) / 5
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hpoly :
      0 < 760 * u ^ 3 + 2793 * u ^ 2 +
        ((6373 : ℝ) / 5) * u + (16357 : ℝ) / 25 := by
    positivity
  have hid :
      nA s ((19 : ℝ) / 10) =
        (1 / 50) *
          (760 * u ^ 3 + 2793 * u ^ 2 +
            ((6373 : ℝ) / 5) * u + (16357 : ℝ) / 25) := by
    dsimp [nA, u]
    ring
  rw [hid]
  positivity

private lemma nA_band3_pos
    {s : ℝ} (hs : 3 ≤ s) :
    0 < nA s ((9 : ℝ) / 5) := by
  let u : ℝ := s - 3
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hpoly :
      0 < 40 * u ^ 3 + 167 * u ^ 2 + 104 * u + 6 := by
    positivity
  have hid :
      nA s ((9 : ℝ) / 5) =
        (9 / 25) * (40 * u ^ 3 + 167 * u ^ 2 + 104 * u + 6) := by
    dsimp [nA, u]
    ring
  rw [hid]
  positivity

private lemma nA_band4_pos
    {s : ℝ} (hs : (79 : ℝ) / 25 ≤ s) :
    0 < nA s ((7 : ℝ) / 4) := by
  let u : ℝ := s - (79 : ℝ) / 25
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hpoly :
      0 < 56 * u ^ 3 + ((6447 : ℝ) / 25) * u ^ 2 +
        ((128263 : ℝ) / 625) * u + (22859 : ℝ) / 15625 := by
    positivity
  have hid :
      nA s ((7 : ℝ) / 4) =
        (1 / 4) *
          (56 * u ^ 3 + ((6447 : ℝ) / 25) * u ^ 2 +
            ((128263 : ℝ) / 625) * u + (22859 : ℝ) / 15625) := by
    dsimp [nA, u]
    ring
  rw [hid]
  positivity

private def qHigh (s : ℝ) : ℝ :=
  16 * s ^ 4 - 61 * s ^ 3 + 9 * s ^ 2 + 63 * s + 9

private lemma qHigh_pos
    {s : ℝ} (hs : (163 : ℝ) / 50 ≤ s) :
    0 < qHigh s := by
  let u : ℝ := s - (163 : ℝ) / 50
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hpoly :
      0 < 16 * u ^ 4 + ((3691 : ℝ) / 25) * u ^ 3 +
        ((540837 : ℝ) / 1250) * u ^ 2 +
        ((24635729 : ℝ) / 62500) * u +
        (11743663 : ℝ) / 3125000 := by
    positivity
  have hid :
      qHigh s =
        16 * u ^ 4 + ((3691 : ℝ) / 25) * u ^ 3 +
          ((540837 : ℝ) / 1250) * u ^ 2 +
          ((24635729 : ℝ) / 62500) * u +
          (11743663 : ℝ) / 3125000 := by
    dsimp [qHigh, u]
    ring
  rw [hid]
  exact hpoly

/-- Low-`U` estimate when the maximizing lower endpoint is `a = a0S s d`. -/
theorem low_phi_a0
    {s d : ℝ}
    (hs : 1 < s) (hd : s / (s - 1) < d)
    (ha0 : 1 < a0S s d)
    (hM : 1 ≤ MS (a0S s d) s d)
    (hR : 0 ≤
      TS s d + 5 * kS s d * MS (a0S s d) s d - 5) :
    (53 : ℝ) / 8 ≤
      a0S s d + s + d + (9 / 8) * (a0S s d / d) := by
  change (53 : ℝ) / 8 ≤ phiA s d
  have hspos : 0 < s := lt_trans zero_lt_one hs
  have hs1pos : 0 < s - 1 := sub_pos.mpr hs
  have hlowerPos : 0 < s / (s - 1) := div_pos hspos hs1pos
  have hdpos : 0 < d := lt_trans hlowerPos hd
  have hd1 : 1 < d := by
    have hlowerOne : 1 < s / (s - 1) := by
      apply (lt_div_iff₀ hs1pos).2
      linarith
    exact hlowerOne.trans hd
  have hsp1 : 0 < s + 1 := by linarith
  have hRId :
      TS s d + 5 * kS s d * MS (a0S s d) s d - 5 =
        pA s d / (2 * d * s ^ 3) := by
    dsimp [TS, kS, MS, a0S, pA]
    field_simp [ne_of_gt hspos, ne_of_gt hdpos]
    ring
  rw [hRId] at hR
  have hRden : 0 < 2 * d * s ^ 3 := by positivity
  have hPnonneg : 0 ≤ pA s d := by
    have hmul := mul_nonneg hR (le_of_lt hRden)
    have hidMul :
        (pA s d / (2 * d * s ^ 3)) * (2 * d * s ^ 3) = pA s d := by
      field_simp [ne_of_gt hRden]
    rwa [hidMul] at hmul
  have hAId :
      (a0S s d - 1) * s ^ 2 = (s + 1) * d - s * (s - 1) := by
    dsimp [a0S]
    field_simp [ne_of_gt hspos]
    ring
  have hAprod : 0 < (a0S s d - 1) * s ^ 2 :=
    mul_pos (sub_pos.mpr ha0) (sq_pos_of_pos hspos)
  rw [hAId] at hAprod
  have hdCap : dCap s < d := by
    dsimp [dCap]
    exact (div_lt_iff₀ hsp1).2 (by linarith)
  by_cases hsHigh : (163 : ℝ) / 50 ≤ s
  · have hQ : 0 < qHigh s := qHigh_pos hsHigh
    have hsSq : ((163 : ℝ) / 50) * s ≤ s ^ 2 := by
      simpa [pow_two] using
        mul_le_mul_of_nonneg_right hsHigh (le_of_lt hspos)
    have hcap38 : (3 : ℝ) / 8 < dCap s := by
      dsimp [dCap]
      apply (lt_div_iff₀ hsp1).2
      nlinarith
    have hden : 0 < 8 * s * (s - 1) * (s + 1) := by positivity
    have hphiCap : (53 : ℝ) / 8 < phiA s (dCap s) := by
      have hid :
          phiA s (dCap s) - (53 : ℝ) / 8 =
            qHigh s / (8 * s * (s - 1) * (s + 1)) := by
        dsimp [phiA, a0S, dCap, qHigh]
        field_simp [ne_of_gt hspos, ne_of_gt hs1pos, ne_of_gt hsp1]
        ring
      have hdiff : 0 < phiA s (dCap s) - (53 : ℝ) / 8 := by
        rw [hid]
        exact div_pos hQ hden
      linarith
    have hmono : phiA s (dCap s) < phiA s d :=
      phiA_lt_of_lt hs hd1 hcap38 hdCap
    exact le_of_lt (hphiCap.trans hmono)
  · have hsUpper : s < (163 : ℝ) / 50 := lt_of_not_ge hsHigh
    by_cases hs14 : s ≤ (14 : ℝ) / 5
    · have hband := pA_band1 (le_of_lt hs) hs14
      have hd2 : (2 : ℝ) < d := by
        by_contra hnot
        have hle : d ≤ (2 : ℝ) := le_of_not_gt hnot
        have hPle : pA s d ≤ pA s 2 :=
          pA_le_of_le hs hle hband.2
        exact (not_lt_of_ge hPnonneg) (hPle.trans_lt hband.1)
      have hN : 0 < nA s 2 := nA_band1_pos (le_of_lt hs) hs14
      have hbase : (53 : ℝ) / 8 < phiA s 2 :=
        phiA_gt_of_nA_pos hspos (by norm_num) hN
      have hmono : phiA s 2 < phiA s d :=
        phiA_lt_of_lt hs hd1 (by norm_num) hd2
      exact le_of_lt (hbase.trans hmono)
    · have hs14' : (14 : ℝ) / 5 < s := lt_of_not_ge hs14
      by_cases hs3 : s ≤ 3
      · have hband := pA_band2 (le_of_lt hs14') hs3
        have hd19 : (19 : ℝ) / 10 < d := by
          by_contra hnot
          have hle : d ≤ (19 : ℝ) / 10 := le_of_not_gt hnot
          have hPle : pA s d ≤ pA s ((19 : ℝ) / 10) :=
            pA_le_of_le hs hle hband.2
          exact (not_lt_of_ge hPnonneg) (hPle.trans_lt hband.1)
        have hN : 0 < nA s ((19 : ℝ) / 10) :=
          nA_band2_pos (le_of_lt hs14')
        have hbase : (53 : ℝ) / 8 < phiA s ((19 : ℝ) / 10) :=
          phiA_gt_of_nA_pos hspos (by norm_num) hN
        have hmono : phiA s ((19 : ℝ) / 10) < phiA s d :=
          phiA_lt_of_lt hs hd1 (by norm_num) hd19
        exact le_of_lt (hbase.trans hmono)
      · have hs3' : 3 < s := lt_of_not_ge hs3
        by_cases hs79 : s ≤ (79 : ℝ) / 25
        · have hband := pA_band3 (le_of_lt hs3') hs79
          have hd9 : (9 : ℝ) / 5 < d := by
            by_contra hnot
            have hle : d ≤ (9 : ℝ) / 5 := le_of_not_gt hnot
            have hPle : pA s d ≤ pA s ((9 : ℝ) / 5) :=
              pA_le_of_le hs hle hband.2
            exact (not_lt_of_ge hPnonneg) (hPle.trans_lt hband.1)
          have hN : 0 < nA s ((9 : ℝ) / 5) :=
            nA_band3_pos (le_of_lt hs3')
          have hbase : (53 : ℝ) / 8 < phiA s ((9 : ℝ) / 5) :=
            phiA_gt_of_nA_pos hspos (by norm_num) hN
          have hmono : phiA s ((9 : ℝ) / 5) < phiA s d :=
            phiA_lt_of_lt hs hd1 (by norm_num) hd9
          exact le_of_lt (hbase.trans hmono)
        · have hs79' : (79 : ℝ) / 25 < s := lt_of_not_ge hs79
          have hband := pA_band4 (le_of_lt hs79') (le_of_lt hsUpper)
          have hd7 : (7 : ℝ) / 4 < d := by
            by_contra hnot
            have hle : d ≤ (7 : ℝ) / 4 := le_of_not_gt hnot
            have hPle : pA s d ≤ pA s ((7 : ℝ) / 4) :=
              pA_le_of_le hs hle hband.2
            exact (not_lt_of_ge hPnonneg) (hPle.trans_lt hband.1)
          have hN : 0 < nA s ((7 : ℝ) / 4) :=
            nA_band4_pos (le_of_lt hs79')
          have hbase : (53 : ℝ) / 8 < phiA s ((7 : ℝ) / 4) :=
            phiA_gt_of_nA_pos hspos (by norm_num) hN
          have hmono : phiA s ((7 : ℝ) / 4) < phiA s d :=
            phiA_lt_of_lt hs hd1 (by norm_num) hd7
          exact le_of_lt (hbase.trans hmono)

end

end Heilbronn8.HullSixTwoFourQ22Reverse
