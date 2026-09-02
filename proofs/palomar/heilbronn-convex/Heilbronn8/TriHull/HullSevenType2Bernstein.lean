import Mathlib

/-!
# Exact interval signs for the hull-seven type 2 scalar reduction

The type 2 scalar proof reduces its remaining one-variable signs to six
Bernstein expansions.  This module records those expansions directly over
the rationals.  Every Bernstein coefficient is strictly positive, so the
sign conclusions use no numerical approximation or external certificate.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

private noncomputable def bernsteinEight
    (z v0 v1 v2 v3 v4 v5 v6 v7 v8 : ℝ) : ℝ :=
  v0 * (1 - z) ^ 8 +
  8 * v1 * z * (1 - z) ^ 7 +
  28 * v2 * z ^ 2 * (1 - z) ^ 6 +
  56 * v3 * z ^ 3 * (1 - z) ^ 5 +
  70 * v4 * z ^ 4 * (1 - z) ^ 4 +
  56 * v5 * z ^ 5 * (1 - z) ^ 3 +
  28 * v6 * z ^ 6 * (1 - z) ^ 2 +
  8 * v7 * z ^ 7 * (1 - z) +
  v8 * z ^ 8

private lemma bernsteinEight_pos
    (z v0 v1 v2 v3 v4 v5 v6 v7 v8 : ℝ)
    (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hv0 : 0 < v0) (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2)
    (hv3 : 0 ≤ v3) (hv4 : 0 ≤ v4) (hv5 : 0 ≤ v5)
    (hv6 : 0 ≤ v6) (hv7 : 0 ≤ v7) (hv8 : 0 < v8) :
    0 < bernsteinEight z v0 v1 v2 v3 v4 v5 v6 v7 v8 := by
  have hOneMinus : 0 ≤ 1 - z := by linarith
  by_cases hone : z = 1
  · subst z
    simpa [bernsteinEight] using hv8
  · have hOneMinusPos : 0 < 1 - z := sub_pos.mpr (lt_of_le_of_ne hz1 hone)
    have h0 : 0 < v0 * (1 - z) ^ 8 :=
      mul_pos hv0 (pow_pos hOneMinusPos 8)
    have h1 : 0 ≤ 8 * v1 * z * (1 - z) ^ 7 := by positivity
    have h2 : 0 ≤ 28 * v2 * z ^ 2 * (1 - z) ^ 6 := by positivity
    have h3 : 0 ≤ 56 * v3 * z ^ 3 * (1 - z) ^ 5 := by positivity
    have h4 : 0 ≤ 70 * v4 * z ^ 4 * (1 - z) ^ 4 := by positivity
    have h5 : 0 ≤ 56 * v5 * z ^ 5 * (1 - z) ^ 3 := by positivity
    have h6 : 0 ≤ 28 * v6 * z ^ 6 * (1 - z) ^ 2 := by positivity
    have h7 : 0 ≤ 8 * v7 * z ^ 7 * (1 - z) := by positivity
    have h8 : 0 ≤ v8 * z ^ 8 := by positivity
    unfold bernsteinEight
    positivity

private noncomputable def bernsteinSeven
    (z v0 v1 v2 v3 v4 v5 v6 v7 : ℝ) : ℝ :=
  v0 * (1 - z) ^ 7 +
  7 * v1 * z * (1 - z) ^ 6 +
  21 * v2 * z ^ 2 * (1 - z) ^ 5 +
  35 * v3 * z ^ 3 * (1 - z) ^ 4 +
  35 * v4 * z ^ 4 * (1 - z) ^ 3 +
  21 * v5 * z ^ 5 * (1 - z) ^ 2 +
  7 * v6 * z ^ 6 * (1 - z) +
  v7 * z ^ 7

private lemma bernsteinSeven_pos
    (z v0 v1 v2 v3 v4 v5 v6 v7 : ℝ)
    (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hv0 : 0 < v0) (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2)
    (hv3 : 0 ≤ v3) (hv4 : 0 ≤ v4) (hv5 : 0 ≤ v5)
    (hv6 : 0 ≤ v6) (hv7 : 0 < v7) :
    0 < bernsteinSeven z v0 v1 v2 v3 v4 v5 v6 v7 := by
  have hOneMinus : 0 ≤ 1 - z := by linarith
  by_cases hone : z = 1
  · subst z
    simpa [bernsteinSeven] using hv7
  · have hOneMinusPos : 0 < 1 - z := sub_pos.mpr (lt_of_le_of_ne hz1 hone)
    have h0 : 0 < v0 * (1 - z) ^ 7 :=
      mul_pos hv0 (pow_pos hOneMinusPos 7)
    have h1 : 0 ≤ 7 * v1 * z * (1 - z) ^ 6 := by positivity
    have h2 : 0 ≤ 21 * v2 * z ^ 2 * (1 - z) ^ 5 := by positivity
    have h3 : 0 ≤ 35 * v3 * z ^ 3 * (1 - z) ^ 4 := by positivity
    have h4 : 0 ≤ 35 * v4 * z ^ 4 * (1 - z) ^ 3 := by positivity
    have h5 : 0 ≤ 21 * v5 * z ^ 5 * (1 - z) ^ 2 := by positivity
    have h6 : 0 ≤ 7 * v6 * z ^ 6 * (1 - z) := by positivity
    have h7 : 0 ≤ v7 * z ^ 7 := by positivity
    unfold bernsteinSeven
    positivity

/-- The outer obstruction polynomial is positive to the left of the surviving
`rho` interval. -/
theorem hullSevenType2_outer_left_pos
    (rho : ℝ) (hlo : 13 / 40 ≤ rho) (hhi : rho ≤ 5 / 8) :
    0 < 8 * rho ^ 8 - 244 * rho ^ 7 + 732 * rho ^ 6 +
      9456 * rho ^ 5 - 12836 * rho ^ 4 + 2157 * rho ^ 3 +
      2662 * rho ^ 2 - 1024 * rho + 96 := by
  let z : ℝ := (40 * rho - 13) / 12
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 1 := by dsimp [z]; linarith
  have hpos := bernsteinEight_pos z
    58890081051067 95162781401065 131076283110775
    155203696661125 158376099149875 136259825790625
    91963704859375 38641246328125 2055804296875
    hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hid :
      (5734400000000 : ℝ) *
        (8 * rho ^ 8 - 244 * rho ^ 7 + 732 * rho ^ 6 +
          9456 * rho ^ 5 - 12836 * rho ^ 4 + 2157 * rho ^ 3 +
          2662 * rho ^ 2 - 1024 * rho + 96) =
      bernsteinEight z
        58890081051067 95162781401065 131076283110775
        155203696661125 158376099149875 136259825790625
        91963704859375 38641246328125 2055804296875 := by
    dsimp [z, bernsteinEight]
    ring
  rw [← hid] at hpos
  nlinarith

/-- The outer obstruction polynomial is positive to the right of the
surviving `rho` interval. -/
theorem hullSevenType2_outer_right_pos
    (rho : ℝ) (hlo : 5 / 7 ≤ rho) (hhi : rho ≤ 5 / 2) :
    0 < 8 * rho ^ 8 - 244 * rho ^ 7 + 732 * rho ^ 6 +
      9456 * rho ^ 5 - 12836 * rho ^ 4 + 2157 * rho ^ 3 +
      2662 * rho ^ 2 - 1024 * rho + 96 := by
  let z : ℝ := (14 * rho - 10) / 25
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 1 := by dsimp [z]; linarith
  have hpos := bernsteinEight_pos z
    450959616 90133068816 916989068016 5020550019716
    19993379486416 63334237593116 166662573214816
    377176424367141 755456510003216
    hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hid :
      (1475789056 : ℝ) *
        (8 * rho ^ 8 - 244 * rho ^ 7 + 732 * rho ^ 6 +
          9456 * rho ^ 5 - 12836 * rho ^ 4 + 2157 * rho ^ 3 +
          2662 * rho ^ 2 - 1024 * rho + 96) =
      bernsteinEight z
        450959616 90133068816 916989068016 5020550019716
        19993379486416 63334237593116 166662573214816
        377176424367141 755456510003216 := by
    dsimp [z, bernsteinEight]
    ring
  rw [← hid] at hpos
  nlinarith

/-- The endpoint polynomial giving the lower bound on `g` is positive on the
surviving `rho` interval. -/
theorem hullSevenType2_g_endpoint_pos
    (rho : ℝ) (hlo : 5 / 8 ≤ rho) (hhi : rho ≤ 5 / 7) :
    0 < 24 * rho ^ 7 - 440 * rho ^ 6 + 802 * rho ^ 5 +
      14516 * rho ^ 4 - 26507 * rho ^ 3 + 15664 * rho ^ 2 -
      3388 * rho + 240 := by
  let z : ℝ := (56 * rho - 35) / 5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 1 := by dsimp [z]; linarith
  have hpos := bernsteinSeven_pos z
    23272373987835 20587652631840 18144919602320 16087682352000
    14576675796480 13789748367360 13921732362240 15184299294720
    hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hid :
      (647660568576 : ℝ) *
        (24 * rho ^ 7 - 440 * rho ^ 6 + 802 * rho ^ 5 +
          14516 * rho ^ 4 - 26507 * rho ^ 3 + 15664 * rho ^ 2 -
          3388 * rho + 240) =
      bernsteinSeven z
        23272373987835 20587652631840 18144919602320 16087682352000
        14576675796480 13789748367360 13921732362240
        15184299294720 := by
    dsimp [z, bernsteinSeven]
    ring
  rw [← hid] at hpos
  nlinarith

/-- The endpoint polynomial giving the upper bound on `u` is positive on the
surviving `rho` interval. -/
theorem hullSevenType2_u_endpoint_pos
    (rho : ℝ) (hlo : 5 / 8 ≤ rho) (hhi : rho ≤ 5 / 7) :
    0 < 64 * rho ^ 8 - 1948 * rho ^ 7 + 5830 * rho ^ 6 +
      75512 * rho ^ 5 - 102363 * rho ^ 4 + 17485 * rho ^ 3 +
      21118 * rho ^ 2 - 8168 * rho + 768 := by
  let z : ℝ := (56 * rho - 35) / 5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 1 := by dsimp [z]; linarith
  have hpos := bernsteinEight_pos z
    954246079859352 659886640067557 419869929689112
    257230613003392 198335892726272 273087071050752
    515120238968832 962005871296512 1655447111073792
    hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hid :
      (24179327893504 : ℝ) *
        (64 * rho ^ 8 - 1948 * rho ^ 7 + 5830 * rho ^ 6 +
          75512 * rho ^ 5 - 102363 * rho ^ 4 + 17485 * rho ^ 3 +
          21118 * rho ^ 2 - 8168 * rho + 768) =
      bernsteinEight z
        954246079859352 659886640067557 419869929689112
        257230613003392 198335892726272 273087071050752
        515120238968832 962005871296512 1655447111073792 := by
    dsimp [z, bernsteinEight]
    ring
  rw [← hid] at hpos
  nlinarith

/-- The epsilon-threshold polynomial is positive on the left half of the
surviving `rho` interval. -/
theorem hullSevenType2_epsilon_left_pos
    (rho : ℝ) (hlo : 5 / 8 ≤ rho) (hhi : rho ≤ 2 / 3) :
    0 < 32768 * rho ^ 8 - 997376 * rho ^ 7 + 2974240 * rho ^ 6 +
      38523136 * rho ^ 5 - 52170591 * rho ^ 4 + 8796688 * rho ^ 3 +
      10845760 * rho ^ 2 - 4184064 * rho + 393216 := by
  let z : ℝ := 24 * rho - 15
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 1 := by dsimp [z]; linarith
  have hpos := bernsteinEight_pos z
    124671291246180 101949658672995 81084969436185 62448744333060
    46437604083396 33473977116480 24006805908480 18512251699200
    17494397419520
    hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hid :
      (7524679680 : ℝ) *
        (32768 * rho ^ 8 - 997376 * rho ^ 7 + 2974240 * rho ^ 6 +
          38523136 * rho ^ 5 - 52170591 * rho ^ 4 +
          8796688 * rho ^ 3 + 10845760 * rho ^ 2 -
          4184064 * rho + 393216) =
      bernsteinEight z
        124671291246180 101949658672995 81084969436185 62448744333060
        46437604083396 33473977116480 24006805908480 18512251699200
        17494397419520 := by
    dsimp [z, bernsteinEight]
    ring
  rw [← hid] at hpos
  nlinarith

/-- The epsilon-threshold polynomial is positive on the right half of the
surviving `rho` interval. -/
theorem hullSevenType2_epsilon_right_pos
    (rho : ℝ) (hlo : 2 / 3 ≤ rho) (hhi : rho ≤ 5 / 7) :
    0 < 32768 * rho ^ 8 - 997376 * rho ^ 7 + 2974240 * rho ^ 6 +
      38523136 * rho ^ 5 - 52170591 * rho ^ 4 + 8796688 * rho ^ 3 +
      10845760 * rho ^ 2 - 4184064 * rho + 393216 := by
  let z : ℝ := 21 * rho - 14
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 1 := by dsimp [z]; linarith
  have hpos := bernsteinEight_pos z
    879357210331040 820885756156200 1056320144625060 1623482348145210
    2562588624134007 3916318401907695 5729882969167245
    8051093936487315 10930431458542410
    hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hid :
      (378228593610 : ℝ) *
        (32768 * rho ^ 8 - 997376 * rho ^ 7 + 2974240 * rho ^ 6 +
          38523136 * rho ^ 5 - 52170591 * rho ^ 4 +
          8796688 * rho ^ 3 + 10845760 * rho ^ 2 -
          4184064 * rho + 393216) =
      bernsteinEight z
        879357210331040 820885756156200 1056320144625060
        1623482348145210 2562588624134007 3916318401907695
        5729882969167245 8051093936487315 10930431458542410 := by
    dsimp [z, bernsteinEight]
    ring
  rw [← hid] at hpos
  nlinarith

end Heilbronn8.TriHull
