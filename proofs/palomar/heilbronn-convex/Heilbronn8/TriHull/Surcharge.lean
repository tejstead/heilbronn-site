import Heilbronn8.TriHull.Core

namespace Heilbronn8.TriHull

lemma fan_triangle_linear_le_vertex {u a b x y : ℝ}
    (_hu : 2 ≤ u) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : a + b ≤ u + 2) :
    x * a + y * b ≤ x * 2 + y * 2 ∨
      x * a + y * b ≤ x * u + y * 2 ∨
      x * a + y * b ≤ x * 2 + y * u := by
  have hgap : 0 ≤ u + 2 - a - b := by linarith
  by_cases hx : 0 ≤ x
  · by_cases hyx : y ≤ x
    · right
      left
      have hxb := mul_nonneg hx hgap
      have hxyb :=
        mul_nonneg (sub_nonneg.mpr hyx) (by linarith : 0 ≤ b - 2)
      nlinarith
    · right
      right
      have hxy : x ≤ y := le_of_not_ge hyx
      have hy : 0 ≤ y := le_trans hx hxy
      have hya := mul_nonneg hy hgap
      have hyxa :=
        mul_nonneg (sub_nonneg.mpr hxy) (by linarith : 0 ≤ a - 2)
      nlinarith
  · have hxneg : x < 0 := lt_of_not_ge hx
    by_cases hy : 0 ≤ y
    · right
      right
      have hxy : x ≤ y := by linarith
      have hya := mul_nonneg hy hgap
      have hyxa :=
        mul_nonneg (sub_nonneg.mpr hxy) (by linarith : 0 ≤ a - 2)
      nlinarith
    · left
      have hyneg : y < 0 := lt_of_not_ge hy
      have hxa :=
        mul_nonneg (by linarith : 0 ≤ -x) (by linarith : 0 ≤ a - 2)
      have hyb :=
        mul_nonneg (by linarith : 0 ≤ -y) (by linarith : 0 ≤ b - 2)
      nlinarith

lemma adjacent_fan_cubic_corner_pos {u v : ℝ}
    (_hu : 2 ≤ u) (hv : 2 ≤ v) (hs : u + v < 7) :
    0 < -u * v ^ 2 - 2 * u * v + 4 * u + 12 * v + 16 := by
  have hcoeff : 0 < v ^ 2 + 2 * v - 4 := by
    nlinarith [sq_nonneg (v - 2)]
  have hreplace : 0 < (7 - v - u) * (v ^ 2 + 2 * v - 4) :=
    mul_pos (by linarith) hcoeff
  have hpoly : 0 < v ^ 3 - 5 * v ^ 2 - 6 * v + 44 := by
    by_cases hv4 : 4 ≤ v
    · have hmono : 0 ≤ (v - 4) * (v + 3) :=
        mul_nonneg (by linarith) (by linarith)
      have hfac : 0 ≤ (v - 4) * (v ^ 2 - v - 10) :=
        mul_nonneg (by linarith) (by nlinarith [hmono])
      nlinarith
    · have hvle : v ≤ 4 := le_of_not_ge hv4
      have hxprod : 0 ≤ (v - 4) ^ 2 * (v - 2) :=
        mul_nonneg (sq_nonneg (v - 4)) (by linarith)
      have hsq := sq_nonneg (5 * (v - 4) + 1)
      nlinarith
  nlinarith

lemma adjacent_fan_corner_gaps {u v : ℝ}
    (hu : 2 ≤ u) (hv : 2 ≤ v) (hs : u + v < 7) :
    0 < 2 * (u + 2) * (v + 2) ∧
    0 < 2 * (v + 2) * (u - v + 4) ∧
    0 < 4 * (2 * u - v + 6) ∧
    0 < 4 * (-u + 2 * v + 6) ∧
    0 < -u * v ^ 2 - 2 * u * v + 4 * u + 12 * v + 16 ∧
    0 < 40 - 2 * u * v ∧
    0 < 2 * (u + 2) * (v - u + 4) ∧
    0 < 32 - 2 * (u - v) ^ 2 ∧
    0 < -u ^ 2 * v - 2 * u * v + 12 * u + 4 * v + 16 := by
  have hsumpos : 0 < u + v := by linarith
  have hsum_sq : (u + v) ^ 2 < 49 := by
    have hp : 0 < (7 - (u + v)) * (7 + (u + v)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have huv : 4 * u * v ≤ (u + v) ^ 2 := by
    nlinarith [sq_nonneg (u - v)]
  have hdiff : (u - v) ^ 2 < 9 := by
    have hp : 0 < (3 - (u - v)) * (3 + (u - v)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  · exact mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  · nlinarith
  · nlinarith
  · exact adjacent_fan_cubic_corner_pos hu hv hs
  · nlinarith
  · exact mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  · nlinarith
  · have h := adjacent_fan_cubic_corner_pos hv hu (by linarith)
    nlinarith

lemma adjacent_fan_upper_lt_two_product
    {α β a b c d e f : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hα : α = a + b + c) (hβ : β = d + e + f)
    (hsum : α + β < 15) :
    a * d * β + b * e * α - 2 * b * d < 2 * α * β := by
  let u : ℝ := α - 4
  let v : ℝ := β - 4
  have hu : 2 ≤ u := by
    dsimp [u]
    nlinarith
  have hv : 2 ≤ v := by
    dsimp [v]
    nlinarith
  have huv : u + v < 7 := by
    dsimp [u, v]
    linarith
  have hab : a + b ≤ u + 2 := by
    dsimp [u]
    linarith
  have hde : d + e ≤ v + 2 := by
    dsimp [v]
    linarith
  rcases adjacent_fan_corner_gaps hu hv huv with
    ⟨hg00, hg01, hg02, hg10, hg11, hg12, hg20, hg21, hg22⟩
  have hfirst := fan_triangle_linear_le_vertex hv hd he hde
      (x := a * β - 2 * b) (y := b * α)
  rcases hfirst with hfirst | hfirst | hfirst
  · have hsecond := fan_triangle_linear_le_vertex hu ha hb hab
        (x := 2 * β) (y := 2 * α - 4)
    rcases hsecond with hsecond | hsecond | hsecond
    · calc
        a * d * β + b * e * α - 2 * b * d =
            (a * β - 2 * b) * d + (b * α) * e := by ring1
        _ ≤ (a * β - 2 * b) * 2 + (b * α) * 2 := hfirst
        _ = (2 * β) * a + (2 * α - 4) * b := by ring1
        _ ≤ (2 * β) * 2 + (2 * α - 4) * 2 := hsecond
        _ < 2 * α * β := by
          dsimp [u, v] at hg00 ⊢
          nlinarith [hg00]
    · calc
        a * d * β + b * e * α - 2 * b * d =
            (a * β - 2 * b) * d + (b * α) * e := by ring1
        _ ≤ (a * β - 2 * b) * 2 + (b * α) * 2 := hfirst
        _ = (2 * β) * a + (2 * α - 4) * b := by ring1
        _ ≤ (2 * β) * u + (2 * α - 4) * 2 := hsecond
        _ < 2 * α * β := by
          dsimp [u, v] at hg10 ⊢
          nlinarith [hg10]
    · calc
        a * d * β + b * e * α - 2 * b * d =
            (a * β - 2 * b) * d + (b * α) * e := by ring1
        _ ≤ (a * β - 2 * b) * 2 + (b * α) * 2 := hfirst
        _ = (2 * β) * a + (2 * α - 4) * b := by ring1
        _ ≤ (2 * β) * 2 + (2 * α - 4) * u := hsecond
        _ < 2 * α * β := by
          dsimp [u, v] at hg20 ⊢
          nlinarith [hg20]
  · have hsecond := fan_triangle_linear_le_vertex hu ha hb hab
        (x := v * β) (y := 2 * α - 2 * v)
    rcases hsecond with hsecond | hsecond | hsecond
    · calc
        a * d * β + b * e * α - 2 * b * d =
            (a * β - 2 * b) * d + (b * α) * e := by ring1
        _ ≤ (a * β - 2 * b) * v + (b * α) * 2 := hfirst
        _ = (v * β) * a + (2 * α - 2 * v) * b := by ring1
        _ ≤ (v * β) * 2 + (2 * α - 2 * v) * 2 := hsecond
        _ < 2 * α * β := by
          dsimp [u, v] at hg01 ⊢
          nlinarith [hg01]
    · calc
        a * d * β + b * e * α - 2 * b * d =
            (a * β - 2 * b) * d + (b * α) * e := by ring1
        _ ≤ (a * β - 2 * b) * v + (b * α) * 2 := hfirst
        _ = (v * β) * a + (2 * α - 2 * v) * b := by ring1
        _ ≤ (v * β) * u + (2 * α - 2 * v) * 2 := hsecond
        _ < 2 * α * β := by
          dsimp [u, v] at hg11 ⊢
          nlinarith [hg11]
    · calc
        a * d * β + b * e * α - 2 * b * d =
            (a * β - 2 * b) * d + (b * α) * e := by ring1
        _ ≤ (a * β - 2 * b) * v + (b * α) * 2 := hfirst
        _ = (v * β) * a + (2 * α - 2 * v) * b := by ring1
        _ ≤ (v * β) * 2 + (2 * α - 2 * v) * u := hsecond
        _ < 2 * α * β := by
          dsimp [u, v] at hg21 ⊢
          nlinarith [hg21]
  · have hsecond := fan_triangle_linear_le_vertex hu ha hb hab
        (x := 2 * β) (y := v * α - 4)
    rcases hsecond with hsecond | hsecond | hsecond
    · calc
        a * d * β + b * e * α - 2 * b * d =
            (a * β - 2 * b) * d + (b * α) * e := by ring1
        _ ≤ (a * β - 2 * b) * 2 + (b * α) * v := hfirst
        _ = (2 * β) * a + (v * α - 4) * b := by ring1
        _ ≤ (2 * β) * 2 + (v * α - 4) * 2 := hsecond
        _ < 2 * α * β := by
          dsimp [u, v] at hg02 ⊢
          nlinarith [hg02]
    · calc
        a * d * β + b * e * α - 2 * b * d =
            (a * β - 2 * b) * d + (b * α) * e := by ring1
        _ ≤ (a * β - 2 * b) * 2 + (b * α) * v := hfirst
        _ = (2 * β) * a + (v * α - 4) * b := by ring1
        _ ≤ (2 * β) * u + (v * α - 4) * 2 := hsecond
        _ < 2 * α * β := by
          dsimp [u, v] at hg12 ⊢
          nlinarith [hg12]
    · calc
        a * d * β + b * e * α - 2 * b * d =
            (a * β - 2 * b) * d + (b * α) * e := by ring1
        _ ≤ (a * β - 2 * b) * 2 + (b * α) * v := hfirst
        _ = (2 * β) * a + (v * α - 4) * b := by ring1
        _ ≤ (2 * β) * 2 + (v * α - 4) * u := hsecond
        _ < 2 * α * β := by
          dsimp [u, v] at hg22 ⊢
          nlinarith [hg22]

lemma adjacent_fan_positive_sign
    {α β γ a b c d e f D : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hγ : 2 ≤ γ)
    (hα : α = a + b + c) (hβ : β = d + e + f)
    (hid : α * β * D = a * d * β + b * e * α - b * d * γ)
    (hsum : α + β < 15) (hDnonneg : 0 ≤ D) :
    0 ≤ D ∧ D < 2 := by
  refine ⟨hDnonneg, ?_⟩
  have hupper := adjacent_fan_upper_lt_two_product
    ha hb hc hd he hf hα hβ hsum
  have hαpos : 0 < α := by nlinarith
  have hβpos : 0 < β := by nlinarith
  have hbd : 0 ≤ b * d := mul_nonneg (by linarith) (by linarith)
  have hreplace : 0 ≤ b * d * (γ - 2) :=
    mul_nonneg hbd (by linarith)
  have hmain : α * β * D < 2 * α * β := by
    nlinarith [hid, hupper, hreplace]
  by_contra h
  have hD : 2 ≤ D := le_of_not_gt h
  have hp : 0 ≤ α * β * (D - 2) :=
    mul_nonneg (mul_nonneg hαpos.le hβpos.le) (by linarith)
  nlinarith

lemma adjacent_fan_negative_sign_part1
    {α β γ a b c d e f D : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hγ : 2 ≤ γ)
    (hα : α = a + b + c) (hβ : β = d + e + f)
    (hid : α * β * D = a * d * β + b * e * α - b * d * γ)
    (hsum : α + β + γ < 17) (hDneg : D < 0) :
    0 < -D ∧ -D < 2 := by
  refine ⟨by linarith, ?_⟩
  have hαpos : 0 < α := by nlinarith
  have hβpos : 0 < β := by nlinarith
  have hαlt : α < 9 := by nlinarith
  have hβlt : β < 9 := by nlinarith
  have hγlt : γ < 5 := by nlinarith
  have hbupper : b ≤ α - 4 := by nlinarith
  have hdupper : d ≤ β - 4 := by nlinarith
  have h9b : 9 * b < 5 * α := by nlinarith
  have h9d : 9 * d < 5 * β := by nlinarith
  have hstep1 : 81 * b * d < 45 * α * d := by
    have hp : 0 < (5 * α - 9 * b) * (9 * d) :=
      mul_pos (by linarith) (by positivity)
    nlinarith
  have hstep2 : 45 * α * d < 25 * α * β := by
    have hp : 0 < (5 * β - 9 * d) * (5 * α) :=
      mul_pos (by linarith) (by positivity)
    nlinarith
  have hbd : 81 * b * d < 25 * α * β :=
    lt_trans hstep1 hstep2
  have hγstep : 81 * b * d * γ < 405 * b * d := by
    have hp : 0 < (5 - γ) * (81 * b * d) :=
      mul_pos (by linarith) (by positivity)
    nlinarith
  have hbdγ : 81 * b * d * γ < 125 * α * β := by
    nlinarith [hγstep, hbd]
  have hcross : b * d * γ < 2 * α * β := by
    have hp := mul_pos hαpos hβpos
    nlinarith [hbdγ]
  have hnegid :
      α * β * (-D) = b * d * γ - a * d * β - b * e * α := by
    linear_combination -hid
  have hstrict : α * β * (-D) < b * d * γ := by
    have hadβ : 0 < a * d * β := by positivity
    have hbeα : 0 < b * e * α := by positivity
    nlinarith [hnegid]
  have hmain : α * β * (-D) < 2 * α * β :=
    lt_trans hstrict hcross
  by_contra h
  have hD : 2 ≤ -D := le_of_not_gt h
  have hp : 0 ≤ α * β * (-D - 2) :=
    mul_nonneg (mul_nonneg hαpos.le hβpos.le) (by linarith)
  nlinarith

set_option maxHeartbeats 1600000 in
lemma adjacent_fan_negative_sign_part2
    {α β γ a b c d e f D : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hγ : 6 ≤ γ)
    (hα : α = a + b + c) (hβ : β = d + e + f)
    (hid : α * β * D = a * d * β + b * e * α - b * d * γ)
    (hsum : α + β + γ < 21) (hDneg : D < 0) :
    0 < -D ∧ -D < 2 := by
  refine ⟨by linarith, ?_⟩
  let u : ℝ := α - 4
  let v : ℝ := β - 4
  let s : ℝ := u + v
  have hαpos : 0 < α := by nlinarith
  have hβpos : 0 < β := by nlinarith
  have hu : 2 ≤ u := by
    dsimp [u]
    nlinarith
  have hv : 2 ≤ v := by
    dsimp [v]
    nlinarith
  have hslo : 4 ≤ s := by
    dsimp [s]
    linarith
  have hshi : s < 7 := by
    dsimp [s, u, v]
    linarith
  have hγupper : γ < 13 - s := by
    dsimp [s, u, v]
    linarith
  have hbupper : b ≤ u := by
    dsimp [u]
    nlinarith
  have hdupper : d ≤ v := by
    dsimp [v]
    nlinarith
  have hbd1 : b * d ≤ u * d := by
    have hp : 0 ≤ (u - b) * d :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hbd2 : u * d ≤ u * v := by
    have hp : 0 ≤ u * (v - d) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hbd : b * d ≤ u * v := le_trans hbd1 hbd2
  have hbdγ : b * d * γ ≤ u * v * γ := by
    have hp : 0 ≤ (u * v - b * d) * γ :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have huvpos : 0 < u * v :=
    mul_pos (by linarith) (by linarith)
  have hγstrict : u * v * γ < u * v * (13 - s) := by
    have hp : 0 < u * v * (13 - s - γ) :=
      mul_pos huvpos (by linarith)
    nlinarith
  have hsqdiff : 4 * u * v ≤ s ^ 2 := by
    dsimp [s]
    nlinarith [sq_nonneg (u - v)]
  have hfactor : 0 ≤ (s ^ 2 - 4 * u * v) * (11 - s) :=
    mul_nonneg (by linarith) (by linarith)
  have hquad : s ^ 2 - 4 * s - 28 ≤ 0 := by
    have hp : 0 ≤ (7 - s) * (s + 3) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hcubic : 0 ≤ (s - 7) * (s ^ 2 - 4 * s - 28) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) hquad
  have hpoly : s ^ 2 * (11 - s) ≤ 196 := by
    nlinarith [hcubic]
  have huvbound : u * v * (11 - s) ≤ 49 := by
    nlinarith [hfactor, hpoly]
  have hfraction :
      u * v * (13 - s) < 2 * (u + 4) * (v + 4) := by
    nlinarith [huvbound]
  have hcross : b * d * γ < 2 * α * β := by
    dsimp [u, v] at hfraction hγstrict hbdγ ⊢
    nlinarith [hbdγ, hγstrict, hfraction]
  have hnegid :
      α * β * (-D) = b * d * γ - a * d * β - b * e * α := by
    linear_combination -hid
  have hstrict : α * β * (-D) < b * d * γ := by
    have hadβ : 0 < a * d * β := by positivity
    have hbeα : 0 < b * e * α := by positivity
    nlinarith [hnegid]
  have hmain : α * β * (-D) < 2 * α * β :=
    lt_trans hstrict hcross
  by_contra h
  have hD : 2 ≤ -D := le_of_not_gt h
  have hp : 0 ≤ α * β * (-D - 2) :=
    mul_nonneg (mul_nonneg hαpos.le hβpos.le) (by linarith)
  nlinarith

lemma adjacent_fan_surcharge_part1_numeric
    {α β γ a b c d e f D : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hγ : 2 ≤ γ)
    (hα : α = a + b + c) (hβ : β = d + e + f)
    (hid : α * β * D = a * d * β + b * e * α - b * d * γ)
    (hD : 2 ≤ |D|) :
    17 ≤ α + β + γ := by
  by_contra h
  have hsum : α + β + γ < 17 := lt_of_not_ge h
  have hαβ : α + β < 15 := by linarith
  by_cases hsign : 0 ≤ D
  · have hpos := adjacent_fan_positive_sign
      ha hb hc hd he hf hγ hα hβ hid hαβ hsign
    have hDmin : 2 ≤ D := by
      rwa [abs_of_nonneg hsign] at hD
    linarith
  · have hDneg : D < 0 := lt_of_not_ge hsign
    have hneg := adjacent_fan_negative_sign_part1
      ha hb hc hd he hf hγ hα hβ hid hsum hDneg
    have hDmin : 2 ≤ -D := by
      rwa [abs_of_neg hDneg] at hD
    linarith

lemma adjacent_fan_surcharge_part2_numeric
    {α β γ a b c d e f D : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hγ : 6 ≤ γ)
    (hα : α = a + b + c) (hβ : β = d + e + f)
    (hid : α * β * D = a * d * β + b * e * α - b * d * γ)
    (hD : 2 ≤ |D|) :
    21 ≤ α + β + γ := by
  by_contra h
  have hsum : α + β + γ < 21 := lt_of_not_ge h
  have hαβ : α + β < 15 := by linarith
  have hγtwo : 2 ≤ γ := by linarith
  by_cases hsign : 0 ≤ D
  · have hpos := adjacent_fan_positive_sign
      ha hb hc hd he hf hγtwo hα hβ hid hαβ hsign
    have hDmin : 2 ≤ D := by
      rwa [abs_of_nonneg hsign] at hD
    linarith
  · have hDneg : D < 0 := lt_of_not_ge hsign
    have hneg := adjacent_fan_negative_sign_part2
      ha hb hc hd he hf hγ hα hβ hid hsum hDneg
    have hDmin : 2 ≤ -D := by
      rwa [abs_of_neg hDneg] at hD
    linarith

/--
All twenty triangles on `A B C P Q R` have ordinary area at least one.
Since `sig` is doubled signed area, each absolute signed area is at least two.
-/
def SixPointMinAreaOne (A B C P Q R : ℝ × ℝ) : Prop :=
  2 ≤ |sig A B C| ∧
  2 ≤ |sig A B P| ∧
  2 ≤ |sig A B Q| ∧
  2 ≤ |sig A B R| ∧
  2 ≤ |sig A C P| ∧
  2 ≤ |sig A C Q| ∧
  2 ≤ |sig A C R| ∧
  2 ≤ |sig A P Q| ∧
  2 ≤ |sig A P R| ∧
  2 ≤ |sig A Q R| ∧
  2 ≤ |sig B C P| ∧
  2 ≤ |sig B C Q| ∧
  2 ≤ |sig B C R| ∧
  2 ≤ |sig B P Q| ∧
  2 ≤ |sig B P R| ∧
  2 ≤ |sig B Q R| ∧
  2 ≤ |sig C P Q| ∧
  2 ≤ |sig C P R| ∧
  2 ≤ |sig C Q R| ∧
  2 ≤ |sig P Q R|

lemma th8_lemma2_doubled_bounds {A B C P Q R : ℝ × ℝ}
    (hABC : 0 < sig A B C)
    (hP : InTriStrict P A B C)
    (hQ : InTriStrict Q P B C)
    (hR : InTriStrict R P C A)
    (hmin : SixPointMinAreaOne A B C P Q R) :
    17 ≤ sig A B C ∧ (6 ≤ sig P A B → 21 ≤ sig A B C) := by
  rcases hmin with
    ⟨_hABCmin, hABPmin, _hABQmin, _hABRmin, _hACPmin,
      _hACQmin, hACRmin, _hAPQmin, hAPRmin, _hAQRmin,
      _hBCPmin, hBCQmin, _hBCRmin, hBPQmin, _hBPRmin,
      _hBQRmin, hCPQmin, hCPRmin, _hCQRmin, hPQRmin⟩
  obtain ⟨hαpos0, hβpos0, hγpos0⟩ :=
    inTriStrict_fan_pos hABC hP
  obtain ⟨hcpos0, hbpos0, hapos0⟩ :=
    inTriStrict_fan_pos hαpos0 hQ
  obtain ⟨hfpos0, hepos0, hdpos0⟩ :=
    inTriStrict_fan_pos hβpos0 hR

  let α : ℝ := sig P B C
  let β : ℝ := sig P C A
  let γ : ℝ := sig P A B
  let a : ℝ := sig P B Q
  let b : ℝ := sig P Q C
  let c : ℝ := sig Q B C
  let d : ℝ := sig P C R
  let e : ℝ := sig P R A
  let f : ℝ := sig R C A
  let D : ℝ := sig P Q R

  have hαpos : 0 < α := by simpa [α] using hαpos0
  have hβpos : 0 < β := by simpa [β] using hβpos0
  have hγpos : 0 < γ := by simpa [γ] using hγpos0
  have hapos : 0 < a := by
    have hrot : sig Q P B = sig P B Q := by
      rw [sig_rotate Q P B]
    simpa [a, hrot] using hapos0
  have hbpos : 0 < b := by
    have hrot : sig Q C P = sig P Q C := by
      rw [sig_rotate Q C P, sig_rotate C P Q]
    simpa [b, hrot] using hbpos0
  have hcpos : 0 < c := by simpa [c] using hcpos0
  have hdpos : 0 < d := by
    have hrot : sig R P C = sig P C R := by
      rw [sig_rotate R P C]
    simpa [d, hrot] using hdpos0
  have hepos : 0 < e := by
    have hrot : sig R A P = sig P R A := by
      rw [sig_rotate R A P, sig_rotate A P R]
    simpa [e, hrot] using hepos0
  have hfpos : 0 < f := by simpa [f] using hfpos0

  have hγ : 2 ≤ γ := by
    rw [sig_rotate A B P, sig_rotate B P A,
      abs_of_pos hγpos] at hABPmin
    simpa [γ] using hABPmin
  have ha : 2 ≤ a := by
    rw [sig_rotate B P Q, sig_swap P Q B, abs_neg,
      abs_of_pos hapos] at hBPQmin
    simpa [a] using hBPQmin
  have hb : 2 ≤ b := by
    rw [sig_rotate C P Q, abs_of_pos hbpos] at hCPQmin
    simpa [b] using hCPQmin
  have hc : 2 ≤ c := by
    rw [sig_rotate B C Q, sig_rotate C Q B,
      abs_of_pos hcpos] at hBCQmin
    simpa [c] using hBCQmin
  have hd : 2 ≤ d := by
    rw [sig_rotate C P R, sig_swap P R C, abs_neg,
      abs_of_pos hdpos] at hCPRmin
    simpa [d] using hCPRmin
  have he : 2 ≤ e := by
    rw [sig_rotate A P R, abs_of_pos hepos] at hAPRmin
    simpa [e] using hAPRmin
  have hf : 2 ≤ f := by
    rw [sig_rotate A C R, sig_rotate C R A, sig_swap R A C,
      abs_neg, abs_of_pos hfpos] at hACRmin
    simpa [f] using hACRmin
  have hD : 2 ≤ |D| := by
    simpa [D] using hPQRmin

  have hfanP : α + β + γ = sig A B C := by
    simpa [α, β, γ] using fan_sum P A B C
  have hfanQ : α = a + b + c := by
    have h := fan_cell_sum P B C Q
    dsimp [α, a, b, c]
    linarith
  have hfanR : β = d + e + f := by
    have h := fan_cell_sum P C A R
    dsimp [β, d, e, f]
    linarith
  have hid : α * β * D =
      a * d * β + b * e * α - b * d * γ := by
    simpa [α, β, γ, a, b, d, e, D] using
      adjacent_fan_product_identity A B C P Q R

  constructor
  · have hmain := adjacent_fan_surcharge_part1_numeric
      ha hb hc hd he hf hγ hfanQ hfanR hid hD
    linarith
  · intro hγsix
    have hmain := adjacent_fan_surcharge_part2_numeric
      ha hb hc hd he hf hγsix hfanQ hfanR hid hD
    linarith

/-- TH8 Lemma 2, part 1, in ordinary-area normalization. -/
theorem th8_lemma2_part1 {A B C P Q R : ℝ × ℝ}
    (hABC : 0 < sig A B C)
    (hP : InTriStrict P A B C)
    (hQ : InTriStrict Q P B C)
    (hR : InTriStrict R P C A)
    (hmin : SixPointMinAreaOne A B C P Q R) :
    (17 : ℝ) / 2 ≤ sig A B C / 2 := by
  have h := (th8_lemma2_doubled_bounds hABC hP hQ hR hmin).1
  linarith

/-- TH8 Lemma 2, part 2, in ordinary-area normalization. -/
theorem th8_lemma2_part2 {A B C P Q R : ℝ × ℝ}
    (hABC : 0 < sig A B C)
    (hP : InTriStrict P A B C)
    (hQ : InTriStrict Q P B C)
    (hR : InTriStrict R P C A)
    (hmin : SixPointMinAreaOne A B C P Q R)
    (hγ : (3 : ℝ) ≤ sig P A B / 2) :
    (21 : ℝ) / 2 ≤ sig A B C / 2 := by
  have hγsix : 6 ≤ sig P A B := by linarith
  have h :=
    (th8_lemma2_doubled_bounds hABC hP hQ hR hmin).2 hγsix
  linarith

end Heilbronn8.TriHull
