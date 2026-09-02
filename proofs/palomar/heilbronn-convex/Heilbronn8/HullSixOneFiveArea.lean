import Heilbronn8.HullSixOneFiveScalar

/-!
# A universal area floor for the hull-six `1 + 5` scalar data

The crossing theorem in `HullSixOneFiveScalar` supplies the extra quarter in
the isolated line level.  To turn that quarter into the target hull-area
bound, one also needs the four lower-chain fan areas to sum to at least
`33 / 4`.  This file proves that missing inequality from the scalar floors and
ears alone.

The only hard peak is `b₂ < b₃ ≥ b₄`.  After normalizing by `b₃`, a
short elimination reduces the contrary assumption to positivity of one cubic
on `[0,17/4]`.  Three rational interval identities certify that positivity.
-/

namespace Heilbronn8

set_option maxHeartbeats 1000000

namespace HullSixOneFiveData

private theorem central_area_excess_normalized
    (h x y z w X Y Z W : ℝ)
    (hh : 0 < h)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hW : 0 ≤ W)
    (hleft : X + Y ≤ 1 - h) (hright : Z + W ≤ 1 - h)
    (hear₁ : 1 ≤ (1 + y) * X - x * Y)
    (hear₂ : 1 ≤ (1 + y) * Z + (1 + z) * Y)
    (hear₃ : 1 ≤ (1 + z) * W - w * Z)
    (hWcap : W ≤ w * h)
    (hsum : x + y + z + w ≤ 17 / 4) : False := by
  have honeY : 0 ≤ 1 + y := by linarith
  have honeZ : 0 ≤ 1 + z := by linarith
  have hXcap : X ≤ 1 - h - Y := by linarith
  have hXscaled : (1 + y) * X ≤ (1 + y) * (1 - h - Y) :=
    mul_le_mul_of_nonneg_left hXcap honeY
  have hxY : 0 ≤ x * Y := mul_nonneg hx hY
  have hUy : (1 + y) * h + Y + y * Y ≤ y := by
    nlinarith only [hear₁, hXscaled, hxY]
  have hypos : 0 < y := by
    by_contra hn
    have hyzero : y = 0 := le_antisymm (le_of_not_gt hn) hy
    rw [hyzero] at hUy
    nlinarith only [hUy, hh, hY]

  have hwpos : 0 < w := by
    by_contra hn
    have hwzero : w = 0 := le_antisymm (le_of_not_gt hn) hw
    subst w
    have hWzero : W = 0 := by nlinarith only [hWcap, hW]
    subst W
    norm_num at hear₃

  have hWscaled : (1 + z) * W ≤ (1 + z) * (w * h) :=
    mul_le_mul_of_nonneg_left hWcap honeZ
  have hrightEar : 1 ≤ w * ((1 + z) * h - Z) := by
    nlinarith only [hear₃, hWscaled]
  have hrightEarY := mul_le_mul_of_nonneg_left hrightEar honeY
  have hmiddleW :=
    mul_le_mul_of_nonneg_left hear₂ (le_of_lt hwpos)
  have hAlower :
      1 + y + w ≤ w * (1 + z) * ((1 + y) * h + Y) := by
    nlinarith only [hrightEarY, hmiddleW]

  have hWright : W ≤ 1 - h - Z := by linarith
  have hWrightScaled : (1 + z) * W ≤ (1 + z) * (1 - h - Z) :=
    mul_le_mul_of_nonneg_left hWright honeZ
  have hZupper :
      (1 + z + w) * Z ≤ z - (1 + z) * h := by
    nlinarith only [hear₃, hWrightScaled]
  have hE : 0 ≤ 1 + z + w := by linarith
  have hmiddleE := mul_le_mul_of_nonneg_left hear₂ hE
  have hZupperY := mul_le_mul_of_nonneg_left hZupper honeY
  have hVupper :
      (1 + z) * ((1 + y) * h - (1 + z + w) * Y) ≤
        y * z - 1 - w := by
    nlinarith only [hZupperY, hmiddleE]
  have hVupperW :=
    mul_le_mul_of_nonneg_left hVupper (le_of_lt hwpos)

  let G := 1 + y + 2 * w + w ^ 2 - w * y * z
  have hYlower :
      G ≤ w * (1 + z) * (2 + z + w) * Y := by
    dsimp [G]
    nlinarith only [hAlower, hVupperW]

  have hwz : 0 ≤ w * (1 + z) :=
    mul_nonneg (le_of_lt hwpos) honeZ
  have hUyScaled := mul_le_mul_of_nonneg_left hUy hwz
  have hYupper :
      w * (1 + z) * y * Y ≤
        w * (1 + z) * y - (1 + y + w) := by
    nlinarith only [hAlower, hUyScaled]
  have hyYlower := mul_le_mul_of_nonneg_left hYlower hy
  have hfactor : 0 ≤ 2 + z + w := by linarith
  have hYupperScaled := mul_le_mul_of_nonneg_left hYupper hfactor

  let N :=
    w * (2 + z + w) + (1 + y) * (2 + y + z + w) -
      y * z * w * (3 + y + z + w)
  have hNidentity :
      N = y * G - (2 + z + w) *
        (w * (1 + z) * y - (1 + y + w)) := by
    dsimp [N, G]
    ring
  have hNnonpos : N ≤ 0 := by
    rw [hNidentity]
    nlinarith only [hyYlower, hYupperScaled]

  let r := y + w
  let p := y * w
  let T := 1 + r - p * (3 + r + z)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hpbound : 4 * p ≤ r ^ 2 := by
    dsimp [p, r]
    nlinarith only [sq_nonneg (y - w)]
  have hrz : r + z ≤ 17 / 4 := by
    dsimp [r]
    linarith only [hsum, hx]
  have hNform :
      N = 2 + 3 * r + r ^ 2 - p + z * T := by
    dsimp [N, r, p, T]
    ring

  have hNpos : 0 < N := by
    by_cases hT : 0 ≤ T
    · have hzT : 0 ≤ z * T := mul_nonneg hz hT
      rw [hNform]
      nlinarith only [hpbound, hzT, hr, sq_nonneg r]
    · have hTneg : T < 0 := lt_of_not_ge hT
      let q₀ := 17 / 4 - r
      let T₀ := 1 + r - (r ^ 2 / 4) * (29 / 4)
      have hq₀ : 0 ≤ q₀ := by dsimp [q₀]; linarith only [hrz, hz]
      have hzq₀ : z ≤ q₀ := by dsimp [q₀]; linarith only [hrz]
      have hpupper : p ≤ r ^ 2 / 4 := by nlinarith only [hpbound]
      have harg : 0 ≤ 3 + r + z := by linarith
      have hargUpper : 3 + r + z ≤ 29 / 4 := by
        linarith only [hrz]
      have hmul₀ : p * (3 + r + z) ≤ (r ^ 2 / 4) * (3 + r + z) :=
        mul_le_mul_of_nonneg_right hpupper harg
      have hrSquare : 0 ≤ r ^ 2 / 4 := by positivity
      have hmul₁ : (r ^ 2 / 4) * (3 + r + z) ≤
          (r ^ 2 / 4) * (29 / 4) :=
        mul_le_mul_of_nonneg_left hargUpper hrSquare
      have hT₀le : T₀ ≤ T := by
        dsimp [T₀, T]
        linarith only [hmul₀, hmul₁]
      have hT₀neg : T₀ < 0 := lt_of_le_of_lt hT₀le hTneg
      have hqT : q₀ * T ≤ z * T :=
        mul_le_mul_of_nonpos_right hzq₀ (le_of_lt hTneg)
      have hqT₀ : q₀ * T₀ ≤ q₀ * T :=
        mul_le_mul_of_nonneg_left hT₀le hq₀
      let L := 2 + 3 * r + 3 / 4 * r ^ 2 + q₀ * T₀
      have hLleN : L ≤ N := by
        rw [hNform]
        dsimp [L]
        nlinarith only [hpbound, hqT, hqT₀]
      let f := 116 * r ^ 3 - 509 * r ^ 2 + 400 * r + 400
      have hLf : 64 * L = f := by
        dsimp [L, q₀, T₀, f]
        ring
      have hrUpper : r ≤ 17 / 4 := by linarith only [hrz, hz]
      have hfpos : 0 < f := by
        by_cases hrTwo : r ≤ 2
        · have hsq : 0 ≤ 116 * r * (r - 2) ^ 2 := by positivity
          have hlinear : 0 ≤ (2 - r) * (45 * r + 154) := by
            exact mul_nonneg (sub_nonneg.mpr hrTwo) (by nlinarith only [hr])
          have hid : f = 116 * r * (r - 2) ^ 2 + 92 +
              (2 - r) * (45 * r + 154) := by
            dsimp [f]
            ring
          rw [hid]
          positivity
        · have hrTwo' : 2 < r := lt_of_not_ge hrTwo
          by_cases hrThree : r ≤ 3
          · let t := r - 5 / 2
            have htlo : -1 / 2 ≤ t := by dsimp [t]; linarith
            have hthi : t ≤ 1 / 2 := by dsimp [t]; linarith
            have hcoef : 0 ≤ 361 + 116 * t := by linarith only [htlo]
            have hquad : 0 ≤ t ^ 2 * (361 + 116 * t) :=
              mul_nonneg (sq_nonneg t) hcoef
            have hid : f = 125 / 4 + 30 * t +
                t ^ 2 * (361 + 116 * t) := by
              dsimp [f, t]
              ring
            rw [hid]
            nlinarith only [htlo, hquad]
          · let t := r - 3
            have ht : 0 < t := by dsimp [t]; linarith
            have hid : f = 151 + 478 * t + 535 * t ^ 2 +
                116 * t ^ 3 := by
              dsimp [f, t]
              ring
            rw [hid]
            positivity
      have hLpos : 0 < L := by nlinarith only [hLf, hfpos]
      exact lt_of_lt_of_le hLpos hLleN
  exact (not_lt_of_ge hNnonpos) hNpos

/-- The central peak `b₂ < b₃ ≥ b₄` already forces a strict
`33 / 4` lower bound for the four fan areas. -/
private theorem area_gt_thirty_three_fourths_of_central
    (D : HullSixOneFiveData)
    (hd₂ : D.b₂ - D.b₃ < 0)
    (hd₃ : 0 ≤ D.b₃ - D.b₄)
    (hd₄ : 0 ≤ D.b₄ - D.b₅) :
    33 / 4 < D.area := by
  by_contra hn
  have harea : D.area ≤ 33 / 4 := le_of_not_gt hn
  have hd₁ : D.b₁ - D.b₂ < 0 := by
    by_contra hn₁
    have hd₁' : 0 ≤ D.b₁ - D.b₂ := le_of_not_gt hn₁
    have h₀ : D.a₁ * (D.b₂ - D.b₃) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith [D.ha₁]) (le_of_lt hd₂)
    have h₁ : 0 ≤ D.a₂ * (D.b₁ - D.b₂) :=
      mul_nonneg (by linarith [D.ha₂]) hd₁'
    nlinarith [D.ear₂, D.hb₂]
  let B := D.b₃
  let h := 1 / B
  let x := D.a₁ - 1
  let y := D.a₂ - 1
  let z := D.a₃ - 1
  let w := D.a₄ - 1
  let X := (D.b₂ - D.b₁) / B
  let Y := (D.b₃ - D.b₂) / B
  let Z := (D.b₃ - D.b₄) / B
  let W := (D.b₄ - D.b₅) / B
  have hB : 0 < B := by dsimp [B]; linarith [D.hb₃]
  have hh : 0 < h := one_div_pos.2 hB
  have hx : 0 ≤ x := by dsimp [x]; linarith [D.ha₁]
  have hy : 0 ≤ y := by dsimp [y]; linarith [D.ha₂]
  have hz : 0 ≤ z := by dsimp [z]; linarith [D.ha₃]
  have hw : 0 ≤ w := by dsimp [w]; linarith [D.ha₄]
  have hX : 0 ≤ X := by
    dsimp [X]
    exact div_nonneg (by linarith [hd₁]) (le_of_lt hB)
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact div_nonneg (by linarith [hd₂]) (le_of_lt hB)
  have hZ : 0 ≤ Z := by
    dsimp [Z]
    exact div_nonneg hd₃ (le_of_lt hB)
  have hW : 0 ≤ W := by
    dsimp [W]
    exact div_nonneg hd₄ (le_of_lt hB)
  have hleft : X + Y ≤ 1 - h := by
    rw [show X + Y = (D.b₃ - D.b₁) / B by
      dsimp [X, Y]
      ring]
    rw [show 1 - h = (B - 1) / B by
      dsimp [h]
      field_simp [ne_of_gt hB] <;> ring]
    exact (div_le_div_iff_of_pos_right hB).2
      (by dsimp [B]; linarith [D.hb₁])
  have hright : Z + W ≤ 1 - h := by
    rw [show Z + W = (D.b₃ - D.b₅) / B by
      dsimp [Z, W]
      ring]
    rw [show 1 - h = (B - 1) / B by
      dsimp [h]
      field_simp [ne_of_gt hB] <;> ring]
    exact (div_le_div_iff_of_pos_right hB).2
      (by dsimp [B]; linarith [D.hb₅])
  have hear₁ : 1 ≤ (1 + y) * X - x * Y := by
    rw [show (1 + y) * X - x * Y =
        (D.a₂ * (D.b₂ - D.b₁) -
          (D.a₁ - 1) * (D.b₃ - D.b₂)) / B by
      dsimp [x, y, X, Y]
      field_simp [ne_of_gt hB] <;> ring]
    apply (le_div_iff₀ hB).2
    dsimp [B]
    nlinarith [D.ear₂]
  have hear₂ : 1 ≤ (1 + y) * Z + (1 + z) * Y := by
    rw [show (1 + y) * Z + (1 + z) * Y =
        (D.a₂ * (D.b₃ - D.b₄) +
          D.a₃ * (D.b₃ - D.b₂)) / B by
      dsimp [y, z, Y, Z]
      field_simp [ne_of_gt hB] <;> ring]
    apply (le_div_iff₀ hB).2
    simpa [B] using D.ear₃
  have hear₃ : 1 ≤ (1 + z) * W - w * Z := by
    rw [show (1 + z) * W - w * Z =
        (D.a₃ * (D.b₄ - D.b₅) -
          (D.a₄ - 1) * (D.b₃ - D.b₄)) / B by
      dsimp [z, w, Z, W]
      field_simp [ne_of_gt hB] <;> ring]
    apply (le_div_iff₀ hB).2
    dsimp [B]
    nlinarith [D.ear₄]
  have hWcap : W ≤ w * h := by
    rw [show W = (D.b₄ - D.b₅) / B by rfl]
    rw [show w * h = (D.a₄ - 1) / B by
      dsimp [w, h]
      field_simp [ne_of_gt hB] <;> ring]
    exact (div_le_div_iff_of_pos_right hB).2
      (by linarith [D.hc₄])
  have hsum : x + y + z + w ≤ 17 / 4 := by
    dsimp [x, y, z, w]
    dsimp [area] at harea
    linarith only [harea]
  exact central_area_excess_normalized h x y z w X Y Z W
    hh hx hy hz hw hX hY hZ hW hleft hright hear₁ hear₂ hear₃
      hWcap hsum

/-- Every endpoint-normalized `1 + 5` scalar package has four-fan area at
least `33 / 4`.  The endpoint-order premise matches the crossing theorem's
public interface; the stronger normalized central argument does not use it. -/
theorem area_ge_thirty_three_fourths
    (D : HullSixOneFiveData) (_horder : D.b₅ ≤ D.b₁) :
    33 / 4 ≤ D.area := by
  by_cases hd₂ : 0 ≤ D.b₂ - D.b₃
  · have hten := D.area_ge_ten_of_d₂_nonneg hd₂
    linarith
  · have hd₂' : D.b₂ - D.b₃ < 0 := lt_of_not_ge hd₂
    by_cases hd₃ : 0 ≤ D.b₃ - D.b₄
    · by_cases hd₄ : 0 ≤ D.b₄ - D.b₅
      · exact le_of_lt
          (D.area_gt_thirty_three_fourths_of_central hd₂' hd₃ hd₄)
      · have hd₄' : D.b₄ - D.b₅ < 0 := lt_of_not_ge hd₄
        have hten := D.area_ge_ten_of_d₄_neg hd₄'
        linarith
    · have hd₃' : D.b₃ - D.b₄ < 0 := lt_of_not_ge hd₃
      by_cases hd₄ : 0 ≤ D.b₄ - D.b₅
      · have hlarge := D.area_ge_seventeen_halves_of_peak_b₄ hd₃' hd₄
        linarith
      · have hd₄' : D.b₄ - D.b₅ < 0 := lt_of_not_ge hd₄
        have hten := D.area_ge_ten_of_d₄_neg hd₄'
        linarith

/-- Complete scalar cap accounting for the `1 + 5` branch.

`leftCap` and `rightCap` are the two transition-edge fan areas which are not
stored in `D`.  In geometry the normalized hull area is exactly

`D.area + D.b₅ + leftCap + rightCap + u`.

Above `17/2` the five unit floors already reach `25/2`.  Below `17/2`, the
crossing theorem upgrades `u` from one to `5/4`, while
`area_ge_thirty_three_fourths` supplies the complementary quarter. -/
theorem hullExpression_ge_twenty_five_halves
    (D : HullSixOneFiveData)
    (horder : D.b₅ ≤ D.b₁)
    (k l : Fin 4) (hkl : k ≤ l)
    (u leftCap rightCap : ℝ)
    (hu : 1 ≤ u) (hleftCap : 1 ≤ leftCap)
    (hrightCap : 1 ≤ rightCap)
    (hcrossA : D.adjacentSum k ≤ u * D.aAt k)
    (hcrossC : D.adjacentSum l ≤ u * D.cAt l) :
    25 / 2 ≤ D.area + D.b₅ + leftCap + rightCap + u := by
  by_cases harea : D.area < 17 / 2
  · have huStrong := D.crossingParameter_ge_five_fourths
      horder harea k l hkl u hcrossA hcrossC
    have hfan := D.area_ge_thirty_three_fourths horder
    linarith [D.hb₅]
  · have hfan : 17 / 2 ≤ D.area := le_of_not_gt harea
    linarith [D.hb₅]

private def reverseFinFour (i : Fin 4) : Fin 4 :=
  ⟨3 - i.val, by omega⟩

private lemma reverseFinFour_antitone (k l : Fin 4) (hkl : k ≤ l) :
    reverseFinFour l ≤ reverseFinFour k := by
  change 3 - l.val ≤ 3 - k.val
  omega

@[simp] private lemma reverse_aAt_reverseFinFour
    (D : HullSixOneFiveData) (i : Fin 4) :
    D.reverse.aAt (reverseFinFour i) = D.cAt i := by
  fin_cases i <;>
    simp [reverseFinFour, reverse, aAt, cAt] <;> ring

@[simp] private lemma reverse_cAt_reverseFinFour
    (D : HullSixOneFiveData) (i : Fin 4) :
    D.reverse.cAt (reverseFinFour i) = D.aAt i := by
  fin_cases i <;>
    simp [reverseFinFour, reverse, aAt, cAt] <;> ring

@[simp] private lemma reverse_adjacentSum_reverseFinFour
    (D : HullSixOneFiveData) (i : Fin 4) :
    D.reverse.adjacentSum (reverseFinFour i) = D.adjacentSum i := by
  fin_cases i <;>
    simp [reverseFinFour, reverse, adjacentSum] <;> ring

/-- Order-free form of the scalar cap closure.  If the stored endpoint order
is wrong, reverse the lower chain and exchange the two interior fan bases.
The crossed indices become `3-l ≤ 3-k`, and
`reverse.area + reverse.b₅ = area + b₅`, so the hull expression itself is
unchanged. -/
theorem hullExpression_ge_twenty_five_halves_orderFree
    (D : HullSixOneFiveData)
    (k l : Fin 4) (hkl : k ≤ l)
    (u leftCap rightCap : ℝ)
    (hu : 1 ≤ u) (hleftCap : 1 ≤ leftCap)
    (hrightCap : 1 ≤ rightCap)
    (hcrossA : D.adjacentSum k ≤ u * D.aAt k)
    (hcrossC : D.adjacentSum l ≤ u * D.cAt l) :
    25 / 2 ≤ D.area + D.b₅ + leftCap + rightCap + u := by
  by_cases horder : D.b₅ ≤ D.b₁
  · exact D.hullExpression_ge_twenty_five_halves horder
      k l hkl u leftCap rightCap hu hleftCap hrightCap hcrossA hcrossC
  · let R := D.reverse
    let k' := reverseFinFour l
    let l' := reverseFinFour k
    have horderR : R.b₅ ≤ R.b₁ := by
      dsimp [R, reverse]
      exact (lt_of_not_ge horder).le
    have hklR : k' ≤ l' := by
      dsimp [k', l']
      exact reverseFinFour_antitone k l hkl
    have hcrossAR : R.adjacentSum k' ≤ u * R.aAt k' := by
      dsimp only [R, k']
      rw [reverse_adjacentSum_reverseFinFour,
        reverse_aAt_reverseFinFour]
      exact hcrossC
    have hcrossCR : R.adjacentSum l' ≤ u * R.cAt l' := by
      dsimp only [R, l']
      rw [reverse_adjacentSum_reverseFinFour,
        reverse_cAt_reverseFinFour]
      exact hcrossA
    have hbound := R.hullExpression_ge_twenty_five_halves horderR
      k' l' hklR u leftCap rightCap hu hleftCap hrightCap hcrossAR hcrossCR
    have hinvariant : R.area + R.b₅ = D.area + D.b₅ := by
      dsimp [R]
      rw [reverse_area]
      simp [reverse]
    linarith only [hbound, hinvariant]

end HullSixOneFiveData

end Heilbronn8
