import Heilbronn8.Survivors.Join.HullSixThreeThreeP111Q223Q233ScalarAMGM

/-!
# Raw scalar reduction for the `p = 111`, `q = 223` cell

The geometry adapter supplies six normalized fan sectors, four consecutive
slope gaps, the lower ear, and the retained cross-chord floor.  The proof
packages the six signed floors as nonnegative slacks.  Three exact identities
then reduce the full fan sum to `hullSixThreeThreeP111Q223Phi`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

/-- Coordinate-level `q = 223` reduction.  All divisions occur only by the
positive line heights. -/
theorem hullSixThreeThreeP111Q223_raw_scalar
    {H a b c d e f A B C D E F X00 TL g1 g2 g3 g4 : ℝ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c)
    (hd1 : 1 ≤ d) (he1 : 1 ≤ e) (hf1 : 1 ≤ f)
    (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hX00 : 1 ≤ X00) (hTL : 1 ≤ TL)
    (hEp : 1 ≤ A + a - b)
    (hY12neg : b + f + 1 ≤ b * f * (g2 + g3 + g4))
    (hY22pos : 1 ≤ c + f - c * f * (g3 + g4))
    (hX21 : 1 ≤ c * e * g3)
    (hY01 :
      e * A / b + a * e * B / (b * c) + a * e * g3 ≤ a + e - 1)
    (hAdef : A = a * b * g1)
    (hBdef : B = b * c * g2)
    (hFdef : F = a * f * (g1 + g2 + g3 + g4))
    (hLowerEar :
      D + E = TL + (d / a) * F + (f / a) * X00)
    (hH : H = A + B + C + D + E + F) :
    (25 : ℝ) / 2 < H := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hf : 0 < f := lt_of_lt_of_le zero_lt_one hf1

  let ep : ℝ := A + a - b - 1
  let ym : ℝ := b * f * (g2 + g3 + g4) - b - f - 1
  let yp : ℝ := c + f - c * f * (g3 + g4) - 1
  let xc : ℝ := C - 1
  let tl : ℝ := TL - 1
  let x0 : ℝ := X00 - 1

  have hep : 0 ≤ ep := by
    dsimp [ep]
    linarith
  have hym : 0 ≤ ym := by
    dsimp [ym]
    linarith
  have hyp : 0 ≤ yp := by
    dsimp [yp]
    linarith
  have hxc : 0 ≤ xc := by
    dsimp [xc]
    linarith
  have htl : 0 ≤ tl := by
    dsimp [tl]
    linarith
  have hx0 : 0 ≤ x0 := by
    dsimp [x0]
    linarith

  let G : ℝ := (a + f) * (1 + 1 / b)
  let U : ℝ := A + B + C
  let L : ℝ := D + E
  let U0 : ℝ := 2 - a + c + (b + c) / f
  let L0 : ℝ := 1 + (d / a) * F + f / a

  have hFslack :
      F - G = (f / b) * ep + (a / b) * ym := by
    dsimp [G, ep, ym]
    rw [hAdef, hFdef]
    field_simp [hb.ne']
    <;> ring
  have hUslack :
      U - U0 = ep + (c / f) * ym + (b / f) * yp + xc := by
    dsimp [U, U0, ep, ym, yp, xc]
    rw [hBdef]
    field_simp [hf.ne']
    <;> ring
  have hLslack :
      L - L0 = tl + (f / a) * x0 := by
    dsimp [L, L0, tl, x0]
    rw [hLowerEar]
    ring

  have hFextra :
      0 ≤ (f / b) * ep + (a / b) * ym := by
    exact add_nonneg
      (mul_nonneg (by positivity) hep)
      (mul_nonneg (by positivity) hym)
  have hUextra :
      0 ≤ ep + (c / f) * ym + (b / f) * yp + xc := by
    positivity
  have hLextra : 0 ≤ tl + (f / a) * x0 := by
    positivity
  have hGF : G ≤ F := by linarith
  have hU0U : U0 ≤ U := by linarith
  have hL0L : L0 ≤ L := by linarith

  have hGpos : 0 < G := by
    dsimp [G]
    positivity
  have hFnonneg : 0 ≤ F := le_trans (le_of_lt hGpos) hGF
  have hda : 1 / a ≤ d / a :=
    (div_le_div_iff_of_pos_right ha).2 hd1
  have hscaleD :
      (1 + 1 / a) * F ≤ (1 + d / a) * F := by
    apply mul_le_mul_of_nonneg_right _ hFnonneg
    linarith
  have hscaleG :
      (1 + 1 / a) * G ≤ (1 + 1 / a) * F := by
    exact mul_le_mul_of_nonneg_left hGF (by positivity)

  have hHsum : H = U + L + F := by
    dsimp [U, L]
    linarith
  have hRawLower : U0 + L0 + F ≤ H := by
    rw [hHsum]
    linarith
  have hPhiLower :
      hullSixThreeThreeP111Q223Phi a b c f ≤ H := by
    have hCore :
        U0 + 1 + f / a + (1 + 1 / a) * G ≤ H := by
      dsimp [L0] at hRawLower
      nlinarith [hscaleD, hscaleG]
    have hPhiIdentity :
        hullSixThreeThreeP111Q223Phi a b c f =
          U0 + 1 + f / a + (1 + 1 / a) * G := by
      unfold hullSixThreeThreeP111Q223Phi
      dsimp [U0, G]
      field_simp [ha.ne', hb.ne', hf.ne']
      <;> ring
    rw [hPhiIdentity]
    exact hCore

  have hA : b - a + 1 ≤ A := by linarith
  have hheight : c ≤ a * (c - 1) :=
    hullSixThreeThreeP111Q223_height
      ha hb hc he hA hB hX21 hY01
  exact hullSixThreeThreeP111Q223_phi_finish
    ha hb hc hf hheight hPhiLower

end Heilbronn8
