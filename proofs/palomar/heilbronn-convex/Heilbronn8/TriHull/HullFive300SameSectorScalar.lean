import Mathlib

namespace Heilbronn8.TriHull

set_option maxHeartbeats 0

private lemma le_abs_cases {r t : ℝ} (h : r ≤ |t|) :
    r ≤ t ∨ t ≤ -r := by
  by_cases ht : 0 ≤ t
  · left
    simpa [abs_of_nonneg ht] using h
  · right
    have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht'] at h
    linarith

private lemma sameSector_tail
    {L S : ℝ} (hL : 14 ≤ L) (hS : 0 ≤ S)
    (hprod : 2 * (L + 2) ≤ (L - 8) * S) :
    21 ≤ L + S + 2 := by
  have hs : 0 < L - 8 := by linarith
  have hfac : 0 ≤ (L - 12) * (L - 13) :=
    mul_nonneg (by linarith) (by linarith)
  have hmul : 0 ≤ (L - 8) * ((L - 8) + S - 11) := by
    nlinarith
  have hlin : 0 ≤ (L - 8) + S - 11 := by
    by_contra hn
    have hn' : (L - 8) + S - 11 < 0 := lt_of_not_ge hn
    have hneg := mul_neg_of_pos_of_neg hs hn'
    linarith
  linarith

private lemma positive_factor_of_product_nonneg
    {p q : ℝ} (hp : 0 < p) (hpq : 0 ≤ p * q) : 0 ≤ q := by
  by_contra hq
  have hq' : q < 0 := lt_of_not_ge hq
  have := mul_neg_of_pos_of_neg hp hq'
  linarith

/--
Raw floor-two scalar closure for the first ordered same-sector chart.

The local rows are the two subdivisions of one fan sector of area `L`.
The opposite-vertex rows have the scale dictated by
`L * cross = M * x - N * y`; hence a raw triangle floor of two gives
`2 * L ≤ |N * y - M * x|`.
-/
theorem hullFive300_sameSectorScalar_orderOne
    {L M N x y z X Y Z a b c : ℝ}
    (hL0 : 2 ≤ L) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz0 : 2 ≤ z)
    (hX0 : 2 ≤ X) (hY0 : 2 ≤ Y) (hZ0 : 2 ≤ Z)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hsumQ : x + y + z = L) (hsumR : X + Y + Z = L)
    (hX : X = x + a + b) (hY : Y = y - a + c)
    (hZ : Z = z - b - c) (hrel : b * y = a * z + c * x)
    (hcrossQ : 2 * L ≤ |N * y - M * x|)
    (hcrossR : 2 * L ≤ |N * Y - M * X|) :
    21 ≤ L + M + N := by
  have hapos : 0 ≤ a - 2 := by linarith
  have hbpos : 0 < b := by linarith
  have hbnonneg : 0 ≤ b := hbpos.le
  have hcpos : 0 ≤ c - 2 := by linarith
  have hxnonneg : 0 ≤ x := by linarith
  have hynonneg : 0 ≤ y := by linarith
  have hznonneg : 0 ≤ z := by linarith
  have hXnonneg : 0 ≤ X := by linarith
  have hYnonneg : 0 ≤ Y := by linarith

  have hz : b + c + 2 ≤ z := by linarith
  have hax : 2 * z ≤ a * z := by
    have := mul_nonneg hapos hznonneg
    nlinarith
  have hcx : 4 ≤ c * x := by
    have := mul_nonneg hcpos hxnonneg
    nlinarith
  have hby : 2 * b + 12 ≤ b * y := by nlinarith
  have hbx : 2 * b ≤ b * x := by
    have := mul_nonneg hbnonneg (by linarith : 0 ≤ x - 2)
    nlinarith
  have hbz : b * (b + 4) ≤ b * z := by
    have := mul_nonneg hbnonneg (by linarith : 0 ≤ z - (b + 4))
    nlinarith
  have hbsq := sq_nonneg (b - 3)
  have hsumQb := congrArg (fun t : ℝ => b * t) hsumQ
  ring_nf at hsumQb
  have hbL : 0 < b * (L - 14) := by nlinarith [hsumQb]
  have hL : 14 < L := by
    by_contra hn
    have hnonpos : L - 14 ≤ 0 := by linarith
    have := mul_nonpos_of_nonneg_of_nonpos hbnonneg hnonpos
    linarith

  have hxUpper : x ≤ L - 8 := by linarith
  have hyUpper : y ≤ L - 8 := by linarith
  have hdet : y * X - x * Y = a * L := by
    rw [hX, hY, ← hsumQ]
    nlinarith [hrel]

  rcases le_abs_cases hcrossQ with hqPos | hqNeg
  · rcases le_abs_cases hcrossR with hrPos | hrNeg
    · -- Both opposite-vertex determinants have the positive sign.
      let S : ℝ := M + N - 2
      have hS : 0 ≤ S := by dsimp [S]; linarith
      have hMx : 2 * x ≤ M * x := by
        have := mul_nonneg (by linarith : 0 ≤ M - 2) hxnonneg
        nlinarith
      have hNy : 2 * (L + x) ≤ N * y := by nlinarith
      have hyS : 2 * (L + 2) ≤ y * S := by
        have hMy : 2 * y ≤ M * y := by
          have := mul_nonneg (by linarith : 0 ≤ M - 2) hynonneg
          nlinarith
        dsimp [S]
        nlinarith
      have hcompare :=
        mul_nonneg (by linarith : 0 ≤ (L - 8) - y) hS
      have hprod : 2 * (L + 2) ≤ (L - 8) * S := by
        nlinarith
      have htail := sameSector_tail hL.le hS hprod
      dsimp [S] at htail
      linarith
    · -- The signs are opposite in the feasible direction.
      have hmulQ :=
        mul_nonneg hXnonneg (by linarith : 0 ≤ (N * y - M * x) - 2 * L)
      have hmulR :=
        mul_nonneg hxnonneg (by linarith : 0 ≤ (M * X - N * Y) - 2 * L)
      have hdetN := congrArg (fun t : ℝ => N * t) hdet
      ring_nf at hdetN
      have hNaProd : 0 ≤ L * (N * a - 2 * (x + X)) := by
        nlinarith [hdetN]
      have hNa : 2 * (x + X) ≤ N * a := by
        have h := positive_factor_of_product_nonneg (by linarith : 0 < L) hNaProd
        nlinarith
      have hmulQ' :=
        mul_nonneg hYnonneg (by linarith : 0 ≤ (N * y - M * x) - 2 * L)
      have hmulR' :=
        mul_nonneg hynonneg (by linarith : 0 ≤ (M * X - N * Y) - 2 * L)
      have hdetM := congrArg (fun t : ℝ => M * t) hdet
      ring_nf at hdetM
      have hMaProd : 0 ≤ L * (M * a - 2 * (y + Y)) := by
        nlinarith [hdetM]
      have hMa : 2 * (y + Y) ≤ M * a := by
        have h := positive_factor_of_product_nonneg (by linarith : 0 < L) hMaProd
        nlinarith

      have hac : 0 ≤ c * (a + 2) - 2 * a := by
        have hca := mul_nonneg hcpos (by linarith : 0 ≤ a)
        nlinarith
      have hzMulA := mul_nonneg (by linarith : 0 ≤ a)
        (by linarith : 0 ≤ z - (b + c + 2))
      have hcx2 := mul_nonneg (by linarith : 0 ≤ c)
        (by linarith : 0 ≤ x - 2)
      have hbyStrong : a * b + 4 * a ≤ b * y := by
        nlinarith [hzMulA, hcx2]
      have hbx2 : 2 * b ≤ b * x := by
        have := mul_nonneg hbnonneg (by linarith : 0 ≤ x - 2)
        nlinarith
      have hbz2 : b * (b + 4) ≤ b * z := by
        have := mul_nonneg hbnonneg (by linarith : 0 ≤ z - (b + 4))
        nlinarith
      have hLnum : 4 * a ≤ b * (L - a - b - 6) := by
        nlinarith [hsumQb]
      have hXYsum : x + X + y + Y = 2 * x + 2 * y + b + c := by
        linarith [hX, hY]
      have hXYsumB := congrArg (fun t : ℝ => b * t) hXYsum
      ring_nf at hXYsumB
      have hSnum :
          4 * a * b + 16 * a + 2 * b ^ 2 + 12 * b ≤
            a * b * (M + N) := by
        have hNaB := mul_nonneg hbnonneg (by linarith : 0 ≤ N * a - 2 * (x + X))
        have hMaB := mul_nonneg hbnonneg (by linarith : 0 ≤ M * a - 2 * (y + Y))
        have hbx4 : 8 * b ≤ 4 * b * x := by nlinarith
        have hby4 : 4 * a * b + 16 * a ≤ 4 * b * y := by nlinarith
        have hbc2 : 4 * b ≤ 2 * b * c := by
          have := mul_nonneg hbnonneg (by linarith : 0 ≤ c - 2)
          nlinarith
        nlinarith [hXYsumB]
      have hpolyA : 0 ≤ a ^ 2 - 8 * a + 2 * b + 12 := by
        nlinarith [sq_nonneg (a - 4)]
      have hpolyB : 0 ≤ b ^ 2 - 8 * b + 4 * a + 16 := by
        nlinarith [sq_nonneg (b - 4)]
      have habpos : 0 < a * b := mul_pos (by linarith) hbpos
      have htotalProd : 0 ≤ a * b * (L + M + N - 26) := by
        have hLscaled := mul_nonneg (by linarith : 0 ≤ a) (by linarith : 0 ≤ b * (L - a - b - 6) - 4 * a)
        have hpolyAScaled := mul_nonneg hbnonneg hpolyA
        have hpolyBScaled := mul_nonneg (by linarith : 0 ≤ a) hpolyB
        nlinarith
      have htotal : 26 ≤ L + M + N := by
        have h := positive_factor_of_product_nonneg habpos htotalProd
        nlinarith
      linarith
  · rcases le_abs_cases hcrossR with hrPos | hrNeg
    · -- This sign order contradicts the positive ordered minor.
      have hmulQ :=
        mul_nonneg hXnonneg (by linarith : 0 ≤ (M * x - N * y) - 2 * L)
      have hmulR :=
        mul_nonneg hxnonneg (by linarith : 0 ≤ (N * Y - M * X) - 2 * L)
      have hNa : 0 < N * a := mul_pos (by linarith) (by linarith)
      have hdetN := congrArg (fun t : ℝ => N * t) hdet
      ring_nf at hdetN
      have hNaL : 0 < L * (N * a) := mul_pos (by linarith : 0 < L) hNa
      have hLXx : 0 ≤ L * (X + x) :=
        mul_nonneg (by linarith : 0 ≤ L) (by linarith : 0 ≤ X + x)
      nlinarith [hdetN, hNaL, hLXx]
    · -- Both opposite-vertex determinants have the negative sign.
      let S : ℝ := M + N - 2
      have hS : 0 ≤ S := by dsimp [S]; linarith
      have hNy : 2 * y ≤ N * y := by
        have := mul_nonneg (by linarith : 0 ≤ N - 2) hynonneg
        nlinarith
      have hMx : 2 * (L + y) ≤ M * x := by nlinarith
      have hxS : 2 * (L + 2) ≤ x * S := by
        have hNx : 2 * x ≤ N * x := by
          have := mul_nonneg (by linarith : 0 ≤ N - 2) hxnonneg
          nlinarith
        dsimp [S]
        nlinarith
      have hcompare :=
        mul_nonneg (by linarith : 0 ≤ (L - 8) - x) hS
      have hprod : 2 * (L + 2) ≤ (L - 8) * S := by
        nlinarith
      have htail := sameSector_tail hL.le hS hprod
      dsimp [S] at htail
      linarith

/-- Raw floor-two scalar closure for the second ordered same-sector chart. -/
theorem hullFive300_sameSectorScalar_orderTwo
    {L M N x y z X Y Z a b c : ℝ}
    (hL0 : 2 ≤ L) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz0 : 2 ≤ z)
    (hX0 : 2 ≤ X) (hY0 : 2 ≤ Y) (hZ0 : 2 ≤ Z)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hsumQ : x + y + z = L) (hsumR : X + Y + Z = L)
    (hX : X = x + a + b) (hZ : Z = z - a + c)
    (hY : Y = y - b - c) (hrel : b * z = a * y + c * x)
    (hcrossQ : 2 * L ≤ |N * y - M * x|)
    (hcrossR : 2 * L ≤ |N * Y - M * X|) :
    21 ≤ L + M + N := by
  have hbpos : 0 < b := by linarith
  have hbnonneg : 0 ≤ b := hbpos.le
  have hxnonneg : 0 ≤ x := by linarith
  have hynonneg : 0 ≤ y := by linarith
  have hznonneg : 0 ≤ z := by linarith
  have hXnonneg : 0 ≤ X := by linarith
  have hYnonneg : 0 ≤ Y := by linarith

  have hyLower : b + c + 2 ≤ y := by linarith
  have hay : 2 * y ≤ a * y := by
    have := mul_nonneg (by linarith : 0 ≤ a - 2) hynonneg
    nlinarith
  have hcx : 4 ≤ c * x := by
    have := mul_nonneg (by linarith : 0 ≤ c - 2) hxnonneg
    nlinarith
  have hbz : 2 * b + 12 ≤ b * z := by nlinarith
  have hbx : 2 * b ≤ b * x := by
    have := mul_nonneg hbnonneg (by linarith : 0 ≤ x - 2)
    nlinarith
  have hby : b * (b + 4) ≤ b * y := by
    have := mul_nonneg hbnonneg (by linarith : 0 ≤ y - (b + 4))
    nlinarith
  have hbsq := sq_nonneg (b - 3)
  have hsumQb := congrArg (fun t : ℝ => b * t) hsumQ
  ring_nf at hsumQb
  have hbL : 0 < b * (L - 14) := by nlinarith [hsumQb]
  have hL : 14 < L := by
    by_contra hn
    have hnonpos : L - 14 ≤ 0 := by linarith
    have := mul_nonpos_of_nonneg_of_nonpos hbnonneg hnonpos
    linarith

  have hxUpper : x ≤ L - 8 := by linarith
  have hYUpper : Y ≤ L - 8 := by linarith
  have hdet : y * X - x * Y = b * L := by
    rw [hX, hY, ← hsumQ]
    nlinarith [hrel]

  rcases le_abs_cases hcrossQ with hqPos | hqNeg
  · rcases le_abs_cases hcrossR with hrPos | hrNeg
    · let S : ℝ := M + N - 2
      have hS : 0 ≤ S := by dsimp [S]; linarith
      have hMX : 2 * X ≤ M * X := by
        have := mul_nonneg (by linarith : 0 ≤ M - 2) (by linarith : 0 ≤ X)
        nlinarith
      have hNY : 2 * (L + X) ≤ N * Y := by nlinarith
      have hYS : 2 * (L + 2) ≤ Y * S := by
        have hMY : 2 * Y ≤ M * Y := by
          have := mul_nonneg (by linarith : 0 ≤ M - 2) hYnonneg
          nlinarith
        dsimp [S]
        nlinarith
      have hcompare :=
        mul_nonneg (by linarith : 0 ≤ (L - 8) - Y) hS
      have hprod : 2 * (L + 2) ≤ (L - 8) * S := by nlinarith
      have htail := sameSector_tail hL.le hS hprod
      dsimp [S] at htail
      linarith
    · have hmulQ :=
        mul_nonneg hXnonneg (by linarith : 0 ≤ (N * y - M * x) - 2 * L)
      have hmulR :=
        mul_nonneg hxnonneg (by linarith : 0 ≤ (M * X - N * Y) - 2 * L)
      have hdetN := congrArg (fun t : ℝ => N * t) hdet
      ring_nf at hdetN
      have hNbProd : 0 ≤ L * (N * b - 2 * (x + X)) := by
        nlinarith [hdetN]
      have hNb : 2 * (x + X) ≤ N * b := by
        have h := positive_factor_of_product_nonneg (by linarith : 0 < L) hNbProd
        nlinarith
      have hmulQ' :=
        mul_nonneg hYnonneg (by linarith : 0 ≤ (N * y - M * x) - 2 * L)
      have hmulR' :=
        mul_nonneg hynonneg (by linarith : 0 ≤ (M * X - N * Y) - 2 * L)
      have hdetM := congrArg (fun t : ℝ => M * t) hdet
      ring_nf at hdetM
      have hMbProd : 0 ≤ L * (M * b - 2 * (y + Y)) := by
        nlinarith [hdetM]
      have hMb : 2 * (y + Y) ≤ M * b := by
        have h := positive_factor_of_product_nonneg (by linarith : 0 < L) hMbProd
        nlinarith
      have hSnum : 4 * b + 2 * c + 20 ≤ b * (M + N) := by
        nlinarith
      have hLbase : b + c + 6 ≤ L := by linarith
      have hpoly : 0 ≤ b ^ 2 - 9 * b + 2 * c + 20 := by
        nlinarith [sq_nonneg (b - (9 / 2 : ℝ))]
      have hbcp : 0 ≤ b * (c - 2) :=
        mul_nonneg hbnonneg (by linarith)
      have htotalProd : 0 ≤ b * (L + M + N - 21) := by
        have hLscaled :=
          mul_nonneg hbnonneg (by linarith : 0 ≤ L - (b + c + 6))
        nlinarith
      have htotal : 21 ≤ L + M + N := by
        have h := positive_factor_of_product_nonneg hbpos htotalProd
        nlinarith
      exact htotal
  · rcases le_abs_cases hcrossR with hrPos | hrNeg
    · have hmulQ :=
        mul_nonneg hXnonneg (by linarith : 0 ≤ (M * x - N * y) - 2 * L)
      have hmulR :=
        mul_nonneg hxnonneg (by linarith : 0 ≤ (N * Y - M * X) - 2 * L)
      have hNb : 0 < N * b := mul_pos (by linarith) hbpos
      have hdetN := congrArg (fun t : ℝ => N * t) hdet
      ring_nf at hdetN
      have hNbL : 0 < L * (N * b) := mul_pos (by linarith : 0 < L) hNb
      have hLXx : 0 ≤ L * (X + x) :=
        mul_nonneg (by linarith : 0 ≤ L) (by linarith : 0 ≤ X + x)
      nlinarith [hdetN, hNbL, hLXx]
    · let S : ℝ := M + N - 2
      have hS : 0 ≤ S := by dsimp [S]; linarith
      have hNy : 2 * y ≤ N * y := by
        have := mul_nonneg (by linarith : 0 ≤ N - 2) hynonneg
        nlinarith
      have hMx : 2 * (L + y) ≤ M * x := by nlinarith
      have hxS : 2 * (L + 2) ≤ x * S := by
        have hNx : 2 * x ≤ N * x := by
          have := mul_nonneg (by linarith : 0 ≤ N - 2) hxnonneg
          nlinarith
        dsimp [S]
        nlinarith
      have hcompare :=
        mul_nonneg (by linarith : 0 ≤ (L - 8) - x) hS
      have hprod : 2 * (L + 2) ≤ (L - 8) * S := by nlinarith
      have htail := sameSector_tail hL.le hS hprod
      dsimp [S] at htail
      linarith

/--
The two ratio-order orbits in one adapter-facing theorem.  The first
disjunct covers ratio orders `{1,2,4,6}` and the second covers `{3,5}`
after swapping the two interior points and/or the two local sector rays.
-/
theorem hullFive300_sameSectorScalar
    {L M N x y z X Y Z a b c : ℝ}
    (hL0 : 2 ≤ L) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz0 : 2 ≤ z)
    (hX0 : 2 ≤ X) (hY0 : 2 ≤ Y) (hZ0 : 2 ≤ Z)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hsumQ : x + y + z = L) (hsumR : X + Y + Z = L)
    (hcrossQ : 2 * L ≤ |N * y - M * x|)
    (hcrossR : 2 * L ≤ |N * Y - M * X|)
    (hchart :
      (X = x + a + b ∧ Y = y - a + c ∧ Z = z - b - c ∧
        b * y = a * z + c * x) ∨
      (X = x + a + b ∧ Z = z - a + c ∧ Y = y - b - c ∧
        b * z = a * y + c * x)) :
    21 ≤ L + M + N := by
  rcases hchart with hchart | hchart
  · rcases hchart with ⟨hX, hY, hZ, hrel⟩
    exact hullFive300_sameSectorScalar_orderOne hL0 hM hN hx hy hz0 hX0 hY0 hZ0
      ha hb hc hsumQ hsumR hX hY hZ hrel hcrossQ hcrossR
  · rcases hchart with ⟨hX, hZ, hY, hrel⟩
    exact hullFive300_sameSectorScalar_orderTwo hL0 hM hN hx hy hz0 hX0 hY0 hZ0
      ha hb hc hsumQ hsumR hX hZ hY hrel hcrossQ hcrossR

end Heilbronn8.TriHull
