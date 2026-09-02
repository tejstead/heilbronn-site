import Heilbronn8.QuadHull.OrbitIAnalytic
import Heilbronn8.QuadHull.OrbitILowScalar

namespace Heilbronn8.QuadHull

/-!
# Closing the orbit-I cyclic leaf

The high-fan branch is handled in `OrbitIAnalytic`.  This file connects an
actual cyclic fan to the two scalar numerators certified in
`OrbitILowScalar`, including the exact transport to the primed fan when `V`
is the smaller total.
-/

/-- The geometric information used by the low-fan scalar reduction. -/
private structure LowFanGeometry (n D m M : ℝ) where
  Sx : ℝ
  Sj : ℝ
  Tx : ℝ
  Tj : ℝ
  Rx : ℝ
  Rj : ℝ
  Sx_lower : 3 ≤ Sx
  Sj_lower : 1 ≤ Sj
  Sy_lower : 3 ≤ cyclicY n Sx Sj
  Tx_lower : 1 ≤ Tx
  Tj_lower : 3 ≤ Tj
  Ty_lower : 3 ≤ cyclicY n Tx Tj
  Rx_lower : 3 ≤ Rx
  Rj_lower : 3 ≤ Rj
  Ry_lower : 1 ≤ cyclicY n Rx Rj
  Sx_favored : 3 * n + m * Sj ≤ D * Sx
  Tx_favored : n + m * Tj ≤ D * Tx
  Rx_favored : 3 * n + m * Rj ≤ D * Rx
  T_mix : n ≤ m * cyclicY n Tx Tj + M * Tx
  R_mix : n ≤ m * cyclicY n Rx Rj + M * Rx
  central : n ^ 2 ≤ -cyclicDet n Sx Sj Tx Tj Rx Rj

private lemma cyclicDet_central_form
    (n Sx Sj Tx Tj Rx Rj : ℝ) :
    -cyclicDet n Sx Sj Tx Tj Rx Rj =
      n * ((Rj - Sj) * (Rx - Tx) + (Sx - Rx) * (Rj - Tj)) := by
  unfold cyclicDet areaDet cyclicY
  ring

private lemma lowFan_common_upper
    {n D m M : ℝ} (g : LowFanGeometry n D m M)
    (hn0 : 0 < n) (hn9 : n < 9) (hD : 0 < D) (hm0 : 0 ≤ m) :
    4 * D ^ 2 * (g.Rj - g.Sj) * (g.Rx - g.Tx) ≤
      (D * (n - 2) - n - 3 * m) ^ 2 := by
  have hSjUpper : g.Sj ≤ n - 6 := by
    have hSy := g.Sy_lower
    unfold cyclicY at hSy
    linarith [g.Sx_lower]
  have hTxUpper : g.Tx ≤ n - 6 := by
    have hTy := g.Ty_lower
    unfold cyclicY at hTy
    linarith [g.Tj_lower]
  have ha : 0 ≤ g.Rj - g.Sj := by linarith [g.Rj_lower, hSjUpper]
  have hb : 0 ≤ g.Rx - g.Tx := by linarith [g.Rx_lower, hTxUpper]
  have hab :
      D * ((g.Rj - g.Sj) + (g.Rx - g.Tx)) ≤
        D * (n - 2) - n - 3 * m := by
    have hRsum : g.Rj + g.Rx ≤ n - 1 := by
      have hRy := g.Ry_lower
      unfold cyclicY at hRy
      linarith
    have hmT : 3 * m ≤ m * g.Tj := by
      nlinarith [mul_nonneg hm0 (sub_nonneg.mpr g.Tj_lower)]
    have hDT : n + 3 * m ≤ D * g.Tx := by linarith [g.Tx_favored]
    have hleft :
        (g.Rj - g.Sj) + (g.Rx - g.Tx) ≤ n - 2 - g.Tx := by
      linarith [hRsum, g.Sj_lower]
    have hmuld := mul_le_mul_of_nonneg_left hleft hD.le
    nlinarith
  have hab0 : 0 ≤ (g.Rj - g.Sj) + (g.Rx - g.Tx) := by linarith
  have hK0 : 0 ≤ D * (n - 2) - n - 3 * m := by
    nlinarith [mul_nonneg hD.le hab0]
  have hsquare :
      (D * ((g.Rj - g.Sj) + (g.Rx - g.Tx))) ^ 2 ≤
        (D * (n - 2) - n - 3 * m) ^ 2 := by
    have hprod := mul_nonneg
      (sub_nonneg.mpr hab)
      (add_nonneg hK0 (mul_nonneg hD.le hab0))
    nlinarith
  have hfour :
      4 * (g.Rj - g.Sj) * (g.Rx - g.Tx) ≤
        ((g.Rj - g.Sj) + (g.Rx - g.Tx)) ^ 2 := by
    nlinarith [sq_nonneg ((g.Rj - g.Sj) - (g.Rx - g.Tx))]
  have hm := mul_le_mul_of_nonneg_left hfour (sq_nonneg D)
  nlinarith [hm, hsquare]

private lemma lowFan_central_upper
    {n D m M : ℝ} (g : LowFanGeometry n D m M)
    (hn0 : 0 < n) :
    n ≤ (g.Rj - g.Sj) * (g.Rx - g.Tx) +
      (g.Sx - g.Rx) * (g.Rj - g.Tj) := by
  have hc := g.central
  rw [cyclicDet_central_form] at hc
  nlinarith [hc, mul_pos hn0 hn0]

private lemma lowFan_R_difference
    {n D m M : ℝ} (g : LowFanGeometry n D m M)
    (hDm : M = m + (D - n)) (hnD : n ≤ D)
    (hM0 : 0 ≤ M) :
    M * (g.Rj - g.Tj) ≤ M * (n - 3) - D := by
  have hd : 0 ≤ D - n := sub_nonneg.mpr hnD
  have hgain : D - n ≤ (M - m) * cyclicY n g.Rx g.Rj := by
    rw [show M - m = D - n by linarith [hDm]]
    nlinarith [mul_nonneg hd (sub_nonneg.mpr g.Ry_lower)]
  have hDrow : D ≤ M * (g.Rx + cyclicY n g.Rx g.Rj) := by
    nlinarith [g.R_mix, hgain]
  unfold cyclicY at hDrow
  have hT := mul_nonneg hM0 (sub_nonneg.mpr g.Tj_lower)
  nlinarith

private lemma lowFan_T_difference
    {n D m M : ℝ} (g : LowFanGeometry n D m M)
    (hDm : M = m + (D - n)) (hnD : n ≤ D)
    (hM0 : 0 ≤ M) :
    M * (g.Tj - g.Rj) ≤
      M * (n - 3) + 2 * n - 3 * D := by
  have hd : 0 ≤ D - n := sub_nonneg.mpr hnD
  have hgain :
      3 * (D - n) ≤ (M - m) * cyclicY n g.Tx g.Tj := by
    rw [show M - m = D - n by linarith [hDm]]
    nlinarith [mul_nonneg hd (sub_nonneg.mpr g.Ty_lower)]
  have hTrow :
      n + 3 * (D - n) ≤ M * (g.Tx + cyclicY n g.Tx g.Tj) := by
    nlinarith [g.T_mix, hgain]
  unfold cyclicY at hTrow
  have hR := mul_nonneg hM0 (sub_nonneg.mpr g.Rj_lower)
  nlinarith

private lemma lowFan_P1_nonneg
    {n D m M : ℝ} (g : LowFanGeometry n D m M)
    (hn0 : 0 < n) (hn83 : (83 : ℝ) / 10 < n) (hn9 : n < 9)
    (hD : 0 < D) (hnD : n ≤ D) (hm1 : 1 ≤ m)
    (hM : 0 < M) (hDm : M = m + (D - n))
    (hCD : 3 * D - 2 * n ≤ M * (n - 3))
    (hquarter : 4 * M < D) (hTR : g.Tj ≤ g.Rj) :
    0 ≤ orbitILowP1Numerator n D M := by
  have hm0 : 0 ≤ m := by linarith
  have hcommon := lowFan_common_upper g hn0 hn9 hD hm0
  have hcentral := lowFan_central_upper g hn0
  have hRdiff := lowFan_R_difference g hDm hnD hM.le
  let B : ℝ := D * (n - 1) - 6 * n - 3 * M
  let C : ℝ := M * (n - 3) - D
  have hB : 0 ≤ B := by
    have hpos : 0 < D * (n - (31 : ℝ) / 4) :=
      mul_pos hD (by linarith [hn83])
    dsimp [B]
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (sub_nonneg.mpr hnD)]
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith
  have hSupper : g.Sx ≤ n - 4 := by
    have hSy := g.Sy_lower
    unfold cyclicY at hSy
    linarith [g.Sj_lower]
  have hE : D * (g.Sx - g.Rx) ≤ B := by
    have hmR : 3 * m ≤ m * g.Rj := by
      nlinarith [mul_nonneg hm0 (sub_nonneg.mpr g.Rj_lower)]
    have hDS := mul_le_mul_of_nonneg_left hSupper hD.le
    dsimp [B]
    nlinarith [g.Rx_favored]
  have hF : M * (g.Rj - g.Tj) ≤ C := by
    simpa [C] using hRdiff
  have hprod :
      D * M * ((g.Sx - g.Rx) * (g.Rj - g.Tj)) ≤ B * C := by
    by_cases he : 0 ≤ g.Sx - g.Rx
    · have hc : 0 ≤ g.Rj - g.Tj := sub_nonneg.mpr hTR
      have hDE : 0 ≤ D * (g.Sx - g.Rx) := mul_nonneg hD.le he
      have hMF : 0 ≤ M * (g.Rj - g.Tj) := mul_nonneg hM.le hc
      have hp := mul_le_mul hE hF hMF hB
      nlinarith [hp]
    · have he' : g.Sx - g.Rx < 0 := lt_of_not_ge he
      have hc : 0 ≤ g.Rj - g.Tj := sub_nonneg.mpr hTR
      have hleft : D * M * ((g.Sx - g.Rx) * (g.Rj - g.Tj)) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg hD.le hM.le) (mul_nonpos_of_nonpos_of_nonneg he'.le hc)
      exact hleft.trans (mul_nonneg hB hC)
  have hscale : 0 ≤ 4 * D ^ 2 * M :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg D)) hM.le
  have hcentMul := mul_le_mul_of_nonneg_left hcentral hscale
  have hprod4D := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 4 * D)
  dsimp [B, C] at hprod4D hB hC
  rw [show D * (n - 2) - n - 3 * m =
      D * (n + 1) - 4 * n - 3 * M by nlinarith [hDm]] at hcommon
  have hcommonM := mul_le_mul_of_nonneg_left hcommon hM.le
  have htotal :
      4 * D ^ 2 * M * n ≤
        M * (D * (n + 1) - 4 * n - 3 * M) ^ 2 +
          4 * D * ((D * (n - 1) - 6 * n - 3 * M) *
            (M * (n - 3) - D)) := by
    calc
      4 * D ^ 2 * M * n ≤
          4 * D ^ 2 * M *
            ((g.Rj - g.Sj) * (g.Rx - g.Tx) +
              (g.Sx - g.Rx) * (g.Rj - g.Tj)) := hcentMul
      _ = M * (4 * D ^ 2 * (g.Rj - g.Sj) * (g.Rx - g.Tx)) +
          4 * D * (D * M * ((g.Sx - g.Rx) * (g.Rj - g.Tj))) := by ring
      _ ≤ M * (D * (n + 1) - 4 * n - 3 * M) ^ 2 +
          4 * D * ((D * (n - 1) - 6 * n - 3 * M) *
            (M * (n - 3) - D)) := add_le_add hcommonM hprod4D
  unfold orbitILowP1Numerator
  convert sub_nonneg.mpr htotal using 1 <;> ring

private lemma lowFan_P2_nonneg
    {n D m M : ℝ} (g : LowFanGeometry n D m M)
    (hn0 : 0 < n) (hn83 : (83 : ℝ) / 10 < n) (hn9 : n < 9)
    (hD : 0 < D) (hnD : n ≤ D) (hm1 : 1 ≤ m)
    (hM : 0 < M) (hDm : M = m + (D - n))
    (hCD : 3 * D - 2 * n ≤ M * (n - 3))
    (hquarter : 4 * M < D) (hRT : g.Rj ≤ g.Tj) :
    0 ≤ orbitILowP2Numerator n D M := by
  have hm0 : 0 ≤ m := by linarith
  have hcommon := lowFan_common_upper g hn0 hn9 hD hm0
  have hcentral := lowFan_central_upper g hn0
  have hTdiff := lowFan_T_difference g hDm hnD hM.le
  let B : ℝ := D * (n - 3) - 4 * n - M
  let C : ℝ := M * (n - 3) + 2 * n - 3 * D
  have hB : 0 ≤ B := by
    have hpos : 0 < D * (n - (29 : ℝ) / 4) :=
      mul_pos hD (by linarith [hn83])
    dsimp [B]
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sub_nonneg.mpr hnD)]
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hRupper : g.Rx ≤ n - 4 := by
    have hRy := g.Ry_lower
    unfold cyclicY at hRy
    linarith [g.Rj_lower]
  have hE : D * (g.Rx - g.Sx) ≤ B := by
    have hmS : m ≤ m * g.Sj := by
      nlinarith [mul_nonneg hm0 (sub_nonneg.mpr g.Sj_lower)]
    have hDR := mul_le_mul_of_nonneg_left hRupper hD.le
    dsimp [B]
    nlinarith [g.Sx_favored]
  have hF : M * (g.Tj - g.Rj) ≤ C := by
    simpa [C] using hTdiff
  have hprod :
      D * M * ((g.Rx - g.Sx) * (g.Tj - g.Rj)) ≤ B * C := by
    by_cases he : 0 ≤ g.Rx - g.Sx
    · have hc : 0 ≤ g.Tj - g.Rj := sub_nonneg.mpr hRT
      have hDE : 0 ≤ D * (g.Rx - g.Sx) := mul_nonneg hD.le he
      have hMF : 0 ≤ M * (g.Tj - g.Rj) := mul_nonneg hM.le hc
      have hp := mul_le_mul hE hF hMF hB
      nlinarith [hp]
    · have he' : g.Rx - g.Sx < 0 := lt_of_not_ge he
      have hc : 0 ≤ g.Tj - g.Rj := sub_nonneg.mpr hRT
      have hleft : D * M * ((g.Rx - g.Sx) * (g.Tj - g.Rj)) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg hD.le hM.le) (mul_nonpos_of_nonpos_of_nonneg he'.le hc)
      exact hleft.trans (mul_nonneg hB hC)
  have hscale : 0 ≤ 4 * D ^ 2 * M :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg D)) hM.le
  have hcentMul := mul_le_mul_of_nonneg_left hcentral hscale
  have hprod4D := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 4 * D)
  dsimp [B, C] at hprod4D hB hC
  rw [show D * (n - 2) - n - 3 * m =
      D * (n + 1) - 4 * n - 3 * M by nlinarith [hDm]] at hcommon
  have hcommonM := mul_le_mul_of_nonneg_left hcommon hM.le
  have htotal :
      4 * D ^ 2 * M * n ≤
        M * (D * (n + 1) - 4 * n - 3 * M) ^ 2 +
          4 * D * ((D * (n - 3) - 4 * n - M) *
            (M * (n - 3) + 2 * n - 3 * D)) := by
    calc
      4 * D ^ 2 * M * n ≤
          4 * D ^ 2 * M *
            ((g.Rj - g.Sj) * (g.Rx - g.Tx) +
              (g.Sx - g.Rx) * (g.Rj - g.Tj)) := hcentMul
      _ = M * (4 * D ^ 2 * (g.Rj - g.Sj) * (g.Rx - g.Tx)) +
          4 * D * (D * M * ((g.Rx - g.Sx) * (g.Tj - g.Rj))) := by ring
      _ ≤ M * (D * (n + 1) - 4 * n - 3 * M) ^ 2 +
          4 * D * ((D * (n - 3) - 4 * n - M) *
            (M * (n - 3) + 2 * n - 3 * D)) := add_le_add hcommonM hprod4D
  unfold orbitILowP2Numerator
  convert sub_nonneg.mpr htotal using 1 <;> ring

/-! ## Exact transport to the primed fan -/

private lemma cyclicDet_prime_transport
    (U V G Sx Sj Tx Tj Rx Rj : ℝ) (hU : U ≠ 0) :
    cyclicDet V
        (cyclicXNum V G Sx Sj / U) Sj
        (cyclicXNum V G Tx Tj / U) Tj
        (cyclicXNum V G Rx Rj / U) Rj =
      (V ^ 2 / U ^ 2) * cyclicDet U Sx Sj Tx Tj Rx Rj := by
  unfold cyclicDet areaDet cyclicY cyclicXNum
  field_simp [hU]
  ring

private lemma cyclicDet_prime_swapped_transport
    (U V G Sx Sj Tx Tj Rx Rj : ℝ) (hU : U ≠ 0) :
    cyclicDet V
        (cyclicYNum U V G (cyclicY U Sx Sj) Sj / U) Sj
        (cyclicYNum U V G (cyclicY U Rx Rj) Rj / U) Rj
        (cyclicYNum U V G (cyclicY U Tx Tj) Tj / U) Tj =
      (V ^ 2 / U ^ 2) * cyclicDet U Sx Sj Tx Tj Rx Rj := by
  unfold cyclicDet areaDet cyclicY cyclicYNum cyclicW
  field_simp [hU]
  ring

private lemma prime_cyclicY_eq
    (U V G X J : ℝ) (hU : U ≠ 0) :
    cyclicY V (cyclicXNum V G X J / U) J =
      cyclicYNum U V G (cyclicY U X J) J / U := by
  unfold cyclicY cyclicXNum cyclicYNum cyclicW
  field_simp [hU]
  ring

private lemma prime_swapped_cyclicY_eq
    (U V G X J : ℝ) (hU : U ≠ 0) :
    cyclicY V (cyclicYNum U V G (cyclicY U X J) J / U) J =
      cyclicXNum V G X J / U := by
  unfold cyclicY cyclicXNum cyclicYNum cyclicW
  field_simp [hU]
  ring

private lemma prime_central
    {U V G Sx Sj Tx Tj Rx Rj : ℝ}
    (r : CyclicLeaf50tDomain U V G Sx Sj Tx Tj Rx Rj) :
    V ^ 2 ≤
      -cyclicDet V
        (cyclicXNum V G Sx Sj / U) Sj
        (cyclicXNum V G Tx Tj / U) Tj
        (cyclicXNum V G Rx Rj / U) Rj := by
  have hU : 0 < U := by linarith [r.U_lower]
  have hc : U ^ 2 ≤ -cyclicDet U Sx Sj Tx Tj Rx Rj := by
    linarith [r.central]
  have hfac : 0 ≤ V ^ 2 / U ^ 2 := div_nonneg (sq_nonneg V) (sq_nonneg U)
  have hm := mul_le_mul_of_nonneg_left hc hfac
  rw [cyclicDet_prime_transport U V G Sx Sj Tx Tj Rx Rj hU.ne']
  calc
    V ^ 2 = (V ^ 2 / U ^ 2) * U ^ 2 := by field_simp [hU.ne']
    _ ≤ (V ^ 2 / U ^ 2) * (-cyclicDet U Sx Sj Tx Tj Rx Rj) := hm
    _ = -((V ^ 2 / U ^ 2) * cyclicDet U Sx Sj Tx Tj Rx Rj) := by ring

private lemma prime_swapped_central
    {U V G Sx Sj Tx Tj Rx Rj : ℝ}
    (r : CyclicLeaf50tDomain U V G Sx Sj Tx Tj Rx Rj) :
    V ^ 2 ≤
      -cyclicDet V
        (cyclicYNum U V G (cyclicY U Sx Sj) Sj / U) Sj
        (cyclicYNum U V G (cyclicY U Rx Rj) Rj / U) Rj
        (cyclicYNum U V G (cyclicY U Tx Tj) Tj / U) Tj := by
  have hU : 0 < U := by linarith [r.U_lower]
  have hc : U ^ 2 ≤ -cyclicDet U Sx Sj Tx Tj Rx Rj := by
    linarith [r.central]
  have hfac : 0 ≤ V ^ 2 / U ^ 2 := div_nonneg (sq_nonneg V) (sq_nonneg U)
  have hm := mul_le_mul_of_nonneg_left hc hfac
  rw [cyclicDet_prime_swapped_transport U V G Sx Sj Tx Tj Rx Rj hU.ne']
  calc
    V ^ 2 = (V ^ 2 / U ^ 2) * U ^ 2 := by field_simp [hU.ne']
    _ ≤ (V ^ 2 / U ^ 2) * (-cyclicDet U Sx Sj Tx Tj Rx Rj) := hm
    _ = -((V ^ 2 / U ^ 2) * cyclicDet U Sx Sj Tx Tj Rx Rj) := by ring

/-- The same strict cutoff holds for the transported (primed) fan total. -/
theorem CyclicLeaf50tDomain.V_gt_eighty_three_tenths
    {U V G Sx Sj Tx Tj Rx Rj : ℝ}
    (r : CyclicLeaf50tDomain U V G Sx Sj Tx Tj Rx Rj) :
    (83 : ℝ) / 10 < V := by
  have hU : 0 < U := by linarith [r.U_lower]
  have hV : 0 < V := by linarith [r.V_lower]
  have hSx : 3 ≤ cyclicXNum V G Sx Sj / U :=
    (le_div_iff₀ hU).2 (by linarith [r.Sx'_lower])
  have hTx : 1 ≤ cyclicXNum V G Tx Tj / U :=
    (le_div_iff₀ hU).2 (by linarith [r.Tx'_lower])
  have hRx : 3 ≤ cyclicXNum V G Rx Rj / U :=
    (le_div_iff₀ hU).2 (by linarith [r.Rx'_lower])
  have hSy : 3 ≤ cyclicY V (cyclicXNum V G Sx Sj / U) Sj := by
    rw [prime_cyclicY_eq U V G Sx Sj hU.ne']
    exact (le_div_iff₀ hU).2 (by linarith [r.Sy'_lower])
  have hTy : 3 ≤ cyclicY V (cyclicXNum V G Tx Tj / U) Tj := by
    rw [prime_cyclicY_eq U V G Tx Tj hU.ne']
    exact (le_div_iff₀ hU).2 (by linarith [r.Ty'_lower])
  have hRy : 1 ≤ cyclicY V (cyclicXNum V G Rx Rj / U) Rj := by
    rw [prime_cyclicY_eq U V G Rx Rj hU.ne']
    exact (le_div_iff₀ hU).2 (by linarith [r.Ry'_lower])
  have hupper := cyclicDet_div_upper_of_row_lower_bounds
    r.V_lower hSx r.Sj_lower hSy hTx r.Tj_lower hTy
      hRx r.Rj_lower hRy
  have hc := prime_central r
  have hcentral :
      V ≤ -cyclicDet V
        (cyclicXNum V G Sx Sj / U) Sj
        (cyclicXNum V G Tx Tj / U) Tj
        (cyclicXNum V G Rx Rj / U) Rj / V := by
    apply (le_div_iff₀ hV).2
    nlinarith
  have hpoly : 0 ≤ V ^ 2 - 13 * V + 39 := by
    nlinarith [hcentral, hupper]
  by_contra hn
  have hVupper : V ≤ (83 : ℝ) / 10 := le_of_not_gt hn
  have hfactor :
      (V - (83 : ℝ) / 10) * (V - (47 : ℝ) / 10) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (by linarith) (by linarith [r.V_lower])
  nlinarith

private lemma prime_mix
    (U V G X J : ℝ) (hU : 0 < U) (hV : 0 ≤ V)
    (hCD : U ≤ G * cyclicY U X J + cyclicW U V G * X) :
    V ≤
      cyclicW U V G * (cyclicXNum V G X J / U) +
        G * (cyclicYNum U V G (cyclicY U X J) J / U) := by
  rw [show cyclicW U V G * (cyclicXNum V G X J / U) +
      G * (cyclicYNum U V G (cyclicY U X J) J / U) =
      (cyclicW U V G * cyclicXNum V G X J +
        G * cyclicYNum U V G (cyclicY U X J) J) / U by
    field_simp [hU.ne'] <;> ring]
  apply (le_div_iff₀ hU).2
  have hm := mul_le_mul_of_nonneg_left hCD hV
  calc
    V * U ≤ V * (G * cyclicY U X J + cyclicW U V G * X) := hm
    _ = G * cyclicYNum U V G (cyclicY U X J) J +
        cyclicW U V G * cyclicXNum V G X J :=
      (cyclic_CD_transport_R U V G X J).symm
    _ = cyclicW U V G * cyclicXNum V G X J +
        G * cyclicYNum U V G (cyclicY U X J) J := by ring

/-! ## The two orientations -/

private def lowFan_first
    {U V G Sx Sj Tx Tj Rx Rj : ℝ}
    (r : CyclicLeaf50tDomain U V G Sx Sj Tx Tj Rx Rj) :
    LowFanGeometry U V G (cyclicW U V G) where
  Sx := Sx
  Sj := Sj
  Tx := Tx
  Tj := Tj
  Rx := Rx
  Rj := Rj
  Sx_lower := r.Sx_lower
  Sj_lower := r.Sj_lower
  Sy_lower := by linarith [r.Sy_lower]
  Tx_lower := r.Tx_lower
  Tj_lower := r.Tj_lower
  Ty_lower := by linarith [r.Ty_lower]
  Rx_lower := r.Rx_lower
  Rj_lower := r.Rj_lower
  Ry_lower := by linarith [r.Ry_lower]
  Sx_favored := by
    have h := r.Sx'_lower
    unfold cyclicXNum at h
    nlinarith
  Tx_favored := by
    have h := r.Tx'_lower
    unfold cyclicXNum at h
    nlinarith
  Rx_favored := by
    have h := r.Rx'_lower
    unfold cyclicXNum at h
    nlinarith
  T_mix := by linarith [r.CDT]
  R_mix := by linarith [r.CDR]
  central := by linarith [r.central]

private noncomputable def lowFan_second
    {U V G Sx Sj Tx Tj Rx Rj : ℝ}
    (r : CyclicLeaf50tDomain U V G Sx Sj Tx Tj Rx Rj) :
    LowFanGeometry V U (cyclicW U V G) G where
  Sx := cyclicYNum U V G (cyclicY U Sx Sj) Sj / U
  Sj := Sj
  Tx := cyclicYNum U V G (cyclicY U Rx Rj) Rj / U
  Tj := Rj
  Rx := cyclicYNum U V G (cyclicY U Tx Tj) Tj / U
  Rj := Tj
  Sx_lower := by
    have hU : 0 < U := by linarith [r.U_lower]
    exact (le_div_iff₀ hU).2 (by linarith [r.Sy'_lower])
  Sj_lower := r.Sj_lower
  Sy_lower := by
    have hU : 0 < U := by linarith [r.U_lower]
    rw [prime_swapped_cyclicY_eq U V G Sx Sj hU.ne']
    exact (le_div_iff₀ hU).2 (by linarith [r.Sx'_lower])
  Tx_lower := by
    have hU : 0 < U := by linarith [r.U_lower]
    exact (le_div_iff₀ hU).2 (by linarith [r.Ry'_lower])
  Tj_lower := r.Rj_lower
  Ty_lower := by
    have hU : 0 < U := by linarith [r.U_lower]
    rw [prime_swapped_cyclicY_eq U V G Rx Rj hU.ne']
    exact (le_div_iff₀ hU).2 (by linarith [r.Rx'_lower])
  Rx_lower := by
    have hU : 0 < U := by linarith [r.U_lower]
    exact (le_div_iff₀ hU).2 (by linarith [r.Ty'_lower])
  Rj_lower := r.Tj_lower
  Ry_lower := by
    have hU : 0 < U := by linarith [r.U_lower]
    rw [prime_swapped_cyclicY_eq U V G Tx Tj hU.ne']
    exact (le_div_iff₀ hU).2 (by linarith [r.Tx'_lower])
  Sx_favored := by
    have hU : 0 < U := by linarith [r.U_lower]
    have hV : 0 ≤ V := by linarith [r.V_lower]
    have hSy : 3 ≤ cyclicY U Sx Sj := by linarith [r.Sy_lower]
    have hm := mul_le_mul_of_nonneg_left hSy hV
    calc
      3 * V + cyclicW U V G * Sj ≤
          cyclicYNum U V G (cyclicY U Sx Sj) Sj := by
            unfold cyclicYNum
            linarith
      _ = U * (cyclicYNum U V G (cyclicY U Sx Sj) Sj / U) := by
        field_simp [hU.ne']
  Tx_favored := by
    have hU : 0 < U := by linarith [r.U_lower]
    have hV : 0 ≤ V := by linarith [r.V_lower]
    have hRy : 1 ≤ cyclicY U Rx Rj := by linarith [r.Ry_lower]
    have hm := mul_le_mul_of_nonneg_left hRy hV
    calc
      V + cyclicW U V G * Rj ≤
          cyclicYNum U V G (cyclicY U Rx Rj) Rj := by
            unfold cyclicYNum
            linarith
      _ = U * (cyclicYNum U V G (cyclicY U Rx Rj) Rj / U) := by
        field_simp [hU.ne']
  Rx_favored := by
    have hU : 0 < U := by linarith [r.U_lower]
    have hV : 0 ≤ V := by linarith [r.V_lower]
    have hTy : 3 ≤ cyclicY U Tx Tj := by linarith [r.Ty_lower]
    have hm := mul_le_mul_of_nonneg_left hTy hV
    calc
      3 * V + cyclicW U V G * Tj ≤
          cyclicYNum U V G (cyclicY U Tx Tj) Tj := by
            unfold cyclicYNum
            linarith
      _ = U * (cyclicYNum U V G (cyclicY U Tx Tj) Tj / U) := by
        field_simp [hU.ne']
  T_mix := by
    have hU : 0 < U := by linarith [r.U_lower]
    have hV : 0 ≤ V := by linarith [r.V_lower]
    rw [prime_swapped_cyclicY_eq U V G Rx Rj hU.ne']
    exact prime_mix U V G Rx Rj hU hV (by linarith [r.CDR])
  R_mix := by
    have hU : 0 < U := by linarith [r.U_lower]
    have hV : 0 ≤ V := by linarith [r.V_lower]
    rw [prime_swapped_cyclicY_eq U V G Tx Tj hU.ne']
    exact prime_mix U V G Tx Tj hU hV (by linarith [r.CDT])
  central := prime_swapped_central r

private lemma quarter_of_first_target
    {n D M : ℝ} (hn0 : 0 < n) (hn83 : (83 : ℝ) / 10 < n)
    (hD : 0 < D) (hnD : n ≤ D)
    (hTarget : M * (D + 1) < D * ((63 : ℝ) / 5 - n) - 2 * n) :
    4 * M < D := by
  by_contra hnot
  have hDM : D ≤ 4 * M := le_of_not_gt hnot
  have hD1 : 0 ≤ D + 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hDM hD1
  have hneg :
      D ^ 2 + (4 * n - (247 : ℝ) / 5) * D + 8 * n < 0 := by
    nlinarith
  have hbase : 0 < n * (5 * n - (207 : ℝ) / 5) :=
    mul_pos hn0 (by linarith [hn83])
  have hinc :
      0 ≤ (D - n) * (D + 5 * n - (247 : ℝ) / 5) :=
    mul_nonneg (sub_nonneg.mpr hnD) (by linarith [hn83, hnD])
  nlinarith [hbase, hinc]

private lemma quarter_of_second_target
    {n D M : ℝ} (hn0 : 0 < n) (hn83 : (83 : ℝ) / 10 < n)
    (hD : 0 < D) (hnD : n ≤ D)
    (hTarget : M * (n + 1) < (58 : ℝ) / 5 * n - n ^ 2 - D) :
    4 * M < D := by
  by_contra hnot
  have hDM : D ≤ 4 * M := le_of_not_gt hnot
  have hn1 : 0 ≤ n + 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hDM hn1
  have hneg :
      D * (n + 5) + 4 * n ^ 2 - (232 : ℝ) / 5 * n < 0 := by
    nlinarith
  have hbase : 0 < n * (5 * n - (207 : ℝ) / 5) :=
    mul_pos hn0 (by linarith [hn83])
  have hinc : 0 ≤ (D - n) * (n + 5) :=
    mul_nonneg (sub_nonneg.mpr hnD) (by linarith)
  nlinarith [hbase, hinc]

/-- The complete orbit-I residual estimate, with no generated leaf bank. -/
theorem orbitI_residual_bound : ResidualBoundHypothesis := by
  intro U V G Sx Sj Tx Tj Rx Rj r
  by_cases hnine : (9 : ℝ) ≤ min U V
  · exact r.bound_of_nine_le_min hnine
  have hmin9 : min U V < 9 := lt_of_not_ge hnine
  by_contra hbound
  have hfail : G + V + (G + U) / V < (58 : ℝ) / 5 :=
    lt_of_not_ge hbound
  have hU : 0 < U := by linarith [r.U_lower]
  have hV : 0 < V := by linarith [r.V_lower]
  have hdiv : (G + U) / V < (58 : ℝ) / 5 - G - V := by linarith
  have hclear := (div_lt_iff₀ hV).1 hdiv
  by_cases hUV : U ≤ V
  · have hn83 := r.U_gt_eighty_three_tenths
    have hn9 : U < 9 := by simpa [min_eq_left hUV] using hmin9
    have hD : 0 < V := hV
    have hM : 0 < cyclicW U V G := by linarith [r.W_lower]
    have hDm : cyclicW U V G = G + (V - U) := by
      unfold cyclicW
      ring
    have hCD := r.high_CD_of_U_le_V hUV
    have hCD' :
        3 * V - 2 * U ≤ cyclicW U V G * (U - 3) := by
      linarith [hCD]
    have hTarget :
        cyclicW U V G * (V + 1) <
          V * ((63 : ℝ) / 5 - U) - 2 * U := by
      unfold cyclicW
      nlinarith [hclear]
    have hquarter := quarter_of_first_target hU hn83 hV hUV hTarget
    have hneg := orbitILow_numerators_first_orientation
      hn83 hn9 hD hUV hM hCD' hTarget
    let g := lowFan_first r
    by_cases hTR : g.Tj ≤ g.Rj
    · have hnon := lowFan_P1_nonneg g hU hn83 hn9 hV hUV r.G_lower
        hM hDm hCD' hquarter hTR
      linarith [hneg.1]
    · have hRT : g.Rj ≤ g.Tj := le_of_not_ge hTR
      have hnon := lowFan_P2_nonneg g hU hn83 hn9 hV hUV r.G_lower
        hM hDm hCD' hquarter hRT
      linarith [hneg.2]
  · have hVU : V ≤ U := le_of_not_ge hUV
    have hn83 := r.V_gt_eighty_three_tenths
    have hn9 : V < 9 := by simpa [min_eq_right hVU] using hmin9
    have hD : 0 < U := hU
    have hM : 0 < G := by linarith [r.G_lower]
    have hDm : G = cyclicW U V G + (U - V) := by
      unfold cyclicW
      ring
    have hCD := r.high_CD_of_V_le_U hVU
    have hCD' : 3 * U - 2 * V ≤ G * (V - 3) := by
      linarith [hCD]
    have hTarget :
        G * (V + 1) < (58 : ℝ) / 5 * V - V ^ 2 - U := by
      nlinarith [hclear]
    have hquarter := quarter_of_second_target hV hn83 hU hVU hTarget
    have hneg := orbitILow_numerators_second_orientation
      hn83 hn9 hD hVU hM hCD' hTarget
    let g := lowFan_second r
    by_cases hTR : g.Tj ≤ g.Rj
    · have hnon := lowFan_P1_nonneg g hV hn83 hn9 hU hVU
        (by linarith [r.W_lower]) hM hDm hCD' hquarter hTR
      linarith [hneg.1]
    · have hRT : g.Rj ≤ g.Tj := le_of_not_ge hTR
      have hnon := lowFan_P2_nonneg g hV hn83 hn9 hU hVU
        (by linarith [r.W_lower]) hM hDm hCD' hquarter hRT
      linarith [hneg.2]

end Heilbronn8.QuadHull
