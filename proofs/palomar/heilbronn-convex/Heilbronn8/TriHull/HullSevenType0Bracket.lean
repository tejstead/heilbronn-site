import Heilbronn8.TriHull.HullSevenType0Scalar

/-!
# Bracket adapter for the population-138 hull-seven chamber

In the preferred type 0 presentation, `d06` is negative and every other
increasing-index bracket is positive.  This adapter derives every recurrence
in `HullSevenType0ChordInput` from a generic rank-two Pluecker relation.
-/

namespace Heilbronn8.TriHull

abbrev HullSevenType0Index := Fin 7

/-- Normalized bracket data in a preferred type 0 presentation. -/
structure HullSevenType0BracketData (H : ℝ) where
  bracket : HullSevenType0Index → HullSevenType0Index → ℝ
  skew : ∀ i j, bracket i j = -bracket j i
  plucker : ∀ i j k l,
    bracket i j * bracket k l -
      bracket i k * bracket j l +
      bracket i l * bracket j k = 0

  d01_ge : 1 ≤ bracket 0 1
  d12_ge : 1 ≤ bracket 1 2
  d23_ge : 1 ≤ bracket 2 3
  d34_ge : 1 ≤ bracket 3 4
  d45_ge : 1 ≤ bracket 4 5
  d56_ge : 1 ≤ bracket 5 6
  neg_d06_ge : 1 ≤ -bracket 0 6

  d13_ge : 1 ≤ bracket 1 3
  d24_ge : 1 ≤ bracket 2 4
  d35_ge : 1 ≤ bracket 3 5
  d14_ge : 1 ≤ bracket 1 4
  d25_ge : 1 ≤ bracket 2 5
  d15_ge : 1 ≤ bracket 1 5
  d04_ge : 1 ≤ bracket 0 4
  d26_ge : 1 ≤ bracket 2 6
  d05_ge : 1 ≤ bracket 0 5
  d16_ge : 1 ≤ bracket 1 6

  ear13 : bracket 1 3 ≤ bracket 1 2 + bracket 2 3 - 1
  ear24 : bracket 2 4 ≤ bracket 2 3 + bracket 3 4 - 1
  ear35 : bracket 3 5 ≤ bracket 3 4 + bracket 4 5 - 1
  left_endpoint :
    bracket 1 2 * bracket 0 4 + bracket 0 1 * bracket 2 4 ≤
      bracket 1 4 * (bracket 0 1 + bracket 1 2 - 1)
  right_endpoint :
    bracket 4 5 * bracket 2 6 + bracket 5 6 * bracket 2 4 ≤
      bracket 2 5 * (bracket 5 6 + bracket 4 5 - 1)
  area :
    bracket 0 1 + bracket 1 2 + bracket 2 3 + bracket 3 4 +
        bracket 4 5 + bracket 5 6 - bracket 0 6 ≤ H

/-- The generic bracket packet supplies the complete type 0 chord input. -/
noncomputable def HullSevenType0BracketData.toChordInput
    {H : ℝ} (X : HullSevenType0BracketData H) :
    HullSevenType0ChordInput H := by
  refine
    { a := X.bracket 0 1
      A := X.bracket 1 2
      B := X.bracket 2 3
      C := X.bracket 3 4
      D := X.bracket 4 5
      z := X.bracket 5 6
      G := -X.bracket 0 6
      p := X.bracket 1 3
      q := X.bracket 2 4
      rChord := X.bracket 3 5
      L := X.bracket 1 4
      R := X.bracket 2 5
      c := X.bracket 1 5
      l := X.bracket 0 4
      m := X.bracket 2 6
      n := X.bracket 0 5
      h := X.bracket 1 6
      a_ge := X.d01_ge
      A_ge := X.d12_ge
      B_ge := X.d23_ge
      C_ge := X.d34_ge
      D_ge := X.d45_ge
      z_ge := X.d56_ge
      G_ge := X.neg_d06_ge
      p_ge := X.d13_ge
      q_ge := X.d24_ge
      rChord_ge := X.d35_ge
      L_ge := X.d14_ge
      R_ge := X.d25_ge
      c_ge := X.d15_ge
      l_ge := X.d04_ge
      m_ge := X.d26_ge
      n_ge := X.d05_ge
      h_ge := X.d16_ge
      p_ear := X.ear13
      q_ear := X.ear24
      r_ear := X.ear35
      plucker_L := ?_
      plucker_R := ?_
      left_cap := X.left_endpoint
      right_cap := X.right_endpoint
      plucker_central := ?_
      plucker_leftFar := ?_
      plucker_rightFar := ?_
      plucker_endpoint := ?_
      area := X.area }
  · have hp := X.plucker 1 2 3 4
    nlinarith
  · have hp := X.plucker 2 3 4 5
    nlinarith
  · have hp := X.plucker 1 2 4 5
    nlinarith
  · have hp := X.plucker 0 1 4 5
    nlinarith
  · have hp := X.plucker 1 2 5 6
    nlinarith
  · have hp := X.plucker 0 1 5 6
    nlinarith

/-- Direct sharp-constant result from the generic determinant packet. -/
theorem hullSeven_v8_of_type0_bracket
    {H : ℝ} (X : HullSevenType0BracketData H) : 1 ≤ v8 * H :=
  hullSeven_v8_of_type0_scalar X.toChordInput

end Heilbronn8.TriHull
