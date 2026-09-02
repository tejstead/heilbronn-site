import Heilbronn8.TriHull.HullSevenType1Scalar

/-!
# Bracket adapter for the population-185 hull-seven chamber

This is the determinant-level front end of `HullSevenType1ChordInput`.
Indices refer to the unique type-1 presentation (rotation two, without
reflection) certified by `ResidualHullSevenType1Classification`: among
increasing-index brackets only `d06` and `d16` are negative.

The adapter does not postulate any of the derived Pluecker recurrences.  It
obtains all five of them from one generic rank-two Pluecker relation.  Its
remaining hypotheses are exactly the normalized triangle floors, the three
consecutive-ear caps, the two endpoint caps, and the hull-area decomposition.
-/

namespace Heilbronn8.TriHull

abbrev HullSevenType1Index := Fin 7

/-- Generic normalized bracket data in the unique type-1 presentation.

For an actual configuration, `bracket i j` is the signed determinant
`[D_i,D_j,p]` divided by the common positive minimum-triangle scale.
Skew-symmetry and Pluecker are universal determinant identities.  The floor
fields are the complete portion of the audited sign packet used below.
-/
structure HullSevenType1BracketData (H : ℝ) where
  bracket : HullSevenType1Index → HullSevenType1Index → ℝ
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
  neg_d16_ge : 1 ≤ -bracket 1 6

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

/-- The generic bracket packet supplies every field of the compact type-1
chord input.  In particular, the signs in the two endpoint rows are obtained
by defining `G=-d06` and `h=-d16`; they are not separate recurrence axioms. -/
noncomputable def HullSevenType1BracketData.toChordInput
    {H : ℝ} (X : HullSevenType1BracketData H) :
    HullSevenType1ChordInput H := by
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
      r := X.bracket 3 5
      L := X.bracket 1 4
      R := X.bracket 2 5
      c := X.bracket 1 5
      l := X.bracket 0 4
      m := X.bracket 2 6
      n := X.bracket 0 5
      h := -X.bracket 1 6
      a_ge := X.d01_ge
      A_ge := X.d12_ge
      B_ge := X.d23_ge
      C_ge := X.d34_ge
      D_ge := X.d45_ge
      z_ge := X.d56_ge
      G_ge := X.neg_d06_ge
      p_ge := X.d13_ge
      q_ge := X.d24_ge
      r_ge := X.d35_ge
      L_ge := X.d14_ge
      R_ge := X.d25_ge
      c_ge := X.d15_ge
      l_ge := X.d04_ge
      m_ge := X.d26_ge
      n_ge := X.d05_ge
      h_ge := X.neg_d16_ge
      p_ear := X.ear13
      q_ear := X.ear24
      r_ear := X.ear35
      plucker_L := ?_
      plucker_R := ?_
      left_endpoint := X.left_endpoint
      right_endpoint := X.right_endpoint
      plucker_central := ?_
      plucker1256 := ?_
      plucker0156 := ?_
      area := X.area }
  · have hp := X.plucker 1 2 3 4
    nlinarith
  · have hp := X.plucker 2 3 4 5
    nlinarith
  · have hp := X.plucker 1 2 4 5
    nlinarith
  · have hp := X.plucker 1 2 5 6
    nlinarith
  · have hp := X.plucker 0 1 5 6
    nlinarith

/-- Direct sharp-constant result from the generic determinant packet. -/
theorem hullSeven_v8_of_type1_bracket
    {H : ℝ} (X : HullSevenType1BracketData H) : 1 ≤ v8 * H :=
  hullSeven_v8_of_type1_scalar X.toChordInput

end Heilbronn8.TriHull
