import Mathlib

set_option maxHeartbeats 0

/-!
# The CAB central sign census

This file is deliberately independent of the hull-five geometry adapter.  It
contains the finite sign argument behind the CAB census and the one polynomial
identity needed to recover the final `PQR` sign in the exceptional cell.

The determinant order used by the adapter is

`BPQ, XPQ, CPQ, BPR, XPR, CPR, BQR, XQR, CQR, PQR`.

For the CAB angular order, `XPQ < 0`, `XPR < 0`, and `XQR > 0` are fixed.
The six propositions below record positivity of the remaining `B`- and
`C`-rows.  Negation means negativity when the adapter supplies its usual
nonzero determinant floors.
-/

namespace Heilbronn8.TriHull

/-- One of the three inner points sees the other two in the same fan sector.

With `XPQ < 0`, `XPR < 0`, and `XQR > 0`, only five of the nominal nine
same-sector cells can occur.  The five disjuncts below are respectively
`PXC` at `P`, `PCB` at `P`, `QCB` at `Q`, `QBX` at `Q`, and `RCB` at `R`.
-/
def CabSameSectorBits
    (bpq cpq bpr cpr bqr cqr : Prop) : Prop :=
  (cpq ∧ cpr) ∨
  (¬ cpq ∧ bpq ∧ ¬ cpr ∧ bpr) ∨
  (cpq ∧ ¬ bpq ∧ ¬ cqr ∧ bqr) ∨
  (bpq ∧ ¬ bqr) ∨
  (cpr ∧ ¬ bpr ∧ cqr ∧ ¬ bqr)

/-- The six unfixed signs of the unique CAB no-same-sector cell.

Together with the fixed `X`-row signs, these are the first nine bits of type
`717`: `101100110`.  The final `PQR` bit is proved positive below.
-/
def Cab717PairBits
    (bpq cpq bpr cpr bqr cqr : Prop) : Prop :=
  bpq ∧ cpq ∧ bpr ∧ ¬ cpr ∧ bqr ∧ ¬ cqr

/-- Pure propositional core of the CAB census.

`hpq`, `hpr`, and `hqr` say that the fixed `X` sign leaves only the three
fan-sector sign pairs.  The remaining four hypotheses exclude the two cyclic
tournaments at `B` and at `C`.  In barycentric coordinates those exclusions
follow from transitivity of the positive ratios `y₁ / y₂` and `y₀ / y₁`, or
equivalently from the corresponding three-term Pluecker identities.
-/
theorem cab_sameSector_or_717_bits
    {bpq cpq bpr cpr bqr cqr : Prop}
    (hpq : bpq ∨ cpq)
    (hpr : bpr ∨ cpr)
    (hqr : ¬ (bqr ∧ cqr))
    (hBcycle₁ : ¬ (bpq ∧ ¬ bpr ∧ bqr))
    (hBcycle₂ : ¬ (¬ bpq ∧ bpr ∧ ¬ bqr))
    (hCcycle₁ : ¬ (cpq ∧ ¬ cpr ∧ cqr))
    (hCcycle₂ : ¬ (¬ cpq ∧ cpr ∧ ¬ cqr)) :
    CabSameSectorBits bpq cpq bpr cpr bqr cqr ∨
      Cab717PairBits bpq cpq bpr cpr bqr cqr := by
  simp only [CabSameSectorBits, Cab717PairBits]
  tauto

/-- The homogeneous barycentric numerator of `sig P Q R`.

If the rows `(p₀,p₁,p₂)`, `(q₀,q₁,q₂)`, `(r₀,r₁,r₂)` all have the same
positive sum `E`, then the geometric determinant is this numerator divided by
`E²`.  Only its sign is used here.
-/
def cabBaryDet
    (p0 p1 p2 q0 q1 q2 r0 r1 r2 : ℝ) : ℝ :=
  p0 * (q1 * r2 - q2 * r1) -
    p1 * (q0 * r2 - q2 * r0) +
    p2 * (q0 * r1 - q1 * r0)

/-- In the exceptional pair-sign cell, the `PQR` sign is forced positive.

The hypotheses are precisely `CPQ > 0`, `XPQ < 0`, `CPR < 0`, and
`XPR < 0`.  After dividing the `q`- and `r`-rows coordinatewise by the
positive `p`-row, they say `u₂ > u₁ > u₀` and `v₂ > v₀ > v₁`.
The proof below keeps the division-free polynomial certificate

`p₀ det = CPQ * (-XPR) - (-XPQ) * CPR`.
-/
theorem cab_717_baryDet_pos
    {p0 p1 p2 q0 q1 q2 r0 r1 r2 : ℝ}
    (hp0 : 0 < p0)
    (hcpq : 0 < p0 * q1 - p1 * q0)
    (hxpq : p2 * q0 - p0 * q2 < 0)
    (hcpr : p0 * r1 - p1 * r0 < 0)
    (hxpr : p2 * r0 - p0 * r2 < 0) :
    0 < cabBaryDet p0 p1 p2 q0 q1 q2 r0 r1 r2 := by
  have hnxpq : 0 < -(p2 * q0 - p0 * q2) := neg_pos.mpr hxpq
  have hnxpr : 0 < -(p2 * r0 - p0 * r2) := neg_pos.mpr hxpr
  have hfirst :
      0 < (p0 * q1 - p1 * q0) * (-(p2 * r0 - p0 * r2)) :=
    mul_pos hcpq hnxpr
  have hsecond :
      (-(p2 * q0 - p0 * q2)) * (p0 * r1 - p1 * r0) < 0 :=
    mul_neg_of_pos_of_neg hnxpq hcpr
  have hid :
      p0 * cabBaryDet p0 p1 p2 q0 q1 q2 r0 r1 r2 =
        (p0 * q1 - p1 * q0) * (-(p2 * r0 - p0 * r2)) -
          (-(p2 * q0 - p0 * q2)) * (p0 * r1 - p1 * r0) := by
    simp only [cabBaryDet]
    ring
  have hmul :
      0 < p0 * cabBaryDet p0 p1 p2 q0 q1 q2 r0 r1 r2 := by
    nlinarith [hfirst, hsecond, hid]
  exact pos_of_mul_pos_right hmul (le_of_lt hp0)

end Heilbronn8.TriHull
