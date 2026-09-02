import Mathlib

set_option linter.style.header false

/-!
# Fixed-variable scalar core for the convex-hexagon case

This is the nonlinear heart of the existing convex-hexagon proof, separated
from its twenty-leaf `min` and coordinate bookkeeping.  The variables have
the following geometric roles:

* `T` is one alternating triangle;
* `E0,…,E5` are the six ears;
* `(P,Pc)`, `(Q,Qc)`, `(R,Rc)` are the three complementary pairs which
  split `T + E1`, `T + E3`, and `T + E5`;
* the three product identities are cyclic Pluecker relations.

The first theorem proves the `6m` bound.  The second records all equality
information exposed by exactly the same argument.  A geometry adapter can
then use the returned determinant table to identify the affine-regular
hexagon.
-/

namespace N6Scratch
namespace HexagonScalar

private lemma split_product_lt
    {m x y K : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hsum : x + y < 4 * m) (hmul : m * (x + y) ≤ K) :
    x * y < K := by
  have hgap : 0 < (x + y) * (4 * m - (x + y)) :=
    mul_pos (add_pos hx hy) (sub_pos.mpr hsum)
  nlinarith [hgap, sq_nonneg (x - y), hmul]

private lemma split_product_le
    {m x y K : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsum : x + y ≤ 4 * m) (hmul : m * (x + y) ≤ K) :
    x * y ≤ K := by
  have hgap : 0 ≤ (x + y) * (4 * m - (x + y)) :=
    mul_nonneg (add_nonneg hx hy) (sub_nonneg.mpr hsum)
  nlinarith [hgap, sq_nonneg (x - y), hmul]

/-- The cyclic Pluecker core forces the doubled hull area to be at least
`6m`.  This is the compact fixed-variable version of the hull-six bound. -/
theorem cycle_bound
    (m H T E0 E1 E2 E3 E4 E5 P Pc Q Qc R Rc : ℝ)
    (hm : 0 < m)
    (hT : 0 < T) (hE1 : 0 < E1) (hE3 : 0 < E3) (hE5 : 0 < E5)
    (hP : 0 < P) (hPc : 0 < Pc) (hQ : 0 < Q) (hQc : 0 < Qc)
    (hR : 0 < R) (hRc : 0 < Rc)
    (hmT : m ≤ T)
    (hmE0 : m ≤ E0) (hmE1 : m ≤ E1) (hmE2 : m ≤ E2)
    (hmE3 : m ≤ E3) (hmE4 : m ≤ E4) (hmE5 : m ≤ E5)
    (harea : T + E1 + E3 + E5 = H)
    (hsumP : P + Pc = T + E1)
    (hsumQ : Q + Qc = T + E3)
    (hsumR : R + Rc = T + E5)
    (hprodP : P * R = E1 * E5 + E0 * T)
    (hprodQ : Q * Pc = E1 * E3 + E2 * T)
    (hprodR : Qc * Rc = E3 * E5 + E4 * T) :
    6 * m ≤ H := by
  by_contra h
  have hbad : H < 6 * m := lt_of_not_ge h
  have hTE1 : T + E1 < 4 * m := by linarith
  have hTE3 : T + E3 < 4 * m := by linarith
  have hTE5 : T + E5 < 4 * m := by linarith
  have hsumP_lt : P + Pc < 4 * m := by linarith
  have hsumQ_lt : Q + Qc < 4 * m := by linarith
  have hsumR_lt : R + Rc < 4 * m := by linarith
  have hmE1E3 : m * E1 ≤ E1 * E3 := by
    calc
      m * E1 = E1 * m := mul_comm _ _
      _ ≤ E1 * E3 := mul_le_mul_of_nonneg_left hmE3 (le_of_lt hE1)
  have hmE3E5 : m * E3 ≤ E3 * E5 := by
    calc
      m * E3 = E3 * m := mul_comm _ _
      _ ≤ E3 * E5 := mul_le_mul_of_nonneg_left hmE5 (le_of_lt hE3)
  have hmE1E5 : m * E5 ≤ E1 * E5 :=
    mul_le_mul_of_nonneg_right hmE1 (le_of_lt hE5)
  have hmP : m * (P + Pc) ≤ E1 * E3 + m * T := by
    calc
      m * (P + Pc) = m * (T + E1) := by rw [hsumP]
      _ = m * T + m * E1 := mul_add _ _ _
      _ ≤ m * T + E1 * E3 := by
        simpa only [add_comm] using add_le_add_left hmE1E3 (m * T)
      _ = E1 * E3 + m * T := add_comm _ _
  have hmQ : m * (Q + Qc) ≤ E3 * E5 + m * T := by
    calc
      m * (Q + Qc) = m * (T + E3) := by rw [hsumQ]
      _ = m * T + m * E3 := mul_add _ _ _
      _ ≤ m * T + E3 * E5 := by
        simpa only [add_comm] using add_le_add_left hmE3E5 (m * T)
      _ = E3 * E5 + m * T := add_comm _ _
  have hmR : m * (R + Rc) ≤ E1 * E5 + m * T := by
    calc
      m * (R + Rc) = m * (T + E5) := by rw [hsumR]
      _ = m * T + m * E5 := mul_add _ _ _
      _ ≤ m * T + E1 * E5 := by
        simpa only [add_comm] using add_le_add_left hmE1E5 (m * T)
      _ = E1 * E5 + m * T := add_comm _ _
  have huP : P * Pc < E1 * E3 + m * T :=
    split_product_lt hP hPc hsumP_lt hmP
  have huQ : Q * Qc < E3 * E5 + m * T :=
    split_product_lt hQ hQc hsumQ_lt hmQ
  have huR : R * Rc < E1 * E5 + m * T :=
    split_product_lt hR hRc hsumR_lt hmR
  have hmE0T : m * T ≤ E0 * T :=
    mul_le_mul_of_nonneg_right hmE0 (le_of_lt hT)
  have hmE2T : m * T ≤ E2 * T :=
    mul_le_mul_of_nonneg_right hmE2 (le_of_lt hT)
  have hmE4T : m * T ≤ E4 * T :=
    mul_le_mul_of_nonneg_right hmE4 (le_of_lt hT)
  have hlP : E1 * E3 + m * T ≤ Q * Pc := by
    rw [hprodQ]
    simpa only [add_comm] using add_le_add_left hmE2T (E1 * E3)
  have hlQ : E3 * E5 + m * T ≤ Qc * Rc := by
    rw [hprodR]
    simpa only [add_comm] using add_le_add_left hmE4T (E3 * E5)
  have hlR : E1 * E5 + m * T ≤ P * R := by
    rw [hprodP]
    simpa only [add_comm] using add_le_add_left hmE0T (E1 * E5)
  have hP_lt_Q : P < Q := by
    by_contra hn
    have hQP : Q ≤ P := le_of_not_gt hn
    have hmul : Q * Pc ≤ P * Pc :=
      mul_le_mul_of_nonneg_right hQP hPc.le
    exact (not_lt_of_ge hmul) (huP.trans_le hlP)
  have hQ_lt_Rc : Q < Rc := by
    have hmul : Qc * Q < Qc * Rc := by
      calc
        Qc * Q = Q * Qc := mul_comm _ _
        _ < E3 * E5 + m * T := huQ
        _ ≤ Qc * Rc := hlQ
    by_contra hn
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left
      (le_of_not_gt hn) hQc.le)) hmul
  have hRc_lt_P : Rc < P := by
    have hmul : Rc * R < P * R := by
      calc
        Rc * R = R * Rc := mul_comm _ _
        _ < E1 * E5 + m * T := huR
        _ ≤ P * R := hlR
    by_contra hn
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_right
      (le_of_not_gt hn) hR.le)) hmul
  linarith

/-- Equality in `cycle_bound` fixes the complete determinant table used by
the proof: every ear is `m`, the alternating triangle is `3m`, and all six
complementary middle triangles are `2m`. -/
theorem cycle_rigidity
    (m H T E0 E1 E2 E3 E4 E5 P Pc Q Qc R Rc : ℝ)
    (hm : 0 < m)
    (hT : 0 < T) (hE1 : 0 < E1) (hE3 : 0 < E3) (hE5 : 0 < E5)
    (hP : 0 < P) (hPc : 0 < Pc) (hQ : 0 < Q) (hQc : 0 < Qc)
    (hR : 0 < R) (hRc : 0 < Rc)
    (hmT : m ≤ T)
    (hmE0 : m ≤ E0) (hmE1 : m ≤ E1) (hmE2 : m ≤ E2)
    (hmE3 : m ≤ E3) (hmE4 : m ≤ E4) (hmE5 : m ≤ E5)
    (harea : T + E1 + E3 + E5 = H)
    (hH : H = 6 * m)
    (hsumP : P + Pc = T + E1)
    (hsumQ : Q + Qc = T + E3)
    (hsumR : R + Rc = T + E5)
    (hprodP : P * R = E1 * E5 + E0 * T)
    (hprodQ : Q * Pc = E1 * E3 + E2 * T)
    (hprodR : Qc * Rc = E3 * E5 + E4 * T) :
    E0 = m ∧ E1 = m ∧ E2 = m ∧ E3 = m ∧ E4 = m ∧ E5 = m ∧
    T = 3 * m ∧
    P = 2 * m ∧ Pc = 2 * m ∧ Q = 2 * m ∧ Qc = 2 * m ∧
    R = 2 * m ∧ Rc = 2 * m := by
  have hTE1 : T + E1 ≤ 4 * m := by linarith
  have hTE3 : T + E3 ≤ 4 * m := by linarith
  have hTE5 : T + E5 ≤ 4 * m := by linarith
  have hsumP_le : P + Pc ≤ 4 * m := by linarith
  have hsumQ_le : Q + Qc ≤ 4 * m := by linarith
  have hsumR_le : R + Rc ≤ 4 * m := by linarith
  have hmE1E3 : m * E1 ≤ E1 * E3 := by
    calc
      m * E1 = E1 * m := mul_comm _ _
      _ ≤ E1 * E3 := mul_le_mul_of_nonneg_left hmE3 (le_of_lt hE1)
  have hmE3E5 : m * E3 ≤ E3 * E5 := by
    calc
      m * E3 = E3 * m := mul_comm _ _
      _ ≤ E3 * E5 := mul_le_mul_of_nonneg_left hmE5 (le_of_lt hE3)
  have hmE1E5 : m * E5 ≤ E1 * E5 :=
    mul_le_mul_of_nonneg_right hmE1 (le_of_lt hE5)
  have hmP : m * (P + Pc) ≤ E1 * E3 + m * T := by
    calc
      m * (P + Pc) = m * (T + E1) := by rw [hsumP]
      _ = m * T + m * E1 := mul_add _ _ _
      _ ≤ m * T + E1 * E3 := by
        simpa only [add_comm] using add_le_add_left hmE1E3 (m * T)
      _ = E1 * E3 + m * T := add_comm _ _
  have hmQ : m * (Q + Qc) ≤ E3 * E5 + m * T := by
    calc
      m * (Q + Qc) = m * (T + E3) := by rw [hsumQ]
      _ = m * T + m * E3 := mul_add _ _ _
      _ ≤ m * T + E3 * E5 := by
        simpa only [add_comm] using add_le_add_left hmE3E5 (m * T)
      _ = E3 * E5 + m * T := add_comm _ _
  have hmR : m * (R + Rc) ≤ E1 * E5 + m * T := by
    calc
      m * (R + Rc) = m * (T + E5) := by rw [hsumR]
      _ = m * T + m * E5 := mul_add _ _ _
      _ ≤ m * T + E1 * E5 := by
        simpa only [add_comm] using add_le_add_left hmE1E5 (m * T)
      _ = E1 * E5 + m * T := add_comm _ _
  have hsplitP : P * Pc ≤ m * (P + Pc) :=
    split_product_le (le_of_lt hP) (le_of_lt hPc) hsumP_le (le_refl _)
  have hsplitQ : Q * Qc ≤ m * (Q + Qc) :=
    split_product_le (le_of_lt hQ) (le_of_lt hQc) hsumQ_le (le_refl _)
  have hsplitR : R * Rc ≤ m * (R + Rc) :=
    split_product_le (le_of_lt hR) (le_of_lt hRc) hsumR_le (le_refl _)
  have hmE0T : m * T ≤ E0 * T :=
    mul_le_mul_of_nonneg_right hmE0 (le_of_lt hT)
  have hmE2T : m * T ≤ E2 * T :=
    mul_le_mul_of_nonneg_right hmE2 (le_of_lt hT)
  have hmE4T : m * T ≤ E4 * T :=
    mul_le_mul_of_nonneg_right hmE4 (le_of_lt hT)
  have hlP : E1 * E3 + m * T ≤ Q * Pc := by
    rw [hprodQ]
    simpa only [add_comm] using add_le_add_left hmE2T (E1 * E3)
  have hlQ : E3 * E5 + m * T ≤ Qc * Rc := by
    rw [hprodR]
    simpa only [add_comm] using add_le_add_left hmE4T (E3 * E5)
  have hlR : E1 * E5 + m * T ≤ P * R := by
    rw [hprodP]
    simpa only [add_comm] using add_le_add_left hmE0T (E1 * E5)
  have huP : P * Pc ≤ E1 * E3 + m * T := hsplitP.trans hmP
  have huQ : Q * Qc ≤ E3 * E5 + m * T := hsplitQ.trans hmQ
  have huR : R * Rc ≤ E1 * E5 + m * T := hsplitR.trans hmR
  have hP_le_Q : P ≤ Q := by
    by_contra hn
    have hQP : Q < P := lt_of_not_ge hn
    have hmul : Q * Pc < P * Pc := mul_lt_mul_of_pos_right hQP hPc
    exact (not_lt_of_ge (huP.trans hlP)) hmul
  have hQ_le_Rc : Q ≤ Rc := by
    have hmul : Qc * Q ≤ Qc * Rc := by
      calc
        Qc * Q = Q * Qc := mul_comm _ _
        _ ≤ E3 * E5 + m * T := huQ
        _ ≤ Qc * Rc := hlQ
    by_contra hn
    exact (not_lt_of_ge hmul)
      (mul_lt_mul_of_pos_left (lt_of_not_ge hn) hQc)
  have hRc_le_P : Rc ≤ P := by
    have hmul : Rc * R ≤ P * R := by
      calc
        Rc * R = R * Rc := mul_comm _ _
        _ ≤ E1 * E5 + m * T := huR
        _ ≤ P * R := hlR
    by_contra hn
    exact (not_lt_of_ge hmul)
      (mul_lt_mul_of_pos_right (lt_of_not_ge hn) hR)
  have hPQ : P = Q := by linarith
  have hQRc : Q = Rc := by linarith
  have hEqP : m * (P + Pc) = E1 * E3 + m * T := by
    apply le_antisymm hmP
    calc
      E1 * E3 + m * T ≤ Q * Pc := hlP
      _ = P * Pc := by rw [hPQ]
      _ ≤ m * (P + Pc) := hsplitP
  have hEqQ : m * (Q + Qc) = E3 * E5 + m * T := by
    apply le_antisymm hmQ
    calc
      E3 * E5 + m * T ≤ Qc * Rc := hlQ
      _ = Qc * Q := by rw [hQRc]
      _ = Q * Qc := mul_comm _ _
      _ ≤ m * (Q + Qc) := hsplitQ
  have hEqR : m * (R + Rc) = E1 * E5 + m * T := by
    apply le_antisymm hmR
    calc
      E1 * E5 + m * T ≤ P * R := hlR
      _ = Rc * R := by rw [hPQ, hQRc]
      _ = R * Rc := mul_comm _ _
      _ ≤ m * (R + Rc) := hsplitR
  have hEqP' : m * (T + E1) = E1 * E3 + m * T := by
    calc
      m * (T + E1) = m * (P + Pc) := by rw [hsumP]
      _ = E1 * E3 + m * T := hEqP
  have hEqQ' : m * (T + E3) = E3 * E5 + m * T := by
    calc
      m * (T + E3) = m * (Q + Qc) := by rw [hsumQ]
      _ = E3 * E5 + m * T := hEqQ
  have hEqR' : m * (T + E5) = E1 * E5 + m * T := by
    calc
      m * (T + E5) = m * (R + Rc) := by rw [hsumR]
      _ = E1 * E5 + m * T := hEqR
  have hzE3 : E1 * (E3 - m) = 0 := by
    nlinarith only [hEqP']
  have hE3eq : E3 = m := by
    rcases mul_eq_zero.mp hzE3 with hzero | hzero
    · exact False.elim ((ne_of_gt hE1) hzero)
    · linarith only [hzero]
  have hzE5 : E3 * (E5 - m) = 0 := by
    nlinarith only [hEqQ']
  have hE5eq : E5 = m := by
    rcases mul_eq_zero.mp hzE5 with hzero | hzero
    · exact False.elim ((ne_of_gt hE3) hzero)
    · linarith only [hzero]
  have hzE1 : E5 * (E1 - m) = 0 := by
    nlinarith only [hEqR']
  have hE1eq : E1 = m := by
    rcases mul_eq_zero.mp hzE1 with hzero | hzero
    · exact False.elim ((ne_of_gt hE5) hzero)
    · linarith only [hzero]
  have hTeq : T = 3 * m := by
    linarith only [harea, hH, hE1eq, hE3eq, hE5eq]
  have hTne : T ≠ 0 := ne_of_gt hT
  have hQPcEq : Q * Pc = E1 * E3 + m * T := by
    apply le_antisymm
    · calc
        Q * Pc = P * Pc := by rw [hPQ]
        _ ≤ m * (P + Pc) := hsplitP
        _ = E1 * E3 + m * T := hEqP
    · exact hlP
  have hQcRcEq : Qc * Rc = E3 * E5 + m * T := by
    apply le_antisymm
    · calc
        Qc * Rc = Q * Qc := by rw [← hQRc]; ring
        _ ≤ m * (Q + Qc) := hsplitQ
        _ = E3 * E5 + m * T := hEqQ
    · exact hlQ
  have hPREq : P * R = E1 * E5 + m * T := by
    apply le_antisymm
    · calc
        P * R = R * Rc := by rw [hPQ, hQRc]; ring
        _ ≤ m * (R + Rc) := hsplitR
        _ = E1 * E5 + m * T := hEqR
    · exact hlR
  have hE2eq : E2 = m := by
    have hz : (E2 - m) * T = 0 := by
      nlinarith only [hprodQ, hQPcEq]
    rcases mul_eq_zero.mp hz with hz | hz
    · linarith only [hz]
    · exact False.elim (hTne hz)
  have hE4eq : E4 = m := by
    have hz : (E4 - m) * T = 0 := by
      nlinarith only [hprodR, hQcRcEq]
    rcases mul_eq_zero.mp hz with hz | hz
    · linarith only [hz]
    · exact False.elim (hTne hz)
  have hE0eq : E0 = m := by
    have hz : (E0 - m) * T = 0 := by
      nlinarith only [hprodP, hPREq]
    rcases mul_eq_zero.mp hz with hz | hz
    · linarith only [hz]
    · exact False.elim (hTne hz)
  have hsumP4 : P + Pc = 4 * m := by
    linarith only [hsumP, hTeq, hE1eq]
  have hPPcEq := hQPcEq
  rw [← hPQ, hE1eq, hE3eq, hTeq] at hPPcEq
  have hprodP4 : P * Pc = 4 * m * m := by
    nlinarith only [hPPcEq]
  have hpc : Pc = 4 * m - P := by linarith only [hsumP4]
  have hprodP4' : P * (4 * m - P) = 4 * m * m := by
    calc
      P * (4 * m - P) = P * Pc := by rw [hpc]
      _ = 4 * m * m := hprodP4
  have hsqP : (P - 2 * m) * (P - 2 * m) = 0 := by
    nlinarith only [hprodP4']
  have hPeq : P = 2 * m := by
    rcases mul_eq_zero.mp hsqP with hz | hz <;> linarith only [hz]
  have hPceq : Pc = 2 * m := by linarith only [hsumP4, hPeq]
  have hQeq : Q = 2 * m := by linarith only [hPQ, hPeq]
  have hRceq : Rc = 2 * m := by linarith only [hQRc, hQeq]
  have hQceq : Qc = 2 * m := by
    linarith only [hsumQ, hTeq, hE3eq, hQeq]
  have hReq : R = 2 * m := by
    linarith only [hsumR, hTeq, hE5eq, hRceq]
  exact ⟨hE0eq, hE1eq, hE2eq, hE3eq, hE4eq, hE5eq, hTeq,
    hPeq, hPceq, hQeq, hQceq, hReq, hRceq⟩

end HexagonScalar
end N6Scratch
