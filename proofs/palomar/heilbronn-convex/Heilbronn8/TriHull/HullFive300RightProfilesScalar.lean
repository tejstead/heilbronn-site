import Mathlib

/-!
# Scalar endpoints for the homogeneous right-ear `300` profiles

Use the cyclic pentagon `A-B-X-C-D` and write

* `T = [ABC]`, `E = [BXC]`;
* `U = [ABX]`, `V = [AXC]`;
* `Z = [BCD]`, `K = [DBX]`, `L = [XCD]`;
* `W = [ABD]`, `F = [ACD]`.

The profile called `C` has its point in `U`, `E`, and `K`, while the
profile called `A` has its point in `V`, `E`, and `L`.  Thus `CCA` gives
two-point lower bounds in `U,K` and one-point lower bounds in `V,L`.
The reflected argument gives `CAA`.

Only scalar identities and lower bounds occur below.  The common proof is a
single Pluecker estimate; in particular, these two endpoints need no
generated box certificate and no case split on the order type of the three
inner points.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- Common Pluecker endpoint.  The two upper bounds coming from `F,W`
multiply, and the cross term cancels exactly against `A*D`:

`E*M = B*C-A*D <= (M+D-m)(M+A-m)-A*D = (M-m)(H-m)`.

The remaining contradiction is linear after multiplying by the positive
minimum `m`. -/
theorem hullFive300_right_cross_scalar
    {m E A B C D M F W H : ℝ}
    (hm : 0 < m)
    (hE : (17 / 2 : ℝ) * m ≤ E)
    (hAD : 10 * m ≤ A + D)
    (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hM : m ≤ M) (hF : m ≤ F) (hW : m ≤ W)
    (hFid : F = M + D - B)
    (hWid : W = M + A - C)
    (hEM : E * M = B * C - A * D)
    (hH : H = A + M + D) :
    m * 25 ≤ 2 * H := by
  have hEpos : 0 < E := by nlinarith
  have hMpos : 0 < M := lt_of_lt_of_le hm hM
  have hBupper : B ≤ M + D - m := by linarith [hF, hFid]
  have hCupper : C ≤ M + A - m := by linarith [hW, hWid]
  have hBfactor0 : 0 ≤ M + D - m := le_trans hB0 hBupper
  have hBCcap :
      B * C ≤ (M + D - m) * (M + A - m) := by
    calc
      B * C ≤ (M + D - m) * C :=
        mul_le_mul_of_nonneg_right hBupper hC0
      _ ≤ (M + D - m) * (M + A - m) :=
        mul_le_mul_of_nonneg_left hCupper hBfactor0
  have hEMcap : E * M ≤ (M - m) * (H - m) := by
    calc
      E * M = B * C - A * D := hEM
      _ ≤ (M + D - m) * (M + A - m) - A * D :=
        sub_le_sub_right hBCcap (A * D)
      _ = (M - m) * (H - m) := by rw [hH]; ring
  have hEMpos : 0 < E * M := mul_pos hEpos hMpos
  have hMmpos : 0 < M - m := by
    by_contra hnot
    have hMeq : M = m := by
      have : M - m ≤ 0 := le_of_not_gt hnot
      linarith
    rw [hMeq] at hEMcap hEMpos
    norm_num at hEMcap
    exact (not_lt_of_ge hEMcap) hEMpos
  by_contra hnot
  have hfail : 2 * H < m * 25 := lt_of_not_ge hnot
  have hHcap : H - m < (23 / 2 : ℝ) * m := by nlinarith
  have hproductCap :
      (M - m) * (H - m) < (M - m) * ((23 / 2 : ℝ) * m) :=
    mul_lt_mul_of_pos_left hHcap hMmpos
  have hElower : (17 / 2 : ℝ) * m * M ≤ E * M :=
    mul_le_mul_of_nonneg_right hE hMpos.le
  have hkey :
      (17 / 2 : ℝ) * m * M < (M - m) * ((23 / 2 : ℝ) * m) :=
    lt_of_le_of_lt (le_trans hElower hEMcap) hproductCap
  have hfactored : m * (23 * m) < m * (6 * M) := by
    nlinarith [hkey]
  have hfactored' : (23 * m) * m < (6 * M) * m := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfactored
  have hMlarge : 23 * m < 6 * M :=
    lt_of_mul_lt_mul_right hfactored' hm.le
  nlinarith [hH, hAD]

/-- The `CCA` endpoint: `U,K` contain two points, while `V,L` contain
one. -/
theorem hullFive300_right_cca_scalar
    {m E U V K L M F W H : ℝ}
    (hm : 0 < m)
    (hE : (17 / 2 : ℝ) * m ≤ E)
    (hU : 7 * m ≤ U) (hK : 7 * m ≤ K)
    (hV : 3 * m ≤ V) (hL : 3 * m ≤ L)
    (hM : m ≤ M) (hW : m ≤ W) (hF : m ≤ F)
    (hFid : F = M + L - V)
    (hWid : W = M + U - K)
    (hEM : E * M = V * K - U * L)
    (hH : H = U + M + L) :
    m * 25 ≤ 2 * H := by
  apply hullFive300_right_cross_scalar
    hm hE (by linarith [hU, hL])
    (by nlinarith [hV, hm]) (by nlinarith [hK, hm])
    hM hF hW hFid hWid hEM hH

/-- The reflected `CAA` endpoint: `V,L` contain two points, while `U,K`
contain one. -/
theorem hullFive300_right_caa_scalar
    {m E U V K L M F W H : ℝ}
    (hm : 0 < m)
    (hE : (17 / 2 : ℝ) * m ≤ E)
    (hV : 7 * m ≤ V) (hL : 7 * m ≤ L)
    (hU : 3 * m ≤ U) (hK : 3 * m ≤ K)
    (hM : m ≤ M) (hW : m ≤ W) (hF : m ≤ F)
    (hFid : F = M + L - V)
    (hWid : W = M + U - K)
    (hEM : E * M = V * K - U * L)
    (hH : H = U + M + L) :
    m * 25 ≤ 2 * H := by
  apply hullFive300_right_cross_scalar
    (m := m) (E := E) (A := L) (B := K) (C := V)
    (D := U) (M := M) (F := W) (W := F) (H := H)
    hm hE (by linarith [hL, hU])
    (by nlinarith [hK, hm]) (by nlinarith [hV, hm])
    hM hW hF hWid hFid
    (by nlinarith [hEM])
    (by linarith [hH])

end Heilbronn8.TriHull
