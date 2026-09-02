import Heilbronn8.TriHull.HullSevenTransferProducer
import Heilbronn8.TriHull.HullSevenBroadRigidity

/-!
# Full chord-input rigidity in the capped C24 branch

Scratch proposal.  The second import is the intended package location of the
adjacent broad-rigidity proposal.  This file is deliberately outside the live
package until both modules have been reviewed and typechecked together.
-/

namespace Heilbronn8.TriHull

set_option maxHeartbeats 1000000

/-- At the sharp root, the common endpoint lower bound has square equal to
the maximal central product.  This is precisely the root polynomial. -/
lemma hullSevenCoreRoot_endpoint_square :
    (hullSevenCoreRoot + 1) ^ 2 -
        (1 + 2 / hullSevenCoreRoot) =
      (1 + (1 + 2 / hullSevenCoreRoot) /
        (hullSevenCoreRoot + 1)) ^ 2 := by
  let s := hullSevenCoreRoot
  have hs : 0 < s := by
    dsimp [s]
    exact hullSevenCoreRoot_pos
  have hQ : hullSevenCoreQ s = 0 := by
    dsimp [s]
    exact hullSevenCoreRoot_eq_zero
  have hid :
      s ^ 2 * (s + 1) ^ 2 *
          (((s + 1) ^ 2 - (1 + 2 / s)) -
            (1 + (1 + 2 / s) / (s + 1)) ^ 2) =
        (s + 2) * hullSevenCoreQ s := by
    unfold hullSevenCoreQ
    field_simp [hs.ne', (add_pos hs (by norm_num : (0 : ℝ) < 1)).ne']
    ring
  rw [hQ, mul_zero] at hid
  have hfactor : 0 < s ^ 2 * (s + 1) ^ 2 := by positivity
  dsimp [s] at hid ⊢
  nlinarith

/-- Recurrence identity for the sharp left and right middle chords. -/
lemma hullSevenCoreRoot_p_identity :
    let s := hullSevenCoreRoot
    let q := 1 + 2 / s
    let A := s + 1
    let B := 1 + 1 / s
    let L := 1 + q / A
    B * (L + A) = q * (A + 1 / s) := by
  dsimp
  have hs := hullSevenCoreRoot_pos
  field_simp [hs.ne', (add_pos hs (by norm_num : (0 : ℝ) < 1)).ne']
  ring

/-- The complete normalized chord tuple forced in the capped branch. -/
structure HullSevenCappedChordRigidity {H : ℝ}
    (X : HullSevenChordInput H) (S : HullSevenCappedSurrogate X) : Prop where
  area_eq : H = hullSevenSharpH
  A_eq : X.A = hullSevenCoreRoot + 1
  D_eq : X.D = hullSevenCoreRoot + 1
  surrogate_t_eq : S.t = 1 / hullSevenCoreRoot
  surrogate_w_eq : S.w = 1 / hullSevenCoreRoot
  q_eq : X.q = 1 + 2 / hullSevenCoreRoot
  a0_eq : X.a0 = 1
  a5_eq : X.a5 = 1
  c_eq : X.c = 1
  l_eq : X.l = 1
  m_eq : X.m = 1
  G_eq : X.G = hullSevenCoreRoot ^ 2
  B_eq : X.B = 1 + 1 / hullSevenCoreRoot
  C_eq : X.C = 1 + 1 / hullSevenCoreRoot
  L_eq : X.L =
    1 + (1 + 2 / hullSevenCoreRoot) / (hullSevenCoreRoot + 1)
  R_eq : X.R =
    1 + (1 + 2 / hullSevenCoreRoot) / (hullSevenCoreRoot + 1)
  p_eq : X.p = hullSevenCoreRoot + 1 + 1 / hullSevenCoreRoot
  r_eq : X.r = hullSevenCoreRoot + 1 + 1 / hullSevenCoreRoot

/-- A capped surrogate attaining the sharp upper boundary forces every chord
input scalar to its unique symmetric value. -/
theorem HullSevenCappedSurrogate.chordInput_rigid_of_v8_upper {H : ℝ}
    (X : HullSevenChordInput H) (S : HullSevenCappedSurrogate X)
    (hupper : v8 * H ≤ 1) :
    HullSevenCappedChordRigidity X S := by
  let data := hullSevenBroadTransferData_of_cappedSurrogate X S
  have broad := HullSevenBroadTransferData.rigid_of_v8_upper data hupper
  change
    X.A - 1 = hullSevenCoreRoot ∧
      S.t = 1 / hullSevenCoreRoot ∧
      S.w = 1 / hullSevenCoreRoot ∧
      X.D - 1 = hullSevenCoreRoot ∧
      1 / (S.t * S.w) = hullSevenCoreRoot ^ 2 ∧
      H = hullSevenSharpH at broad
  rcases broad with ⟨hAsub, ht, hw, hDsub, hdataG, hH⟩
  have hA : X.A = hullSevenCoreRoot + 1 := by linarith
  have hD : X.D = hullSevenCoreRoot + 1 := by linarith
  have hsum := S.sum_eq
  have hq : X.q = 1 + 2 / hullSevenCoreRoot := by
    rw [ht, hw] at hsum
    calc
      X.q = 1 + (1 / hullSevenCoreRoot + 1 / hullSevenCoreRoot) := by
        linarith
      _ = 1 + 2 / hullSevenCoreRoot := by ring
  have hs : 0 < hullSevenCoreRoot := hullSevenCoreRoot_pos
  have hqX : 0 < X.q := lt_of_lt_of_le (by norm_num) X.q_ge
  have hLX : 0 < X.L := lt_of_lt_of_le (by norm_num) X.L_ge
  have hRX : 0 < X.R := lt_of_lt_of_le (by norm_num) X.R_ge

  have hclose := hullSeven_surrogate_closing_le X
    (mul_pos S.t_pos S.w_pos) S.product_lower
  have hcloseRoot : hullSevenCoreRoot ^ 2 ≤ X.G := by
    rw [hdataG] at hclose
    exact hclose
  have hBC : X.q + 1 ≤ X.B + X.C := by linarith [X.q_ear]
  have hbudget :
      X.a0 + X.A + X.B + X.C + X.D + X.a5 + X.G ≤
        hullSevenSharpH := by
    calc
      X.a0 + X.A + X.B + X.C + X.D + X.a5 + X.G ≤ H := X.area
      _ = hullSevenSharpH := hH
  rw [hA, hD] at hbudget
  unfold hullSevenSharpH at hbudget
  have ha0 : X.a0 = 1 := by
    nlinarith [X.a0_ge, X.a5_ge, hBC, hcloseRoot]
  have ha5 : X.a5 = 1 := by
    nlinarith [X.a0_ge, X.a5_ge, hBC, hcloseRoot]
  have hBCeq : X.B + X.C = X.q + 1 := by
    nlinarith [X.a0_ge, X.a5_ge, hBC, hcloseRoot]
  have hG : X.G = hullSevenCoreRoot ^ 2 := by
    nlinarith [X.a0_ge, X.a5_ge, hBC, hcloseRoot]

  let q0 := 1 + 2 / hullSevenCoreRoot
  let A0 := hullSevenCoreRoot + 1
  let L0 := 1 + q0 / A0
  let B0 := 1 + 1 / hullSevenCoreRoot
  have hq0eq : X.q = q0 := by simpa only [q0] using hq
  have hA0eq : X.A = A0 := by simpa only [A0] using hA
  have hD0eq : X.D = A0 := by simpa only [A0] using hD
  have hL0pos : 0 < L0 := by dsimp [L0, q0, A0]; positivity
  have hA0pos : 0 < A0 := by dsimp [A0]; positivity
  have hq0pos : 0 < q0 := by dsimp [q0]; positivity
  have hLlower : L0 ≤ X.L := by
    have h := (hullSeven_left_endpoint_preserved X).2.1
    rw [hq0eq, hA0eq] at h
    simpa only [L0] using h
  have hRlower : L0 ≤ X.R := by
    have h := (hullSeven_right_endpoint_preserved X).2.1
    rw [hq0eq, hD0eq] at h
    simpa only [L0] using h
  have hendpointSquare : A0 ^ 2 - q0 = L0 ^ 2 := by
    simpa only [A0, q0, L0] using hullSevenCoreRoot_endpoint_square
  have hLRupper : X.L * X.R ≤ L0 ^ 2 := by
    calc
      X.L * X.R = X.A * X.D - X.c * X.q := X.LR_rec
      _ ≤ X.A * X.D - X.q := by
        have hm := mul_le_mul_of_nonneg_right X.c_ge hqX.le
        nlinarith
      _ = A0 ^ 2 - q0 := by rw [hA0eq, hD0eq, hq0eq]; ring
      _ = L0 ^ 2 := hendpointSquare
  have hLRlower : L0 ^ 2 ≤ X.L * X.R := by
    calc
      L0 ^ 2 = L0 * L0 := by ring
      _ ≤ L0 * X.R :=
        mul_le_mul_of_nonneg_left hRlower hL0pos.le
      _ ≤ X.L * X.R :=
        mul_le_mul_of_nonneg_right hLlower hRX.le
  have hLReq : X.L * X.R = L0 ^ 2 :=
    le_antisymm hLRupper hLRlower
  have hLeq : X.L = L0 := by
    apply le_antisymm ?_ hLlower
    by_contra hnot
    have hgt : L0 < X.L := lt_of_not_ge hnot
    have hmul : L0 ^ 2 < X.L * X.R := by
      calc
        L0 ^ 2 = L0 * L0 := by ring
        _ < X.L * L0 := mul_lt_mul_of_pos_right hgt hL0pos
        _ ≤ X.L * X.R :=
          mul_le_mul_of_nonneg_left hRlower hLX.le
    exact (not_lt_of_ge hLReq.le) hmul
  have hReq : X.R = L0 := by
    apply le_antisymm ?_ hRlower
    by_contra hnot
    have hgt : L0 < X.R := lt_of_not_ge hnot
    have hmul : L0 ^ 2 < X.L * X.R := by
      calc
        L0 ^ 2 = L0 * L0 := by ring
        _ < L0 * X.R := mul_lt_mul_of_pos_left hgt hL0pos
        _ ≤ X.L * X.R :=
          mul_le_mul_of_nonneg_right hLlower hRX.le
    exact (not_lt_of_ge hLReq.le) hmul
  have hc : X.c = 1 := by
    have hrec := X.LR_rec
    rw [hLeq, hReq, hA0eq, hD0eq, hq0eq] at hrec
    have hzero : q0 * (X.c - 1) = 0 := by
      linear_combination hendpointSquare + hrec
    have hsub : X.c - 1 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hq0pos.ne'
    linarith only [hsub]
  have hLA : L0 * A0 = A0 + q0 := by
    dsimp [L0]
    field_simp [hA0pos.ne']
  have hl : X.l = 1 := by
    have he := X.left_endpoint
    rw [ha0, hA0eq, hq0eq, hLeq] at he
    have hAle : A0 * X.l ≤ A0 := by
      calc
        A0 * X.l ≤ L0 * A0 - q0 := by
          convert sub_le_sub_right he q0 using 1 <;> ring
        _ = A0 := by rw [hLA]; ring
    have hAge : A0 ≤ A0 * X.l := by
      simpa using mul_le_mul_of_nonneg_left X.l_ge hA0pos.le
    have hmul : A0 * X.l = A0 := le_antisymm hAle hAge
    have hzero : A0 * (X.l - 1) = 0 := by nlinarith
    have hsub : X.l - 1 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hA0pos.ne'
    linarith
  have hm : X.m = 1 := by
    have he := X.right_endpoint
    rw [ha5, hD0eq, hq0eq, hReq] at he
    have hAle : A0 * X.m ≤ A0 := by
      calc
        A0 * X.m ≤ L0 * A0 - q0 := by
          convert sub_le_sub_right he q0 using 1 <;> ring
        _ = A0 := by rw [hLA]; ring
    have hAge : A0 ≤ A0 * X.m := by
      simpa using mul_le_mul_of_nonneg_left X.m_ge hA0pos.le
    have hmul : A0 * X.m = A0 := le_antisymm hAle hAge
    have hzero : A0 * (X.m - 1) = 0 := by nlinarith
    have hsub : X.m - 1 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hA0pos.ne'
    linarith

  have hleftProduct : 0 ≤ (A0 - 1) * X.B - A0 := by
    have hqp := mul_le_mul_of_nonneg_left X.p_ear hqX.le
    have hineq : X.B * X.L + X.A * X.C ≤
        X.q * (X.A + X.B - 1) := by
      calc
        X.B * X.L + X.A * X.C = X.q * X.p := by
          nlinarith [X.L_rec]
        _ ≤ X.q * (X.A + X.B - 1) := hqp
    have hCexpr : X.C = X.q + 1 - X.B := by linarith [hBCeq]
    have hgap :
        0 ≤ X.q * (X.A + X.B - 1) -
          (X.B * X.L + X.A * X.C) := by linarith
    have hid :
        X.q * (X.A + X.B - 1) -
            (X.B * X.L + X.A * X.C) =
          L0 * ((A0 - 1) * X.B - A0) := by
      rw [hCexpr, hA0eq, hq0eq, hLeq]
      dsimp [L0, A0, q0]
      field_simp [hs.ne']
      ring
    rw [hid] at hgap
    by_contra hnot
    exact (not_lt_of_ge hgap)
      (mul_neg_of_pos_of_neg hL0pos (lt_of_not_ge hnot))
  have hrightProduct : 0 ≤ (A0 - 1) * X.C - A0 := by
    have hqr := mul_le_mul_of_nonneg_left X.r_ear hqX.le
    have hineq : X.C * X.R + X.D * X.B ≤
        X.q * (X.D + X.C - 1) := by
      calc
        X.C * X.R + X.D * X.B = X.q * X.r := by
          nlinarith [X.R_rec]
        _ ≤ X.q * (X.D + X.C - 1) := by
          simpa [add_comm] using hqr
    have hBexpr : X.B = X.q + 1 - X.C := by linarith [hBCeq]
    have hgap :
        0 ≤ X.q * (X.D + X.C - 1) -
          (X.C * X.R + X.D * X.B) := by linarith
    have hid :
        X.q * (X.D + X.C - 1) -
            (X.C * X.R + X.D * X.B) =
          L0 * ((A0 - 1) * X.C - A0) := by
      rw [hBexpr, hD0eq, hq0eq, hReq]
      dsimp [L0, A0, q0]
      field_simp [hs.ne']
      ring
    rw [hid] at hgap
    by_contra hnot
    exact (not_lt_of_ge hgap)
      (mul_neg_of_pos_of_neg hL0pos (lt_of_not_ge hnot))
  have hAB0 : A0 = (A0 - 1) * B0 := by
    dsimp [A0, B0]
    field_simp [hs.ne']
    ring
  have hBLower : B0 ≤ X.B := by
    by_contra hnot
    have hlt : X.B < B0 := lt_of_not_ge hnot
    have hneg : (A0 - 1) * X.B < (A0 - 1) * B0 :=
      mul_lt_mul_of_pos_left hlt (by dsimp [A0]; linarith)
    rw [← hAB0] at hneg
    linarith
  have hCLower : B0 ≤ X.C := by
    by_contra hnot
    have hlt : X.C < B0 := lt_of_not_ge hnot
    have hneg : (A0 - 1) * X.C < (A0 - 1) * B0 :=
      mul_lt_mul_of_pos_left hlt (by dsimp [A0]; linarith)
    rw [← hAB0] at hneg
    linarith
  have hBCtarget : X.B + X.C = 2 * B0 := by
    rw [hBCeq, hq0eq]
    dsimp [q0, B0]
    ring
  have hB : X.B = B0 := by linarith
  have hC : X.C = B0 := by linarith
  have hp : X.p = A0 + 1 / hullSevenCoreRoot := by
    have hrec := X.L_rec
    rw [hB, hC, hLeq, hA0eq, hq0eq] at hrec
    have hid := hullSevenCoreRoot_p_identity
    dsimp [A0, B0, L0, q0] at hrec ⊢
    dsimp at hid
    have hzero :
        (1 + 2 / hullSevenCoreRoot) *
          (X.p - (hullSevenCoreRoot + 1 + 1 / hullSevenCoreRoot)) = 0 := by
      linear_combination hid - hrec
    have hpositive : 0 < 1 + 2 / hullSevenCoreRoot := by positivity
    have hsub := (mul_eq_zero.mp hzero).resolve_left hpositive.ne'
    linarith only [hsub]
  have hr : X.r = A0 + 1 / hullSevenCoreRoot := by
    have hrec := X.R_rec
    rw [hB, hC, hReq, hD0eq, hq0eq] at hrec
    have hid := hullSevenCoreRoot_p_identity
    dsimp [A0, B0, L0, q0] at hrec ⊢
    dsimp at hid
    have hzero :
        (1 + 2 / hullSevenCoreRoot) *
          (X.r - (hullSevenCoreRoot + 1 + 1 / hullSevenCoreRoot)) = 0 := by
      linear_combination hid - hrec
    have hpositive : 0 < 1 + 2 / hullSevenCoreRoot := by positivity
    have hsub := (mul_eq_zero.mp hzero).resolve_left hpositive.ne'
    linarith only [hsub]
  exact
    { area_eq := hH
      A_eq := hA
      D_eq := hD
      surrogate_t_eq := ht
      surrogate_w_eq := hw
      q_eq := hq
      a0_eq := ha0
      a5_eq := ha5
      c_eq := hc
      l_eq := hl
      m_eq := hm
      G_eq := hG
      B_eq := by simpa only [B0] using hB
      C_eq := by simpa only [B0] using hC
      L_eq := by simpa only [L0, q0, A0] using hLeq
      R_eq := by simpa only [L0, q0, A0] using hReq
      p_eq := by simpa only [A0] using hp
      r_eq := by simpa only [A0] using hr }

end Heilbronn8.TriHull
