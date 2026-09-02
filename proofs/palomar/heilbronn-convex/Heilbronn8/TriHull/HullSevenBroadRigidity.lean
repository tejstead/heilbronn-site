import Heilbronn8.TriHull.HullSevenBroadCore

/-!
# Equality rigidity for the broad hull-seven scalar core

This is a phase-two optimizer-classification draft.  It deliberately lives
outside the frozen `Heilbronn8` package until it has been source-audited and
typechecked in the dedicated build lane.

The sharp lower-bound proof in `HullSevenBroadCore` is monotone.  At equality
none of its transfer slack can remain: the radial parameter is the reciprocal
of `hullSevenCoreRoot`, both geometric-mean steps are equalities, both outer
floors are equalities, and the closing floor is an equality.
-/

namespace Heilbronn8.TriHull

/-- Strict form of the outer radial monotonicity used by equality analysis. -/
lemma hullSevenRadialOuter_strictAnti {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy : y ≤ 1) :
    hullSevenRadialOuter y < hullSevenRadialOuter x := by
  have hy0 : 0 < y := lt_trans hx hxy
  have hx1 : x ≤ 1 := le_trans hxy.le hy
  have hprodLe : x * y ≤ 1 := by
    have hmul : x * y ≤ x := by
      nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hy)]
    exact le_trans hmul hx1
  have hxy0 : 0 < x * y := mul_pos hx hy0
  have hinv : 1 ≤ 1 / (x * y) := by
    apply (le_div_iff₀ hxy0).2
    simpa using hprodLe
  have hlast : 0 < (x + y) / (x ^ 2 * y ^ 2) := by positivity
  have hbracket :
      0 < -2 + 2 / (x * y) + (x + y) / (x ^ 2 * y ^ 2) := by
    have htwice : 2 ≤ 2 / (x * y) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hid :
      hullSevenRadialOuter x - hullSevenRadialOuter y =
        (y - x) *
          (-2 + 2 / (x * y) + (x + y) / (x ^ 2 * y ^ 2)) := by
    unfold hullSevenRadialOuter
    field_simp [hx.ne', hy0.ne']
    ring
  rw [← sub_pos, hid]
  exact mul_pos (sub_pos.mpr hxy) hbracket

/-- Strict form of central radial monotonicity.  The proof is the same
`19/60`-margin argument as the non-strict theorem in `HullSevenBroadCore`. -/
lemma hullSevenRadialCentral_strictMono {x y : ℝ}
    (hx : (2 / 3 : ℝ) ≤ x) (hxy : x < y) :
    hullSevenRadialCentral x < hullSevenRadialCentral y := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hy0 : 0 < y := lt_trans hx0 hxy
  have hxyLe : x ≤ y := hxy.le
  have hsquares : x ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxyLe) (by positivity : 0 ≤ x + y)]
  have hsqrt :
      Real.sqrt (x ^ 2 + 1) ≤ Real.sqrt (y ^ 2 + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hySquare : (4 / 9 : ℝ) ≤ y ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ y - 2 / 3)
      (by positivity : 0 ≤ y + 2 / 3)]
  have hrootSquare :
      (Real.sqrt (y ^ 2 + 1)) ^ 2 = y ^ 2 + 1 :=
    Real.sq_sqrt (by positivity)
  have hrootLower : (6 / 5 : ℝ) ≤ Real.sqrt (y ^ 2 + 1) := by
    have hroot0 := Real.sqrt_nonneg (y ^ 2 + 1)
    nlinarith
  have hrootProduct :
      (6 / 5 : ℝ) * (y - x) ≤
        (y + 1) * Real.sqrt (y ^ 2 + 1) -
          (x + 1) * Real.sqrt (x ^ 2 + 1) := by
    have hid :
        (y + 1) * Real.sqrt (y ^ 2 + 1) -
            (x + 1) * Real.sqrt (x ^ 2 + 1) =
          (y - x) * Real.sqrt (y ^ 2 + 1) +
            (x + 1) *
              (Real.sqrt (y ^ 2 + 1) - Real.sqrt (x ^ 2 + 1)) := by
      ring
    rw [hid]
    have hfirst := mul_le_mul_of_nonneg_left hrootLower
      (sub_nonneg.mpr hxyLe)
    have hsecond :
        0 ≤ (x + 1) *
          (Real.sqrt (y ^ 2 + 1) - Real.sqrt (x ^ 2 + 1)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hsqrt)
    linarith
  have hpoly : 4 * (x + y) ≤ 27 * x ^ 2 * y ^ 2 := by
    let a := x - 2 / 3
    let b := y - 2 / 3
    have ha : 0 ≤ a := by dsimp [a]; linarith
    have hb : 0 ≤ b := by dsimp [b]; linarith
    have hid :
        27 * x ^ 2 * y ^ 2 - 4 * (x + y) =
          12 * a + 12 * b + 12 * a ^ 2 + 12 * b ^ 2 +
            48 * a * b + 36 * a ^ 2 * b + 36 * a * b ^ 2 +
              27 * a ^ 2 * b ^ 2 := by
      dsimp [a, b]
      ring
    rw [← sub_nonneg, hid]
    positivity
  have hden : 0 < x ^ 2 * y ^ 2 := by positivity
  have hcoefficient :
      (x + y) / (x ^ 2 * y ^ 2) ≤ 27 / 4 := by
    apply (div_le_iff₀ hden).2
    nlinarith [hpoly]
  have hcoefficientMul := mul_le_mul_of_nonneg_left hcoefficient
    (sub_nonneg.mpr hxyLe)
  have hreciprocal :
      1 / y ^ 2 - 1 / x ^ 2 =
        -(y - x) * ((x + y) / (x ^ 2 * y ^ 2)) := by
    field_simp [hx0.ne', hy0.ne']
    ring
  have hdiff :
      hullSevenRadialCentral y - hullSevenRadialCentral x =
        2 * (y - x) + 2 * (y ^ 2 - x ^ 2) +
          (1 / y ^ 2 - 1 / x ^ 2) +
            2 * ((y + 1) * Real.sqrt (y ^ 2 + 1) -
              (x + 1) * Real.sqrt (x ^ 2 + 1)) := by
    unfold hullSevenRadialCentral
    ring
  rw [← sub_pos, hdiff, hreciprocal]
  have hsum : (4 / 3 : ℝ) ≤ x + y := by linarith
  have hmargin : (0 : ℝ) < (19 / 60) * (y - x) := by positivity
  nlinarith

/-- The exact tuple forced in the broad scalar core at the `v8` boundary. -/
structure HullSevenBroadRigidity {H : ℝ}
    (D : HullSevenBroadTransferData H) : Prop where
  area_eq : H = hullSevenSharpH
  s_eq : D.s = hullSevenCoreRoot
  t_eq : D.t = 1 / hullSevenCoreRoot
  w_eq : D.w = 1 / hullSevenCoreRoot
  u_eq : D.u = hullSevenCoreRoot
  G_eq : D.G = hullSevenCoreRoot ^ 2

/-- Boundary rigidity for the broad transfer. -/
theorem hullSeven_broad_transfer_rigidity {H : ℝ}
    (D : HullSevenBroadTransferData H)
    (hboundary : v8 * H ≤ 1) :
    HullSevenBroadRigidity D := by
  have hlower := hullSeven_v8_of_broad_transfer D
  have hprod : v8 * H = 1 := le_antisymm hboundary hlower
  have hH : H = hullSevenSharpH := by
    have hsharp := v8_mul_hullSevenSharpH
    nlinarith [v8_pos]

  let z := D.t * D.w
  let r := Real.sqrt z
  let r0 := 1 / hullSevenCoreRoot
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos D.t_pos D.w_pos
  have hr : 0 < r := by dsimp [r]; exact Real.sqrt_pos.2 hz
  have hrsq : r ^ 2 = D.t * D.w := by
    dsimp [r, z]
    exact Real.sq_sqrt (mul_pos D.t_pos D.w_pos).le
  have hr0pos : 0 < r0 := by
    dsimp [r0]
    exact one_div_pos.mpr hullSevenCoreRoot_pos
  have hr0lo : (2 / 3 : ℝ) ≤ r0 := by
    dsimp [r0]
    exact hullSevenReciprocalRoot_mem.1
  have hr0hi : r0 ≤ 1 := by
    dsimp [r0]
    exact hullSevenReciprocalRoot_mem.2

  have htw : 2 * r ≤ D.t + D.w := by
    nlinarith only [D.t_pos, D.w_pos, hr,
      sq_nonneg (D.t - D.w), hrsq]
  have hsInv : 1 / D.t ≤ D.s := by
    apply (div_le_iff₀ D.t_pos).2
    simpa using D.left_outer
  have huInv : 1 / D.w ≤ D.u := by
    apply (div_le_iff₀ D.w_pos).2
    simpa using D.right_outer
  have hinvIdentity : 1 / D.t + 1 / D.w = (D.t + D.w) / r ^ 2 := by
    field_simp [D.t_pos.ne', D.w_pos.ne', hr.ne']
    nlinarith [hrsq]
  have hinvLower : 2 / r ≤ 1 / D.t + 1 / D.w := by
    rw [hinvIdentity]
    apply (div_le_div_iff₀ hr (sq_pos_of_pos hr)).2
    nlinarith [hrsq, mul_nonneg (sub_nonneg.mpr htw) hr.le]
  have hsu : 2 / r ≤ D.s + D.u :=
    le_trans hinvLower (add_le_add hsInv huInv)
  have hGr : 1 / r ^ 2 ≤ D.G := by
    rw [hrsq]
    simpa [z] using D.closing
  have houter :
      hullSevenRadialOuter r ≤ 6 + D.s + D.t + D.w + D.u + D.G := by
    unfold hullSevenRadialOuter
    linarith

  obtain ⟨ha, hb⟩ :=
    hullSeven_shifted_factors_pos D.s_pos D.t_pos D.w_pos D.u_pos D.central
  let a := D.s + 1 - z
  let b := D.u + 1 - z
  have ha' : 0 < a := by simpa [a, z] using ha
  have hb' : 0 < b := by simpa [b, z] using hb
  have htwFactor : (r + 1) ^ 2 ≤ (D.t + 1) * (D.w + 1) := by
    nlinarith [hrsq]
  have hfactorBound :
      (r + 1) ^ 2 * (r ^ 2 + 1) ≤ a * b := by
    calc
      (r + 1) ^ 2 * (r ^ 2 + 1) ≤
          (D.t + 1) * (D.w + 1) * (r ^ 2 + 1) := by
        exact mul_le_mul_of_nonneg_right htwFactor (by positivity)
      _ = (D.t + 1) * (D.w + 1) * (z + 1) := by rw [hrsq]
      _ ≤ a * b := by simpa [a, b, z] using D.central
  have habSquare : 4 * a * b ≤ (a + b) ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hsqrtSq :
      (Real.sqrt (r ^ 2 + 1)) ^ 2 = r ^ 2 + 1 :=
    Real.sq_sqrt (by positivity)
  have htargetSquare :
      (2 * (r + 1) * Real.sqrt (r ^ 2 + 1)) ^ 2 ≤
        (a + b) ^ 2 := by
    calc
      (2 * (r + 1) * Real.sqrt (r ^ 2 + 1)) ^ 2 =
          4 * (r + 1) ^ 2 * (r ^ 2 + 1) := by
        rw [mul_pow, mul_pow, hsqrtSq]
        ring
      _ ≤ 4 * (a * b) := by nlinarith [hfactorBound]
      _ ≤ (a + b) ^ 2 := by nlinarith [habSquare]
  have htargetPos :
      0 ≤ 2 * (r + 1) * Real.sqrt (r ^ 2 + 1) := by positivity
  have habSumPos : 0 ≤ a + b := by linarith
  have hshifted :
      2 * (r + 1) * Real.sqrt (r ^ 2 + 1) ≤ a + b :=
    (sq_le_sq₀ htargetPos habSumPos).1 htargetSquare
  have hsuCentralZ :
      2 * z - 2 + 2 * (r + 1) * Real.sqrt (r ^ 2 + 1) ≤
        D.s + D.u := by
    dsimp [a, b] at hshifted
    dsimp [z] at hshifted ⊢
    linarith
  have hsuCentral :
      2 * r ^ 2 - 2 + 2 * (r + 1) * Real.sqrt (r ^ 2 + 1) ≤
        D.s + D.u := by
    simpa [z, hrsq] using hsuCentralZ
  have hcentral :
      hullSevenRadialCentral r ≤
        6 + D.s + D.t + D.w + D.u + D.G := by
    unfold hullSevenRadialCentral
    linarith [hsuCentral, htw, hGr]

  have htotal : 6 + D.s + D.t + D.w + D.u + D.G ≤
      hullSevenSharpH := by simpa [hH] using D.area
  have hrEq : r = r0 := by
    rcases lt_trichotomy r r0 with hlt | heq | hgt
    · have hstrict := hullSevenRadialOuter_strictAnti hr hlt hr0hi
      have hat : hullSevenRadialOuter r0 = hullSevenSharpH := by
        dsimp [r0]
        exact hullSevenRadialOuter_at_reciprocalRoot
      rw [hat] at hstrict
      linarith [houter, htotal]
    · exact heq
    · have hstrict := hullSevenRadialCentral_strictMono hr0lo hgt
      have hat : hullSevenRadialCentral r0 = hullSevenSharpH := by
        dsimp [r0]
        exact hullSevenRadialCentral_at_reciprocalRoot
      rw [hat] at hstrict
      linarith [hcentral, htotal]

  have houterAt : hullSevenRadialOuter r = hullSevenSharpH := by
    rw [hrEq]
    dsimp [r0]
    exact hullSevenRadialOuter_at_reciprocalRoot
  have htwEq : D.t + D.w = 2 * r := by
    unfold hullSevenRadialOuter at houterAt houter
    linarith [houter, htotal, htw, hsu, hGr]
  have hsuEq : D.s + D.u = 2 / r := by
    unfold hullSevenRadialOuter at houterAt houter
    linarith [houter, htotal, htw, hsu, hGr]
  have hGEq : D.G = 1 / r ^ 2 := by
    unfold hullSevenRadialOuter at houterAt houter
    linarith [houter, htotal, htw, hsu, hGr]
  have htwVars : D.t = r ∧ D.w = r := by
    have hsq : (D.t - D.w) ^ 2 = 0 := by
      calc
        (D.t - D.w) ^ 2 = (D.t + D.w) ^ 2 - 4 * (D.t * D.w) := by ring
        _ = (2 * r) ^ 2 - 4 * r ^ 2 := by rw [htwEq, ← hrsq]
        _ = 0 := by ring
    constructor <;> nlinarith only [hsq, htwEq]
  rcases htwVars with ⟨htEq, hwEq⟩
  have hsInvEq : 1 / r ≤ D.s := by simpa [htEq] using hsInv
  have huInvEq : 1 / r ≤ D.u := by simpa [hwEq] using huInv
  have hsuEq' : D.s + D.u = 1 / r + 1 / r := by
    calc
      D.s + D.u = 2 / r := hsuEq
      _ = 1 / r + 1 / r := by ring
  have hsuVars : D.s = 1 / r ∧ D.u = 1 / r := by
    constructor <;> linarith only [hsuEq', hsInvEq, huInvEq]
  rcases hsuVars with ⟨hsEq, huEq⟩
  have hinvR0 : 1 / r0 = hullSevenCoreRoot := by
    dsimp [r0]
    field_simp [hullSevenCoreRoot_pos.ne']
  have hsqR0 : 1 / r0 ^ 2 = hullSevenCoreRoot ^ 2 := by
    calc
      1 / r0 ^ 2 = (1 / r0) ^ 2 := by ring
      _ = hullSevenCoreRoot ^ 2 := by rw [hinvR0]
  refine
    { area_eq := hH
      s_eq := ?_
      t_eq := ?_
      w_eq := ?_
      u_eq := ?_
      G_eq := ?_ }
  · rw [hsEq, hrEq, hinvR0]
  · rw [htEq, hrEq]
  · rw [hwEq, hrEq]
  · rw [huEq, hrEq, hinvR0]
  · rw [hGEq, hrEq, hsqR0]

/-- Conjunction-shaped compatibility API used by the capped-chord rigidity
layer.  It is a direct unpacking of `hullSeven_broad_transfer_rigidity`. -/
theorem HullSevenBroadTransferData.rigid_of_v8_upper {H : ℝ}
    (data : HullSevenBroadTransferData H)
    (hupper : v8 * H ≤ 1) :
    data.s = hullSevenCoreRoot ∧
      data.t = 1 / hullSevenCoreRoot ∧
      data.w = 1 / hullSevenCoreRoot ∧
      data.u = hullSevenCoreRoot ∧
      data.G = hullSevenCoreRoot ^ 2 ∧
      H = hullSevenSharpH := by
  have rigid := hullSeven_broad_transfer_rigidity data hupper
  exact ⟨rigid.s_eq, rigid.t_eq, rigid.w_eq, rigid.u_eq,
    rigid.G_eq, rigid.area_eq⟩

end Heilbronn8.TriHull
