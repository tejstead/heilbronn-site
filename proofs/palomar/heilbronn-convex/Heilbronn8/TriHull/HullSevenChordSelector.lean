import Heilbronn8.TriHull.HullSevenAllAboveCap
import Heilbronn8.TriHull.HullSevenEndpointHighPoint

/-!
# The source-independent hull-seven chord selector

Every `HullSevenChordInput` contains enough information to produce the
two-outcome selection used by the sharp transfer.  The high-point interval is
the overlap of the left and right surrogate-chord thresholds.  Its
nonemptiness is exactly the denominator-cleared identity already proved as
`hullSevenSurrogate_threshold_identity`.

The high point either lies below the central cap, crosses the cap between it
and an endpoint, or both endpoints lie above the cap.  The last case produces
`HullSevenAllAboveCapData`; no coordinate-box or extra sign hypothesis enters
this module.
-/

namespace Heilbronn8.TriHull

private lemma hullSevenSurrogateP_strictMono {A D q x y : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hq : 0 < q)
    (hx : 0 ≤ x) (hxy : x < y) :
    hullSevenSurrogateP A D q x < hullSevenSurrogateP A D q y := by
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  have hxq : 0 < x + q := add_pos_of_nonneg_of_pos hx hq
  have hyq : 0 < y + q := add_pos hy hq
  have hid :
      hullSevenSurrogateP A D q y - hullSevenSurrogateP A D q x =
        (A + q) * (D + q) * q * (y - x) /
          ((x + q) * (y + q)) := by
    unfold hullSevenSurrogateP
    field_simp [hxq.ne', hyq.ne']
    ring
  rw [← sub_pos, hid]
  have hnum : 0 < (A + q) * (D + q) * q * (y - x) :=
    mul_pos (mul_pos (mul_pos (add_pos hA hq) (add_pos hD hq)) hq)
      (sub_pos.mpr hxy)
  exact div_pos hnum (mul_pos hxq hyq)

private lemma hullSevenSurrogateP_reflect_lt {A D q x y : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hq : 0 < q)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hvalue : hullSevenSurrogateP A D q x <
      hullSevenSurrogateP A D q y) :
    x < y := by
  by_contra hnot
  have hyx : y ≤ x := le_of_not_gt hnot
  rcases hyx.eq_or_lt with heq | hlt
  · subst x
    exact (lt_irrefl _ hvalue)
  · have hmono := hullSevenSurrogateP_strictMono hA hD hq hy hlt
    exact (not_lt_of_ge hmono.le) hvalue

private structure HullSevenSurrogateHighPoint {H : ℝ}
    (X : HullSevenChordInput H) where
  t : ℝ
  w : ℝ
  t_pos : 0 < t
  w_pos : 0 < w
  sum_eq : t + w = X.q - 1
  left_outer : 1 ≤ (X.A - 1) * t
  right_outer : 1 ≤ (X.D - 1) * w
  product_lower :
    X.L * X.R ≤ hullSevenSurrogateP X.A X.D X.q (t * w)

private noncomputable def hullSeven_highPoint {H : ℝ}
    (X : HullSevenChordInput H) : HullSevenSurrogateHighPoint X := by
  let Y := HullSevenEndpointHighPointInput.ofChordInput X
  let P := hullSeven_endpointHighPoint Y
  exact
    { t := P.t
      w := P.w
      t_pos := P.t_pos
      w_pos := P.w_pos
      sum_eq := by
        simpa [Y, HullSevenEndpointHighPointInput.ofChordInput] using P.sum_eq
      left_outer := by
        simpa [Y, HullSevenEndpointHighPointInput.ofChordInput] using P.left_outer
      right_outer := by
        simpa [Y, HullSevenEndpointHighPointInput.ofChordInput] using P.right_outer
      product_lower := by
        simpa [Y, HullSevenEndpointHighPointInput.ofChordInput] using P.product_lower }

private lemma hullSeven_cap_pos {H : ℝ} (X : HullSevenChordInput H) :
    0 < hullSevenCentralCap X.A X.D X.q := by
  have hq : 0 < X.q := lt_of_lt_of_le (by norm_num) X.q_ge
  have hL : 0 < X.L := lt_of_lt_of_le (by norm_num) X.L_ge
  have hR : 0 < X.R := lt_of_lt_of_le (by norm_num) X.R_ge
  have hLR : 0 < X.L * X.R := mul_pos hL hR
  have hcq : X.q ≤ X.c * X.q := by
    have hm := mul_le_mul_of_nonneg_right X.c_ge hq.le
    simpa using hm
  have hnum : 0 < X.A * X.D - X.q := by
    nlinarith [X.LR_rec, hcq, hLR]
  have hden : 0 < X.A + X.D + X.q + 1 := by
    linarith [X.A_ge, X.D_ge, X.q_ge]
  unfold hullSevenCentralCap
  exact div_pos hnum hden

private lemma hullSeven_surrogateP_at_cap {H : ℝ}
    (X : HullSevenChordInput H) :
    hullSevenSurrogateP X.A X.D X.q
        (hullSevenCentralCap X.A X.D X.q) =
      X.A * X.D - X.q := by
  have hq : 0 < X.q := lt_of_lt_of_le (by norm_num) X.q_ge
  have hz : 0 < hullSevenCentralCap X.A X.D X.q := hullSeven_cap_pos X
  have hden : 0 < X.A + X.D + X.q + 1 := by
    linarith [X.A_ge, X.D_ge, X.q_ge]
  have hid := hullSevenSurrogate_cap_identity hq (add_pos hz hq) hden
  rw [sub_self, mul_zero, zero_div] at hid
  linarith

private lemma hullSeven_LR_le_capProduct {H : ℝ}
    (X : HullSevenChordInput H) :
    X.L * X.R ≤ X.A * X.D - X.q := by
  have hq : 0 ≤ X.q := le_trans (by norm_num) X.q_ge
  have hm := mul_le_mul_of_nonneg_right X.c_ge hq
  rw [X.LR_rec]
  nlinarith

private noncomputable def hullSevenCappedAt {H : ℝ}
    (X : HullSevenChordInput H) (t : ℝ)
    (ht : 0 < t) (hw : 0 < X.q - 1 - t)
    (hleft : 1 ≤ (X.A - 1) * t)
    (hright : 1 ≤ (X.D - 1) * (X.q - 1 - t))
    (hproduct : X.L * X.R ≤
      hullSevenSurrogateP X.A X.D X.q (t * (X.q - 1 - t)))
    (hcap : hullSevenSurrogateP X.A X.D X.q
      (t * (X.q - 1 - t)) ≤ X.A * X.D - X.q) :
    HullSevenCappedSurrogate X where
  t := t
  w := X.q - 1 - t
  t_pos := ht
  w_pos := hw
  sum_eq := by ring
  left_outer := hleft
  right_outer := hright
  product_lower := hproduct
  product_upper := hcap

private lemma hullSeven_capped_at_cap_root {H : ℝ}
    (X : HullSevenChordInput H) (t : ℝ)
    (ht : 0 < t) (hw : 0 < X.q - 1 - t)
    (hleft : 1 ≤ (X.A - 1) * t)
    (hright : 1 ≤ (X.D - 1) * (X.q - 1 - t))
    (hz : t * (X.q - 1 - t) = hullSevenCentralCap X.A X.D X.q) :
    Nonempty (HullSevenCappedSurrogate X) := by
  refine ⟨hullSevenCappedAt X t ht hw hleft hright ?_ ?_⟩
  · rw [hz, hullSeven_surrogateP_at_cap]
    exact hullSeven_LR_le_capProduct X
  · rw [hz, hullSeven_surrogateP_at_cap]

private noncomputable def hullSeven_allAboveData {H : ℝ}
    (X : HullSevenChordInput H)
    (hinterval : 1 / (X.A - 1) ≤ X.q - 1 - 1 / (X.D - 1))
    (hleftAbove : hullSevenCentralCap X.A X.D X.q <
      (1 / (X.A - 1)) * (X.q - 1 - 1 / (X.A - 1))) :
    HullSevenAllAboveCapData H := by
  let s := X.A - 1
  let u := X.D - 1
  let z := hullSevenCentralCap X.A X.D X.q
  let rho := Real.sqrt z
  have hs : 0 < s := sub_pos.mpr (hullSeven_left_endpoint_preserved X).1
  have hu : 0 < u := sub_pos.mpr (hullSeven_right_endpoint_preserved X).1
  have hz : 0 < z := by dsimp [z]; exact hullSeven_cap_pos X
  have hrho : 0 < rho := by dsimp [rho]; exact Real.sqrt_pos.2 hz
  have hrho2 : rho ^ 2 = z := by
    dsimp [rho]
    exact Real.sq_sqrt hz.le
  have hleftScaled : s * z + 1 / s < X.q - 1 := by
    have hleftAbove' :
        z < (1 / s) * (X.q - 1 - 1 / s) := by
      simpa [s, z] using hleftAbove
    have hm := mul_lt_mul_of_pos_left hleftAbove' hs
    have hcancel :
        s * ((1 / s) * (X.q - 1 - 1 / s)) =
          X.q - 1 - 1 / s := by
      field_simp [hs.ne']
    rw [hcancel] at hm
    linarith
  have hradialAMGM : 2 * rho ≤ s * z + 1 / s := by
    have hsquare := sq_nonneg (s * rho - 1)
    rw [← hrho2]
    have hform :
        s * rho ^ 2 + 1 / s = (s ^ 2 * rho ^ 2 + 1) / s := by
      field_simp [hs.ne']
    rw [hform]
    apply (le_div_iff₀ hs).2
    nlinarith
  have hradial : 1 + 2 * rho ≤ X.q := by linarith
  have hradialStrict : 1 + 2 * rho < X.q := by
    linarith [hradialAMGM, hleftScaled]
  have hcapIdentity :
      (s + 1 - rho ^ 2) * (u + 1 - rho ^ 2) =
        (1 + rho ^ 2) * (X.q + rho ^ 2) := by
    rw [hrho2]
    have hden : 0 < X.A + X.D + X.q + 1 := by
      linarith [X.A_ge, X.D_ge, X.q_ge]
    have hcapEq :
        z * (X.A + X.D + X.q + 1) = X.A * X.D - X.q := by
      dsimp [z]
      unfold hullSevenCentralCap
      field_simp [hden.ne']
    dsimp [s, u]
    nlinarith [hcapEq]
  have hclosing : 1 / rho ^ 2 ≤ X.G := by
    rw [hrho2]
    apply hullSeven_surrogate_closing_le X hz
    rw [hullSeven_surrogateP_at_cap]
    exact hullSeven_LR_le_capProduct X
  have harea : 5 + X.q + s + u + 1 / rho ^ 2 ≤ H := by
    have hBC : X.q + 1 ≤ X.B + X.C := by linarith [X.q_ear]
    linarith [X.area, X.a0_ge, X.a5_ge, hclosing]
  exact
    { s := s
      u := u
      q := X.q
      rho := rho
      s_pos := hs
      u_pos := hu
      rho_pos := hrho
      radial_q := hradial
      radial_q_strict := hradialStrict
      interval := by
        dsimp [s, u]
        linarith [hinterval]
      cap_identity := hcapIdentity
      area := harea }

/-- Every abstract chord input has the exact capped/all-above selection used
by the sharp transfer. -/
theorem hullSevenChordSelection_proved {H : ℝ}
    (X : HullSevenChordInput H) : HullSevenChordSelection X := by
  let high := hullSeven_highPoint X
  let s := X.A - 1
  let u := X.D - 1
  let lo := 1 / s
  let hi := X.q - 1 - 1 / u
  let zcap := hullSevenCentralCap X.A X.D X.q
  let zfun : ℝ → ℝ := fun t => hullSevenTransferZ X.q t
  have hs : 0 < s := sub_pos.mpr (hullSeven_left_endpoint_preserved X).1
  have hu : 0 < u := sub_pos.mpr (hullSeven_right_endpoint_preserved X).1
  have htlo : lo ≤ high.t := by
    have hm : 1 / s ≤ high.t := by
      apply (div_le_iff₀ hs).2
      simpa [mul_comm] using high.left_outer
    simpa [lo] using hm
  have hthi : high.t ≤ hi := by
    have hm : 1 / u ≤ high.w := by
      apply (div_le_iff₀ hu).2
      simpa [mul_comm] using high.right_outer
    dsimp [hi, u]
    linarith [high.sum_eq]
  have hinterval : lo ≤ hi := le_trans htlo hthi
  have hzcap : 0 < zcap := by dsimp [zcap]; exact hullSeven_cap_pos X
  have hzhigh : zfun high.t = high.t * high.w := by
    dsimp [zfun, hullSevenTransferZ]
    linear_combination -high.t * high.sum_eq
  by_cases hhighCap :
      hullSevenSurrogateP X.A X.D X.q (high.t * high.w) ≤
        X.A * X.D - X.q
  · left
    exact ⟨
      { t := high.t
        w := high.w
        t_pos := high.t_pos
        w_pos := high.w_pos
        sum_eq := high.sum_eq
        left_outer := high.left_outer
        right_outer := high.right_outer
        product_lower := high.product_lower
        product_upper := hhighCap }⟩
  · have hcapValue :
        hullSevenSurrogateP X.A X.D X.q zcap =
          X.A * X.D - X.q := by
      dsimp [zcap]
      exact hullSeven_surrogateP_at_cap X
    have hPstrict :
        hullSevenSurrogateP X.A X.D X.q zcap <
          hullSevenSurrogateP X.A X.D X.q (high.t * high.w) := by
      rw [hcapValue]
      exact lt_of_not_ge hhighCap
    have hhighZ : zcap < high.t * high.w := by
      have hA : 0 < X.A := lt_of_lt_of_le (by norm_num) X.A_ge
      have hD : 0 < X.D := lt_of_lt_of_le (by norm_num) X.D_ge
      have hq : 0 < X.q := lt_of_lt_of_le (by norm_num) X.q_ge
      have htw : 0 ≤ high.t * high.w := (mul_pos high.t_pos high.w_pos).le
      exact hullSevenSurrogateP_reflect_lt hA hD hq hzcap.le htw hPstrict
    have hzfunHigh : zcap < zfun high.t := by simpa [hzhigh] using hhighZ
    by_cases hleft : zfun lo ≤ zcap
    · have hcont : ContinuousOn zfun (Set.Icc lo high.t) := by
        apply Continuous.continuousOn
        dsimp [zfun, hullSevenTransferZ]
        fun_prop
      have hsub := intermediate_value_Icc htlo hcont
      have hmem : zcap ∈ Set.Icc (zfun lo) (zfun high.t) :=
        ⟨hleft, hzfunHigh.le⟩
      obtain ⟨t, ht, htz⟩ := hsub hmem
      left
      apply hullSeven_capped_at_cap_root X t
      · exact lt_of_lt_of_le (one_div_pos.mpr hs) ht.1
      · have : t ≤ hi := le_trans ht.2 hthi
        dsimp [hi, u] at this
        exact lt_of_lt_of_le (one_div_pos.mpr hu) (by linarith)
      · have hm := mul_le_mul_of_nonneg_left ht.1 hs.le
        have hlo : s * lo = 1 := by
          dsimp [lo]
          field_simp [hs.ne']
        rw [hlo] at hm
        simpa [s] using hm
      · have hti : t ≤ hi := le_trans ht.2 hthi
        have hm := mul_le_mul_of_nonneg_left
          (show 1 / u ≤ X.q - 1 - t by dsimp [hi] at hti; linarith) hu.le
        simpa [u, hu.ne'] using hm
      · simpa [zfun, hullSevenTransferZ, zcap] using htz
    · have hleftAbove : zcap < zfun lo := lt_of_not_ge hleft
      by_cases hright : zfun hi ≤ zcap
      · let negZ : ℝ → ℝ := fun t => -zfun t
        have hcont : ContinuousOn negZ (Set.Icc high.t hi) := by
          apply Continuous.continuousOn
          dsimp [negZ, zfun, hullSevenTransferZ]
          fun_prop
        have hsub := intermediate_value_Icc hthi hcont
        have hmem : -zcap ∈ Set.Icc (negZ high.t) (negZ hi) := by
          dsimp [negZ]
          constructor <;> linarith [hzfunHigh]
        obtain ⟨t, ht, htz⟩ := hsub hmem
        left
        apply hullSeven_capped_at_cap_root X t
        · exact lt_of_lt_of_le high.t_pos ht.1
        · have hti := ht.2
          dsimp [hi, u] at hti
          exact lt_of_lt_of_le (one_div_pos.mpr hu) (by linarith)
        · have htl : lo ≤ t := le_trans htlo ht.1
          have hm := mul_le_mul_of_nonneg_left htl hs.le
          have hlo : s * lo = 1 := by
            dsimp [lo]
            field_simp [hs.ne']
          rw [hlo] at hm
          simpa [s] using hm
        · have hm := mul_le_mul_of_nonneg_left
            (show 1 / u ≤ X.q - 1 - t by
              have hti : t ≤ hi := ht.2
              dsimp [hi] at hti
              linarith) hu.le
          simpa [u, hu.ne'] using hm
        · have : zfun t = zcap := by dsimp [negZ] at htz; linarith
          simpa [zfun, hullSevenTransferZ, zcap] using this
      · right
        refine ⟨hullSeven_allAboveData X (by simpa [lo, hi, s, u] using hinterval) ?_⟩
        have : zfun lo = lo * (X.q - 1 - lo) := by
          rfl
        rw [this] at hleftAbove
        simpa [lo, s, zcap] using hleftAbove

/-- At or below the sharp normalized area, the strict all-above alternative
is impossible, so the selector necessarily returns a capped surrogate. -/
theorem hullSevenCappedSurrogate_exists_of_v8_upper {H : ℝ}
    (X : HullSevenChordInput H)
    (hupper : v8 * H ≤ 1) :
    Nonempty (HullSevenCappedSurrogate X) := by
  rcases hullSevenChordSelection_proved X with hcap | habove
  · exact hcap
  · rcases habove with ⟨data⟩
    exact (data.not_v8_boundary hupper).elim

/-- The complete abstract chord theorem: only construction of
`HullSevenChordInput` remains geometric/chamber-specific. -/
theorem hullSeven_v8_of_chord_input {H : ℝ}
    (X : HullSevenChordInput H) : 1 ≤ v8 * H :=
  hullSeven_v8_of_chord_input_split X
    (hullSevenChordSelection_proved X)
    hullSevenAllAboveCapClosure_proved

end Heilbronn8.TriHull
