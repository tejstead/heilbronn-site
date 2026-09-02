import Heilbronn8.TriHull.HullSevenBroadCore

/-!
# Exact algebra for the hull-seven broad transfer

These are the denominator-cleared identities used by the endpoint/central-ear
surrogate.  The future geometric producer only has to derive their positivity
hypotheses from the common C24 chord chamber.
-/

namespace Heilbronn8.TriHull

noncomputable def hullSevenSurrogateL (s t q : ℝ) : ℝ :=
  t * (q + s + 1) / (t + 1)

noncomputable def hullSevenSurrogateP (A D q z : ℝ) : ℝ :=
  (A + q) * (D + q) * z / (z + q)

noncomputable def hullSevenCentralCap (A D q : ℝ) : ℝ :=
  (A * D - q) / (A + D + q + 1)

/-- Product of the left and right central-ear-tight chords. -/
lemma hullSevenSurrogate_product {s t w u q : ℝ}
    (ht : 0 < t) (hw : 0 < w) (hsum : t + w = q - 1) :
    hullSevenSurrogateL s t q * hullSevenSurrogateL u w q =
      hullSevenSurrogateP (s + 1) (u + 1) q (t * w) := by
  have hq : q = t + w + 1 := by linarith
  subst q
  have ht1 : t + 1 ≠ 0 := ne_of_gt (by positivity)
  have hw1 : w + 1 ≠ 0 := ne_of_gt (by positivity)
  have hsumPos : 0 < t * w + (t + w + 1) := by positivity
  unfold hullSevenSurrogateL hullSevenSurrogateP
  field_simp [ht1, hw1, hsumPos.ne']
  ring

/-- The surrogate closing fan cell is exactly `1/z`. -/
lemma hullSevenSurrogate_closing {A D q z : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hq : 0 < q) (hz : 0 < z) :
    let P := hullSevenSurrogateP A D q z
    (((A * D - P) / q + A + D + q) / P) = 1 / z := by
  dsimp
  unfold hullSevenSurrogateP
  have hzq : z + q ≠ 0 := ne_of_gt (add_pos hz hq)
  have hAq : A + q ≠ 0 := ne_of_gt (add_pos hA hq)
  have hDq : D + q ≠ 0 := ne_of_gt (add_pos hD hq)
  field_simp [hq.ne', hz.ne', hzq, hAq, hDq]
  ring

/-- Difference from the central floor threshold, before taking signs. -/
lemma hullSevenSurrogate_cap_identity {A D q z : ℝ}
    (hq : 0 < q) (hzq : 0 < z + q) (hden : 0 < A + D + q + 1) :
    hullSevenSurrogateP A D q z - (A * D - q) =
      q * (A + D + q + 1) *
        (z - hullSevenCentralCap A D q) / (z + q) := by
  unfold hullSevenSurrogateP hullSevenCentralCap
  field_simp [hq.ne', hzq.ne', hden.ne']
  ring

/-- After `q=t+w+1`, the floor `c' >= 1` is exactly the shifted-product
condition consumed by `hullSeven_broad_core_v8`. -/
lemma hullSevenCentral_floor_identity {s t w u : ℝ} :
    let A := s + 1
    let D := u + 1
    let q := t + w + 1
    let z := t * w
    (A * D - q) * (z + q) - z * (A + q) * (D + q) =
      q * ((A - z) * (D - z) - (t + 1) * (w + 1) * (z + 1)) := by
  dsimp
  ring

/-- Semantic sign consequence of `hullSevenCentral_floor_identity`: a
surrogate central chord of magnitude at least one supplies exactly the broad
core's shifted-product hypothesis. -/
lemma hullSevenBroadCentral_of_surrogate_floor {s t w u : ℝ}
    (ht : 0 < t) (hw : 0 < w)
    (hfloor :
      1 ≤ (((s + 1) * (u + 1) -
        hullSevenSurrogateP (s + 1) (u + 1) (t + w + 1) (t * w)) /
          (t + w + 1))) :
    (t + 1) * (w + 1) * (t * w + 1) ≤
      (s + 1 - t * w) * (u + 1 - t * w) := by
  let A := s + 1
  let D := u + 1
  let q := t + w + 1
  let z := t * w
  let P := hullSevenSurrogateP A D q z
  have hq : 0 < q := by dsimp [q]; positivity
  have hzq : 0 < z + q := by dsimp [z, q]; positivity
  have hP : P ≤ A * D - q := by
    have hscaled := (le_div_iff₀ hq).1 (by simpa [A, D, q, z, P] using hfloor)
    linarith
  have hPidentity : P * (z + q) = z * (A + q) * (D + q) := by
    unfold P hullSevenSurrogateP
    field_simp [hzq.ne']
  have hleft :
      0 ≤ (A * D - q) * (z + q) - z * (A + q) * (D + q) := by
    have hscaled := mul_le_mul_of_nonneg_right hP hzq.le
    rw [hPidentity] at hscaled
    linarith
  have hid := hullSevenCentral_floor_identity (s := s) (t := t) (w := w)
    (u := u)
  have hid' :
      (A * D - q) * (z + q) - z * (A + q) * (D + q) =
        q * ((A - z) * (D - z) -
          (t + 1) * (w + 1) * (z + 1)) := by
    simpa [A, D, q, z] using hid
  have hproduct :
      0 ≤ q *
        ((A - z) * (D - z) - (t + 1) * (w + 1) * (z + 1)) := by
    rw [← hid']
    exact hleft
  by_contra hnot
  have hneg :
      (A - z) * (D - z) - (t + 1) * (w + 1) * (z + 1) < 0 := by
    dsimp [A, D, z]
    linarith
  exact (not_lt_of_ge hproduct) (mul_neg_of_pos_of_neg hq hneg)

/-- Package a valid central-ear surrogate into the exact broad-transfer seam.
The remaining geometric argument only has to select `t,w` and prove the
displayed floor and area comparison. -/
noncomputable def hullSevenBroadTransferData_of_surrogate {H s t w u : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hw : 0 < w) (hu : 0 < u)
    (hst : 1 ≤ s * t) (huw : 1 ≤ u * w)
    (hfloor :
      1 ≤ (((s + 1) * (u + 1) -
        hullSevenSurrogateP (s + 1) (u + 1) (t + w + 1) (t * w)) /
          (t + w + 1)))
    (harea : 6 + s + t + w + u + 1 / (t * w) ≤ H) :
    HullSevenBroadTransferData H := by
  refine
    { s := s
      t := t
      w := w
      u := u
      G := 1 / (t * w)
      s_pos := hs
      t_pos := ht
      w_pos := hw
      u_pos := hu
      left_outer := hst
      right_outer := huw
      closing := le_rfl
      central := hullSevenBroadCentral_of_surrogate_floor ht hw hfloor
      area := harea }

/-- Exact endpoint-slack factorization.  It shows that `s*t >= 1` is the
condition for the surrogate chord to stay above the endpoint floor. -/
lemma hullSevenSurrogate_endpoint_identity {s t q : ℝ}
    (hs : 0 < s + 1) (ht : 0 < t + 1) :
    hullSevenSurrogateL s t q - (1 + q / (s + 1)) =
      (s * t - 1) * (q + s + 1) / ((s + 1) * (t + 1)) := by
  unfold hullSevenSurrogateL
  field_simp [hs.ne', ht.ne']
  ring

/-- Corrected high-point threshold identity.  An earlier informal statement
omitted the leading factor `d`; the sign conclusion is unchanged. -/
lemma hullSevenSurrogate_threshold_identity {s u v w d q : ℝ}
    (hs : 0 < s) (hu : 0 < u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hd : 0 ≤ d) (hq : q = v + w + 1 - d)
    (hD0 : 0 < q + s + 1 + d * (s + 1))
    (hD1 : 0 < q + u + 1 + d * (u + 1)) :
    let D0 := q + s + 1 + d * (s + 1)
    let D1 := q + u + 1 + d * (u + 1)
    let t0 := (v * (q + s + 1) - d * (s + 1)) / D0
    let t1 := v - d + d * (u + 1) * (w + 1) / D1
    (t1 - t0) * D0 * D1 =
      d * q * (d * s * u + s * u + s * v + s + u * w + u) := by
  dsimp
  field_simp [hD0.ne', hD1.ne']
  subst q
  ring

/-- The original Plücker closing-cell identity, stated independently of a
particular recurrence encoding. -/
lemma hullSevenClosing_plucker_identity
    {A D q c l m a0 a5 L R G : ℝ}
    (hLR : L * R = A * D - c * q)
    (hG : G * (L * R) =
      c * l * m + A * a5 * l + D * a0 * m + a0 * a5 * q) :
    G * (A * D - c * q) =
      c * l * m + A * a5 * l + D * a0 * m + a0 * a5 * q := by
  rw [← hLR]
  exact hG

end Heilbronn8.TriHull
