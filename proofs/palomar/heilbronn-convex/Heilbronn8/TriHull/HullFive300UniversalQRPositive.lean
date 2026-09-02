import Heilbronn8.TriHull.HullFive300UniversalQRNegative

set_option maxHeartbeats 0

/-!
# The double-positive `QR` subcell of the remaining `--++` orbit

This source-only scalar lemma handles the subcell in which `XQR` and `DQR`
are both positive.  The proof first eliminates the two auxiliary slope
parameters by exact Pluecker identities.  Two elementary square-root bounds
then reduce the result to one rational polynomial which is positive on the
half-line `t >= 1`.
-/

namespace Heilbronn8.TriHull

/-- The two-variable AM-GM inequality in the exact square-root form used by
the positive `QR` cell. -/
private lemma two_sqrt_product_le_add {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    2 * Real.sqrt u * Real.sqrt v ≤ u + v := by
  have husq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu
  have hvsq : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv
  have hleft0 : 0 ≤ 2 * Real.sqrt u * Real.sqrt v := by positivity
  have hright0 : 0 ≤ u + v := add_nonneg hu hv
  apply (sq_le_sq₀ hleft0 hright0).1
  calc
    (2 * Real.sqrt u * Real.sqrt v) ^ 2 = 4 * u * v := by
      rw [mul_pow, mul_pow, husq, hvsq]
      ring
    _ ≤ (u + v) ^ 2 := by nlinarith [sq_nonneg (u - v)]

/-- Equal products of nonnegative pairs have equal products of square roots.
This avoids relying on a particular orientation of `Real.sqrt_mul`. -/
private lemma sqrt_product_eq_of_product_eq
    {u v p q : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hproduct : u * v = p * q) :
    Real.sqrt u * Real.sqrt v = Real.sqrt p * Real.sqrt q := by
  have husq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu
  have hvsq : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv
  have hpsq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp
  have hqsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
  have hleft0 : 0 ≤ Real.sqrt u * Real.sqrt v := by positivity
  have hright0 : 0 ≤ Real.sqrt p * Real.sqrt q := by positivity
  have hsquares :
      (Real.sqrt u * Real.sqrt v) ^ 2 =
        (Real.sqrt p * Real.sqrt q) ^ 2 := by
    rw [mul_pow, mul_pow, husq, hvsq, hpsq, hqsq, hproduct]
  apply le_antisymm
  · exact (sq_le_sq₀ hleft0 hright0).1 hsquares.le
  · exact (sq_le_sq₀ hright0 hleft0).1 hsquares.ge

/-- If `b,d >= 2`, `Delta >= 2`, and `b+d=N+Delta`, then the two square
roots dominate the endpoint pair `sqrt 2 + sqrt N`. -/
private lemma sqrt_two_add_sqrt_le_pair
    {b d N Delta : ℝ}
    (hb : 2 ≤ b) (hd : 2 ≤ d)
    (hN : 0 ≤ N) (hDelta : 2 ≤ Delta)
    (hfan : b + d = N + Delta) :
    Real.sqrt 2 + Real.sqrt N ≤ Real.sqrt b + Real.sqrt d := by
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  have hd0 : 0 ≤ d := le_trans (by norm_num) hd
  have htwo0 : (0 : ℝ) ≤ 2 := by norm_num
  have hprodBase :=
    mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hd)
  have hbd : 2 * N ≤ b * d := by
    nlinarith
  have hs2sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt htwo0
  have hsNsq : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN
  have hsbsq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb0
  have hsdsq : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd0
  have hrootProduct :
      Real.sqrt 2 * Real.sqrt N ≤ Real.sqrt b * Real.sqrt d := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    calc
      (Real.sqrt 2 * Real.sqrt N) ^ 2 = 2 * N := by
        rw [mul_pow, hs2sq, hsNsq]
      _ ≤ b * d := hbd
      _ = (Real.sqrt b * Real.sqrt d) ^ 2 := by
        rw [mul_pow, hsbsq, hsdsq]
  apply (sq_le_sq₀ (by positivity) (by positivity)).1
  calc
    (Real.sqrt 2 + Real.sqrt N) ^ 2 =
        2 + N + 2 * (Real.sqrt 2 * Real.sqrt N) := by
      rw [add_sq, hs2sq, hsNsq]
      ring
    _ ≤ b + d + 2 * (Real.sqrt b * Real.sqrt d) := by
      nlinarith
    _ = (Real.sqrt b + Real.sqrt d) ^ 2 := by
      rw [add_sq, hsbsq, hsdsq]
      ring

/-- The exact one-variable inequality left after the two `QR` AM-GM steps.

The proof uses `t = sqrt (N/2)`.  Its only irrational estimate is isolated as
`sqrt (t^2+1) >= 707(t+1)/1000`; after clearing the positive denominator,
the remaining quartic is a sum of nonnegative terms. -/
private lemma qr_positive_one_variable {N : ℝ} (hN : 2 ≤ N) :
    25 ≤ N + 8 + 8 / N +
      2 * Real.sqrt (2 + 4 / N) * (Real.sqrt 2 + Real.sqrt N) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  let t : ℝ := Real.sqrt (N / 2)
  let s : ℝ := Real.sqrt (t ^ 2 + 1)
  have hhalf0 : 0 ≤ N / 2 := by positivity
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact Real.sqrt_nonneg _
  have htsq : t ^ 2 = N / 2 := by
    dsimp [t]
    exact Real.sq_sqrt hhalf0
  have ht : 1 ≤ t := by
    by_contra hnot
    have htlt : t < 1 := lt_of_not_ge hnot
    have hprod : 0 < (1 - t) * (1 + t) :=
      mul_pos (sub_pos.mpr htlt) (by linarith)
    nlinarith
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hssq : s ^ 2 = t ^ 2 + 1 := by
    dsimp [s]
    exact Real.sq_sqrt (by positivity)

  have hsLower : (707 / 1000 : ℝ) * (t + 1) ≤ s := by
    have hleft0 : 0 ≤ (707 / 1000 : ℝ) * (t + 1) := by positivity
    apply (sq_le_sq₀ hleft0 hs0).1
    rw [hssq]
    nlinarith [sq_nonneg (t - 1)]

  let u : ℝ := t - 1
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hquadratic : 0 < 2285 * u ^ 2 - 844 * u + 78 := by
    nlinarith [sq_nonneg (2285 * u - 422)]
  have hu3 : 0 ≤ u ^ 3 := pow_nonneg hu 3
  have hu4 : 0 ≤ u ^ 4 := pow_nonneg hu 4
  have hpolyIdentity :
      500 * t ^ 4 + 707 * t ^ 3 - 2836 * t ^ 2 + 707 * t + 1000 =
        500 * u ^ 4 + 2707 * u ^ 3 +
          (2285 * u ^ 2 - 844 * u + 78) := by
    dsimp [u]
    ring
  have hpoly :
      0 < 500 * t ^ 4 + 707 * t ^ 3 - 2836 * t ^ 2 +
        707 * t + 1000 := by
    rw [hpolyIdentity]
    nlinarith

  have hgapIdentity :
      (250 * t ^ 2) *
          (2 * t ^ 2 + 4 / t ^ 2 +
            (707 / 250 : ℝ) * (t + 2 + 1 / t) - 17) =
        500 * t ^ 4 + 707 * t ^ 3 - 2836 * t ^ 2 +
          707 * t + 1000 := by
    field_simp [ne_of_gt htpos]
    ring
  have hgapProduct :
      0 < (250 * t ^ 2) *
        (2 * t ^ 2 + 4 / t ^ 2 +
          (707 / 250 : ℝ) * (t + 2 + 1 / t) - 17) := by
    rw [hgapIdentity]
    exact hpoly
  have hfactorPos : 0 < 250 * t ^ 2 := by positivity
  have hgap :
      0 < 2 * t ^ 2 + 4 / t ^ 2 +
        (707 / 250 : ℝ) * (t + 2 + 1 / t) - 17 := by
    rcases (mul_pos_iff.mp hgapProduct) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge hfactorPos.le) h.1)

  have hcrossFactor : 0 ≤ 4 * (t + 1) / t := by positivity
  have hcross := mul_le_mul_of_nonneg_left hsLower hcrossFactor
  have hcrossIdentity :
      (4 * (t + 1) / t) * ((707 / 1000 : ℝ) * (t + 1)) =
        (707 / 250 : ℝ) * (t + 2 + 1 / t) := by
    field_simp [ne_of_gt htpos]
    ring
  rw [hcrossIdentity] at hcross
  have htBound :
      25 ≤ 8 + 2 * t ^ 2 + 4 / t ^ 2 +
        4 * (t + 1) / t * s := by
    nlinarith

  have hs2sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsNsq : (Real.sqrt N) ^ 2 = N :=
    Real.sq_sqrt (le_trans (by norm_num) hN)
  have hsN0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hsNIdentity : Real.sqrt N = Real.sqrt 2 * t := by
    have hright0 : 0 ≤ Real.sqrt 2 * t := by positivity
    have hsquares :
        (Real.sqrt N) ^ 2 = (Real.sqrt 2 * t) ^ 2 := by
      rw [hsNsq, mul_pow, hs2sq, htsq]
      ring
    apply le_antisymm
    · exact (sq_le_sq₀ hsN0 hright0).1 hsquares.le
    · exact (sq_le_sq₀ hright0 hsN0).1 hsquares.ge

  have hq0 : 0 ≤ 2 + 4 / N := by positivity
  have hqsq : (Real.sqrt (2 + 4 / N)) ^ 2 = 2 + 4 / N :=
    Real.sq_sqrt hq0
  have hqIdentity :
      Real.sqrt (2 + 4 / N) = Real.sqrt 2 * s / t := by
    have hleft0 : 0 ≤ Real.sqrt (2 + 4 / N) := Real.sqrt_nonneg _
    have hright0 : 0 ≤ Real.sqrt 2 * s / t := by positivity
    have hsquares :
        (Real.sqrt (2 + 4 / N)) ^ 2 =
          (Real.sqrt 2 * s / t) ^ 2 := by
      rw [hqsq, div_pow, mul_pow, hs2sq, hssq]
      have hNIdentity : N = 2 * t ^ 2 := by nlinarith [htsq]
      rw [hNIdentity]
      field_simp [ne_of_gt htpos]
      ring
    apply le_antisymm
    · exact (sq_le_sq₀ hleft0 hright0).1 hsquares.le
    · exact (sq_le_sq₀ hright0 hleft0).1 hsquares.ge

  have hNIdentity : N = 2 * t ^ 2 := by nlinarith [htsq]
  have hcrossTranslate :
      2 * (Real.sqrt 2 * s / t) *
          (Real.sqrt 2 + Real.sqrt 2 * t) =
        4 * (t + 1) / t * s := by
    field_simp [ne_of_gt htpos]
    linear_combination 2 * s * (t + 1) * hs2sq
  calc
    25 ≤ 8 + 2 * t ^ 2 + 4 / t ^ 2 +
        4 * (t + 1) / t * s := htBound
    _ = N + 8 + 8 / N +
        2 * Real.sqrt (2 + 4 / N) *
          (Real.sqrt 2 + Real.sqrt N) := by
      rw [hsNIdentity, hqIdentity, hNIdentity]
      rw [hcrossTranslate]
      field_simp [ne_of_gt htpos]
      ring

/-- The double-positive auxiliary `QR` cell in the `delta,tau < 0` outer
orbit.  Here `xi=XQR`, `eta=DQR`, `Delta=PQR`, `N=-CQR`, while `aqr=AQR`
and `bqr=BQR`.  The four raw slope equations are retained in the interface;
the two shorter identities used by the estimate are derived inside the
proof by exact polynomial elimination. -/
theorem hullFive300_ee_qr_positive_scalar
    {a b c d e f g x y z w Delta N xi eta sigma rho aqr bqr H : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hg : 2 ≤ g) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hz : 2 ≤ z) (hw : 2 ≤ w)
    (hDelta : 2 ≤ Delta) (hN : 2 ≤ N)
    (hxi : 2 ≤ xi) (heta : 2 ≤ eta)
    (haqr : 2 ≤ aqr) (hbqr : 2 ≤ bqr)
    (hfan : b + d = N + Delta)
    (hcentralQ : a * N = b * bqr + c * Delta)
    (hcentralR : e * N = d * aqr + f * Delta)
    (hXQRN : N * sigma = b * xi + y * Delta)
    (hXQRB : bqr * sigma = a * xi + x * Delta)
    (hDQRN : N * rho = d * eta + z * Delta)
    (hDQRA : aqr * rho = e * eta + w * Delta)
    (hH : H = a + b + d + e + x + y + z + w + g) :
    25 ≤ H := by
  have hDeltaPos : 0 < Delta := lt_of_lt_of_le (by norm_num) hDelta
  have hNPos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have haqrPos : 0 < aqr := lt_of_lt_of_le (by norm_num) haqr
  have hbqrPos : 0 < bqr := lt_of_lt_of_le (by norm_num) hbqr
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  have hd0 : 0 ≤ d := le_trans (by norm_num) hd
  have hN0 : 0 ≤ N := hNPos.le

  have hXScaled :
      Delta * (N * x + c * xi - bqr * y) = 0 := by
    linear_combination
      bqr * hXQRN - N * hXQRB - xi * hcentralQ
  have hXSlope : bqr * y = N * x + c * xi := by
    rcases mul_eq_zero.mp hXScaled with hzero | hrow
    · exact False.elim (hDeltaPos.ne' hzero)
    · linarith
  have hDScaled :
      Delta * (N * w + f * eta - aqr * z) = 0 := by
    linear_combination
      aqr * hDQRN - N * hDQRA - eta * hcentralR
  have hDSlope : aqr * z = N * w + f * eta := by
    rcases mul_eq_zero.mp hDScaled with hzero | hrow
    · exact False.elim (hDeltaPos.ne' hzero)
    · linarith

  let q : ℝ := 2 + 4 / N
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  let uq : ℝ := b * bqr / N
  let vq : ℝ := (2 * N + 4) / bqr
  let ur : ℝ := d * aqr / N
  let vr : ℝ := (2 * N + 4) / aqr
  have huq0 : 0 ≤ uq := by dsimp [uq]; positivity
  have hvq0 : 0 ≤ vq := by dsimp [vq]; positivity
  have hur0 : 0 ≤ ur := by dsimp [ur]; positivity
  have hvr0 : 0 ≤ vr := by dsimp [vr]; positivity

  have hcentralQLower : uq + 2 * Delta / N ≤ a := by
    have hrewrite :
        uq + 2 * Delta / N = (b * bqr + 2 * Delta) / N := by
      dsimp [uq]
      ring
    rw [hrewrite, div_le_iff₀ hNPos]
    have hcDelta := mul_le_mul_of_nonneg_right hc hDeltaPos.le
    nlinarith [hcentralQ]
  have hXSlopeLower : vq ≤ y := by
    dsimp [vq]
    rw [div_le_iff₀ hbqrPos]
    have hNx := mul_le_mul_of_nonneg_left hx hN0
    have hcxi : 4 ≤ c * xi := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hxi)]
    nlinarith [hXSlope]
  have hcentralRLower : ur + 2 * Delta / N ≤ e := by
    have hrewrite :
        ur + 2 * Delta / N = (d * aqr + 2 * Delta) / N := by
      dsimp [ur]
      ring
    rw [hrewrite, div_le_iff₀ hNPos]
    have hfDelta := mul_le_mul_of_nonneg_right hf hDeltaPos.le
    nlinarith [hcentralR]
  have hDSlopeLower : vr ≤ z := by
    dsimp [vr]
    rw [div_le_iff₀ haqrPos]
    have hNw := mul_le_mul_of_nonneg_left hw hN0
    have hfeta : 4 ≤ f * eta := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr heta)]
    nlinarith [hDSlope]

  have huqvq : uq * vq = b * q := by
    dsimp [uq, vq, q]
    field_simp [ne_of_gt hNPos, ne_of_gt hbqrPos]
  have hurvr : ur * vr = d * q := by
    dsimp [ur, vr, q]
    field_simp [ne_of_gt hNPos, ne_of_gt haqrPos]
  have hrootQ :
      Real.sqrt uq * Real.sqrt vq = Real.sqrt b * Real.sqrt q :=
    sqrt_product_eq_of_product_eq huq0 hvq0 hb0 hq0 huqvq
  have hrootR :
      Real.sqrt ur * Real.sqrt vr = Real.sqrt d * Real.sqrt q :=
    sqrt_product_eq_of_product_eq hur0 hvr0 hd0 hq0 hurvr
  have hAMQ : 2 * Real.sqrt b * Real.sqrt q ≤ uq + vq := by
    calc
      2 * Real.sqrt b * Real.sqrt q =
          2 * (Real.sqrt b * Real.sqrt q) := by ring
      _ = 2 * (Real.sqrt uq * Real.sqrt vq) := by rw [hrootQ]
      _ = 2 * Real.sqrt uq * Real.sqrt vq := by ring
      _ ≤ uq + vq := two_sqrt_product_le_add huq0 hvq0
  have hAMR : 2 * Real.sqrt d * Real.sqrt q ≤ ur + vr := by
    calc
      2 * Real.sqrt d * Real.sqrt q =
          2 * (Real.sqrt d * Real.sqrt q) := by ring
      _ = 2 * (Real.sqrt ur * Real.sqrt vr) := by rw [hrootR]
      _ = 2 * Real.sqrt ur * Real.sqrt vr := by ring
      _ ≤ ur + vr := two_sqrt_product_le_add hur0 hvr0
  have hAMsum :
      2 * Real.sqrt q * (Real.sqrt b + Real.sqrt d) ≤
        uq + vq + ur + vr := by
    calc
      2 * Real.sqrt q * (Real.sqrt b + Real.sqrt d) =
          (2 * Real.sqrt b * Real.sqrt q) +
            (2 * Real.sqrt d * Real.sqrt q) := by ring
      _ ≤ (uq + vq) + (ur + vr) := add_le_add hAMQ hAMR
      _ = uq + vq + ur + vr := by ring
  have hfour :
      4 * Delta / N = 2 * Delta / N + 2 * Delta / N := by ring
  have hpairs :
      4 * Delta / N +
          2 * Real.sqrt q * (Real.sqrt b + Real.sqrt d) ≤
        a + e + y + z := by
    rw [hfour]
    nlinarith [hcentralQLower, hXSlopeLower,
      hcentralRLower, hDSlopeLower, hAMsum]

  have hrootSum :
      Real.sqrt 2 + Real.sqrt N ≤ Real.sqrt b + Real.sqrt d :=
    sqrt_two_add_sqrt_le_pair hb hd hN0 hDelta hfan
  have hrootScaled := mul_le_mul_of_nonneg_left hrootSum
    (show 0 ≤ 2 * Real.sqrt q by positivity)
  have hcore :
      4 * Delta / N +
          2 * Real.sqrt q * (Real.sqrt 2 + Real.sqrt N) ≤
        a + e + y + z := by
    nlinarith [hpairs, hrootScaled]
  have hDeltaRatio : 8 / N ≤ 4 * Delta / N := by
    apply (div_le_div_iff_of_pos_right hNPos).2
    nlinarith
  have hLower :
      N + 8 + 8 / N +
          2 * Real.sqrt q * (Real.sqrt 2 + Real.sqrt N) ≤ H := by
    nlinarith [hH, hfan, hcore, hDeltaRatio]
  have hfinal := qr_positive_one_variable hN
  dsimp [q] at hLower
  exact hfinal.trans hLower

end Heilbronn8.TriHull
