import Heilbronn8.TriHull.Core

/-!
# Geometry packets for hull-five `1 + 1 + 1`

The pentagon is written in cyclic order as `A-B-X-C-D`.  The seven hull
areas used by the compact scalar endpoint are

`T=ABC`, `U=ABX`, `V=AXC`, `E=BXC`, `W=ABD`, `Z=BCD`, `F=CDA`.

This module contains only universal determinant identities and small
nonnegative-product certificates.  It deliberately does not choose a
maximal hull triangle and does not depend on retained keys.
-/

namespace Heilbronn8.TriHull

/-! ## Universal pentagon identities -/

lemma hullFive111_right_sum (A B X C : ℝ × ℝ) :
    sig A B X + sig A X C = sig A B C + sig B X C := by
  simp only [sig]
  ring

lemma hullFive111_left_sum (A B C D : ℝ × ℝ) :
    sig A B D + sig B C D = sig A B C + sig C D A := by
  simp only [sig]
  ring

/-- The cross-row identity used by an `U` ear point. -/
lemma hullFive111_ear_u_identity (A B X C P : ℝ × ℝ) :
    sig A B X * sig P C B =
      sig P A B * sig B X C - sig P B X * sig A B C := by
  simp only [sig]
  ring

/-- The cross-row identity used by a `V` ear point. -/
lemma hullFive111_ear_v_identity (A B X C P : ℝ × ℝ) :
    sig A X C * sig P C B =
      sig P C A * sig B X C - sig P X C * sig A B C := by
  simp only [sig]
  ring

/-- First determinant identity for a central point. -/
lemma hullFive111_central_u_identity (A B X C P : ℝ × ℝ) :
    sig A B C * sig P X A =
      sig P C A * sig A B X - sig P A B * sig A X C := by
  simp only [sig]
  ring

/-- Second determinant identity for a central point. -/
lemma hullFive111_central_w_identity (A B C D P : ℝ × ℝ) :
    sig A B C * sig P B D =
      sig P B C * sig A B D - sig P A B * sig B C D := by
  simp only [sig]
  ring

/-! ## The generic ear inequality -/

/-- Homogeneous ear inequality at minimum-area scale `m`.

The variables `a,b,c` are the three fan pieces of `U`; `q` is the cross
triangle in the adjacent ear.  Only `a,b,q` need explicit lower floors. -/
lemma hullFive111_ear_scaled
    {m T U E a b c q : ℝ}
    (hm : 0 ≤ m) (hT : 0 ≤ T) (hU : 0 ≤ U) (hE : 0 ≤ E)
    (ha : m ≤ a) (hb : m ≤ b) (hq : m ≤ q)
    (hfan : a + b + c = U)
    (hcross : U * q = c * E - a * T) :
    m * T + 2 * m ^ 2 ≤ (U - 2 * m) * (E - m) := by
  have hc : c ≤ U - 2 * m := by linarith
  have hUq : m * U ≤ U * q := by
    have hmul : 0 ≤ U * (q - m) :=
      mul_nonneg hU (sub_nonneg.mpr hq)
    nlinarith
  have haT : m * T ≤ a * T := by
    exact mul_le_mul_of_nonneg_right ha hT
  have hcE : c * E ≤ (U - 2 * m) * E := by
    exact mul_le_mul_of_nonneg_right hc hE
  nlinarith [hcross]

/-- Unit-normalized form of `hullFive111_ear_scaled`. -/
lemma hullFive111_ear
    {T U E a b c q : ℝ}
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hE : 0 ≤ E)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hq : 1 ≤ q)
    (hfan : a + b + c = U)
    (hcross : U * q = c * E - a * T) :
    T + 2 ≤ (U - 2) * (E - 1) := by
  have h := hullFive111_ear_scaled
    (m := (1 : ℝ)) (T := T) (U := U) (E := E)
    (a := a) (b := b) (c := c) (q := q)
    (by norm_num) hT hU hE ha hb hq hfan hcross
  norm_num at h ⊢
  simpa using h

/-! ## Central determinant certificates -/

/-- Homogeneous `UZ` central certificate.

For the central point, `x,y,z` are its fan pieces in `ABC`, while `a` and
`b` are the selected cross triangles in `AXC` and `ABD`. -/
lemma hullFive111_uz_central_scaled
    {m T U V W Z x y z a b : ℝ}
    (hm : 0 ≤ m) (hT : 0 ≤ T) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hW : 0 ≤ W) (hZ : 0 ≤ Z)
    (hfan : x + y + z = T)
    (hy : m ≤ y) (ha : m ≤ a) (hb : m ≤ b)
    (haxp : T * a = V * z - U * y)
    (hpbd : T * b = W * x - Z * z) :
    m * (V * W + W * (T + U) + T * V + Z * (T + U)) ≤
      T * V * W := by
  have hga : 0 ≤ V * z - U * y - m * T := by
    have hmul : 0 ≤ T * (a - m) :=
      mul_nonneg hT (sub_nonneg.mpr ha)
    nlinarith [haxp]
  have hgb : 0 ≤ W * x - Z * z - m * T := by
    have hmul : 0 ≤ T * (b - m) :=
      mul_nonneg hT (sub_nonneg.mpr hb)
    nlinarith [hpbd]
  have hWZ : 0 ≤ W + Z := add_nonneg hW hZ
  have hcoef : 0 ≤ V * W + U * (W + Z) :=
    add_nonneg (mul_nonneg hV hW) (mul_nonneg hU hWZ)
  have hcertificate : 0 ≤
      V * (W * x - Z * z - m * T) +
        (W + Z) * (V * z - U * y - m * T) +
        (V * W + U * (W + Z)) * (y - m) := by
    exact add_nonneg
      (add_nonneg (mul_nonneg hV hgb) (mul_nonneg hWZ hga))
      (mul_nonneg hcoef (sub_nonneg.mpr hy))
  have hid :
      T * V * W -
          m * (V * W + W * (T + U) + T * V + Z * (T + U)) =
        V * (W * x - Z * z - m * T) +
          (W + Z) * (V * z - U * y - m * T) +
          (V * W + U * (W + Z)) * (y - m) := by
    rw [← hfan]
    ring
  nlinarith [hid]

/-- Unit-normalized `UZ` central inequality. -/
lemma hullFive111_uz_central
    {T U V W Z x y z a b : ℝ}
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hW : 0 ≤ W) (hZ : 0 ≤ Z)
    (hfan : x + y + z = T)
    (hy : 1 ≤ y) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (haxp : T * a = V * z - U * y)
    (hpbd : T * b = W * x - Z * z) :
    V * W + W * (T + U) + T * V + Z * (T + U) ≤
      T * V * W := by
  simpa using hullFive111_uz_central_scaled
    (m := (1 : ℝ)) (T := T) (U := U) (V := V) (W := W) (Z := Z)
    (x := x) (y := y) (z := z) (a := a) (b := b)
    (by norm_num) hT hU hV hW hZ hfan hy ha hb haxp hpbd

/-- Homogeneous `VZ` central certificate. -/
lemma hullFive111_vz_central_scaled
    {m T U V W Z F x y z q r : ℝ}
    (hm : 0 ≤ m) (hT : 0 ≤ T) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hW : 0 ≤ W) (hZ : 0 ≤ Z)
    (hfan : x + y + z = T) (hleft : W + Z = T + F)
    (hq : m ≤ q) (hr : m ≤ r) (hz : m ≤ z)
    (hpxa : T * q = y * U - z * V)
    (hpbd : T * r = x * W - z * Z) :
    m * (W * (T + V) + U * (2 * T + F)) ≤ T * U * W := by
  have hgq : 0 ≤ y * U - z * V - m * T := by
    have hmul : 0 ≤ T * (q - m) :=
      mul_nonneg hT (sub_nonneg.mpr hq)
    nlinarith [hpxa]
  have hgr : 0 ≤ x * W - z * Z - m * T := by
    have hmul : 0 ≤ T * (r - m) :=
      mul_nonneg hT (sub_nonneg.mpr hr)
    nlinarith [hpbd]
  have hcoef : 0 ≤ V * W + U * Z + U * W := by
    positivity
  have hcertificate : 0 ≤
      W * (y * U - z * V - m * T) +
        U * (x * W - z * Z - m * T) +
        (z - m) * (V * W + U * Z + U * W) := by
    exact add_nonneg
      (add_nonneg (mul_nonneg hW hgq) (mul_nonneg hU hgr))
      (mul_nonneg (sub_nonneg.mpr hz) hcoef)
  have hF : F = W + Z - T := by linarith [hleft]
  have hid :
      T * U * W - m * (W * (T + V) + U * (2 * T + F)) =
        W * (y * U - z * V - m * T) +
          U * (x * W - z * Z - m * T) +
          (z - m) * (V * W + U * Z + U * W) := by
    rw [hF, ← hfan]
    ring
  nlinarith [hid]

/-- Unit-normalized `VZ` central inequality. -/
lemma hullFive111_vz_central
    {T U V W Z F x y z q r : ℝ}
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hW : 0 ≤ W) (hZ : 0 ≤ Z)
    (hfan : x + y + z = T) (hleft : W + Z = T + F)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hz : 1 ≤ z)
    (hpxa : T * q = y * U - z * V)
    (hpbd : T * r = x * W - z * Z) :
    W * (T + V) + U * (2 * T + F) ≤ T * U * W := by
  simpa using hullFive111_vz_central_scaled
    (m := (1 : ℝ)) (T := T) (U := U) (V := V) (W := W) (Z := Z)
    (F := F) (x := x) (y := y) (z := z) (q := q) (r := r)
    (by norm_num) hT hU hV hW hZ hfan hleft hq hr hz hpxa hpbd

/-! ## The geometric reason ear ownership is separated -/

/-- Two nonadjacent open ears of a strict convex pentagon cannot contain the
same point.  The chord `L-R` strictly separates `LMR` from `RST`.

The three orientation hypotheses are precisely the cyclic-order rows needed
for that chord separation. -/
lemma hullFive111_nonadjacent_ears_disjoint
    {L M R S T P : ℝ × ℝ}
    (hLMR : 0 < sig L M R)
    (hLRS : 0 < sig L R S) (hLRT : 0 < sig L R T)
    (hleft : InTriStrict P L M R)
    (hright : InTriStrict P R S T) : False := by
  obtain ⟨_, hPRL, _⟩ := inTriStrict_fan_pos hLMR hleft
  have hnegative : sig L R P < 0 := by
    have hid : sig L R P = -sig P R L := by
      simp only [sig]
      ring
    rw [hid]
    linarith
  obtain ⟨a, b, c, ha, hb, hc, habc, hP⟩ := hright
  have hpositive : 0 < sig L R P := by
    rw [hP, sig_affine_thd L R R S T a b c habc, sig_eq23]
    have hbS : 0 < b * sig L R S := mul_pos hb hLRS
    have hcT : 0 < c * sig L R T := mul_pos hc hLRT
    linarith
  linarith

end Heilbronn8.TriHull
