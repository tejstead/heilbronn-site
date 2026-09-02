import Mathlib

/-!
# The scalar core of the exceptional CAB type-717 cell

This file contains no search output.  It isolates the short area argument
used after the CAB fan-sector census leaves its unique exceptional sign cell.

The names in the homogeneous theorem have the following geometric meaning in
the oriented central triangle `BXC`:

* `p0 = [XCP]`, `p1 = -[BCP]`, `u = [BXP]`;
* `r0 = [XCR]`, `s = -[BCR]`, `r2 = [BXR]`;
* `j = [BPR]`, `g = -[CPR]`, `h = -[XPR]`;
* `b = [XDP]`, `f = [XDR]`;
* `K = [DBX]`, `L = [XCD]`, and `Z = [BCD]`.

Thus `E = [BXC]`.  The type-717 signs make every displayed quantity
positive.  The hard branch is `E <= 21m/2`; in that branch the central
identities force `Z >= 3m`.  Together with `[BXC] >= 17m/2` and the hull ear
`[ABD] >= m`, this is exactly the required hull bound.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.TriHull

/-- Dimensionless core of the type-717 estimate.

After scaling the minimum triangle area to one, the three sector identities
and the upper bound on the central triangle already leave a surplus of
`5 / 2`.  The proof is a division-free polynomial certificate. -/
theorem hullFive300_cab717_normalized_core
    {u j g h s r0 r2 E : ℝ}
    (hu : 1 ≤ u) (hj : 1 ≤ j) (hg : 1 ≤ g)
    (hh : 1 ≤ h) (hs : 1 ≤ s)
    (hr2 : r2 = u + j + h)
    (hpair : j * r0 = g * r2 + h * s)
    (hE : E = r0 + s + r2)
    (hcap : 2 * E ≤ 21) :
    (5 / 2 : ℝ) ≤ r0 + r2 + j + g - h * (s + 3) := by
  let lo : ℝ := 1 + j + h
  let C : ℝ :=
    (21 / 2 : ℝ) * j - (lo + h * s + j * s + j * lo)
  let D : ℝ := r0 + r2 + j + g - h * (s + 3)
  let Q : ℝ :=
    (1 + j) * lo + j ^ 2 + j + h * s - j * h * (s + 3) -
      (5 / 2 : ℝ) * j
  let A : ℝ := j + s + 1
  let coeff : ℝ := j * (s + 2) - s - 1
  let P : ℝ :=
    10 * (j - 2) ^ 2 +
      (s - 1) * (2 * j ^ 2 - 7 * j + 14) +
      (s - 1) ^ 2 * (2 * j - 2)

  have hj0 : 0 ≤ j := by linarith
  have hjpos : 0 < j := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hlo_pos : 0 < lo := by
    dsimp only [lo]
    linarith
  have hlo_r2 : lo ≤ r2 := by
    dsimp only [lo]
    nlinarith [hr2]
  have hr2_nonneg : 0 ≤ r2 := le_trans hlo_pos.le hlo_r2
  have hgr2 : r2 ≤ g * r2 := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr hg) hr2_nonneg
    nlinarith
  have hjlo : j * lo ≤ j * r2 :=
    mul_le_mul_of_nonneg_left hlo_r2 hj0
  have hjr0 : lo + h * s ≤ j * r0 := by
    rw [hpair]
    nlinarith
  have hjE : j * E = j * r0 + j * s + j * r2 := by
    rw [hE]
    ring
  have hcap' : E ≤ (21 / 2 : ℝ) := by linarith
  have hjcap : j * E ≤ j * (21 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hcap' hj0
  have hC : 0 ≤ C := by
    dsimp only [C]
    nlinarith [hjlo, hjr0, hjE, hjcap]

  have hu_term : 0 ≤ (j + 1) * (u - 1) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hu)
  have hg_term : 0 ≤ (g - 1) * (j + r2) :=
    mul_nonneg (sub_nonneg.mpr hg) (by nlinarith [hj0, hr2_nonneg])
  have hDQidentity :
      j * (D - (5 / 2 : ℝ)) - Q =
        (j + 1) * (u - 1) + (g - 1) * (j + r2) := by
    calc
      j * (D - (5 / 2 : ℝ)) - Q =
          (j + 1) * (u - 1) + (g - 1) * (j + r2) +
            (j * r0 - (g * r2 + h * s)) +
            (j + 1) * (r2 - (u + j + h)) := by
              dsimp only [D, Q, lo]
              ring
      _ = (j + 1) * (u - 1) + (g - 1) * (j + r2) := by
        rw [hpair, hr2]
        ring
  have hQupper : Q ≤ j * (D - (5 / 2 : ℝ)) := by
    nlinarith [hu_term, hg_term, hDQidentity]

  have hquad : 0 ≤ 2 * j ^ 2 - 7 * j + 14 := by
    nlinarith [sq_nonneg (4 * j - 7)]
  have hP : 0 ≤ P := by
    have h0 : 0 ≤ 10 * (j - 2) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg (j - 2))
    have h1 : 0 ≤ (s - 1) * (2 * j ^ 2 - 7 * j + 14) :=
      mul_nonneg (sub_nonneg.mpr hs) hquad
    have h2 : 0 ≤ (s - 1) ^ 2 * (2 * j - 2) :=
      mul_nonneg (sq_nonneg (s - 1)) (by linarith)
    dsimp only [P]
    nlinarith
  have hcoeff : 0 ≤ coeff := by
    have hprod : 0 ≤ (j - 1) * (s + 2) :=
      mul_nonneg (sub_nonneg.mpr hj) (by linarith)
    dsimp only [coeff]
    nlinarith
  have hApos : 0 < A := by
    dsimp only [A]
    linarith
  have hcertificate :
      2 * A * Q = j * P + 2 * coeff * C := by
    dsimp only [A, Q, P, coeff, C, lo]
    ring
  have hright_nonneg : 0 ≤ j * P + 2 * coeff * C := by
    have hjP : 0 ≤ j * P := mul_nonneg hj0 hP
    have hcC : 0 ≤ 2 * coeff * C :=
      mul_nonneg (mul_nonneg (by norm_num) hcoeff) hC
    nlinarith
  have htwoAQ : 0 ≤ 2 * A * Q := by
    rw [hcertificate]
    exact hright_nonneg
  have hQ : 0 ≤ Q := by
    by_contra hnot
    have hQneg : Q < 0 := lt_of_not_ge hnot
    have htwoA : 0 < 2 * A := mul_pos (by norm_num) hApos
    have : 2 * A * Q < 0 := mul_neg_of_pos_of_neg htwoA hQneg
    linarith
  have hD : (5 / 2 : ℝ) ≤ D := by
    by_contra hnot
    have hneg : D - (5 / 2 : ℝ) < 0 := by linarith
    have hjneg : j * (D - (5 / 2 : ℝ)) < 0 :=
      mul_neg_of_pos_of_neg hjpos hneg
    linarith [hQupper, hQ]
  exact hD

/-- Homogeneous form of `hullFive300_cab717_normalized_core`.

Every variable is a doubled area and `m` is the minimum doubled triangle
area.  The conclusion is kept with its positive `5m²/2` surplus because this
form composes directly with the outer `D`-row estimate below. -/
theorem hullFive300_cab717_homogeneous_core
    {m u j g h s r0 r2 E : ℝ}
    (hm : 0 < m)
    (hu : m ≤ u) (hj : m ≤ j) (hg : m ≤ g)
    (hh : m ≤ h) (hs : m ≤ s)
    (hr2 : r2 = u + j + h)
    (hpair : j * r0 = g * r2 + h * s)
    (hE : E = r0 + s + r2)
    (hcap : 2 * E ≤ 21 * m) :
    (5 / 2 : ℝ) * m ^ 2 ≤
      m * (r0 + r2 + j + g) - h * (s + 3 * m) := by
  have hmne : m ≠ 0 := ne_of_gt hm
  have hu' : 1 ≤ u / m := (le_div_iff₀ hm).2 (by simpa using hu)
  have hj' : 1 ≤ j / m := (le_div_iff₀ hm).2 (by simpa using hj)
  have hg' : 1 ≤ g / m := (le_div_iff₀ hm).2 (by simpa using hg)
  have hh' : 1 ≤ h / m := (le_div_iff₀ hm).2 (by simpa using hh)
  have hs' : 1 ≤ s / m := (le_div_iff₀ hm).2 (by simpa using hs)
  have hr2' : r2 / m = u / m + j / m + h / m := by
    field_simp [hmne]
    nlinarith [hr2]
  have hpair' :
      (j / m) * (r0 / m) =
        (g / m) * (r2 / m) + (h / m) * (s / m) := by
    field_simp [hmne]
    nlinarith [hpair]
  have hE' : E / m = r0 / m + s / m + r2 / m := by
    field_simp [hmne]
    nlinarith [hE]
  have hcap' : 2 * (E / m) ≤ 21 := by
    calc
      2 * (E / m) = (2 * E) / m := by ring
      _ ≤ 21 := (div_le_iff₀ hm).2 (by nlinarith [hcap])
  have hcore := hullFive300_cab717_normalized_core
    hu' hj' hg' hh' hs' hr2' hpair' hE' hcap'
  have hm2pos : 0 < m ^ 2 := sq_pos_of_pos hm
  have hscaled := mul_le_mul_of_nonneg_right hcore hm2pos.le
  field_simp [hmne] at hscaled
  nlinarith

/-- The outer `D`-row elimination in the exceptional cell.

The two row Pluecker identities and the pair Pluecker identity eliminate
`K` and `L`.  The only metric inputs are the floors on `[XDR]` and `[DPR]`.
-/
theorem hullFive300_cab717_outer_z_lower
    {m E p0 p1 u r0 s r2 j g h b f K L Z : ℝ}
    (hm : 0 < m)
    (hf : m ≤ f)
    (hr0 : m ≤ r0) (hr2floor : m ≤ r2)
    (hj : m ≤ j) (hg : m ≤ g) (hs : m ≤ s)
    (hE_P : E = p0 + p1 + u)
    (hE_R : E = r0 + s + r2)
    (hp1 : p1 = s + j + g)
    (hsector : r2 = u + j + h)
    (hpair : E * h = p0 * r2 - u * r0)
    (hbrow : E * b = K * p0 - L * u)
    (hfrow : E * f = K * r0 - L * r2)
    (hDPR : f + h + m ≤ b)
    (hZ : Z = K + L - E) :
    m * (r0 + r2 + j + g) - h * s ≤ h * Z := by
  have hEpos : 0 < E := by
    rw [hE_R]
    nlinarith
  have hRnonneg : 0 ≤ r0 + r2 := by nlinarith
  have hjg_nonneg : 0 ≤ j + g := by nlinarith
  have hbmul : (f + h + m) * (r0 + r2) ≤ b * (r0 + r2) :=
    mul_le_mul_of_nonneg_right hDPR hRnonneg
  have hfsmall : m * (j + g) ≤ f * (j + g) :=
    mul_le_mul_of_nonneg_right hf hjg_nonneg
  have hK : h * K = b * r2 - f * u := by
    have hmul : E * (h * K) = E * (b * r2 - f * u) := by
      calc
        E * (h * K) = K * (E * h) := by ring
        _ = K * (p0 * r2 - u * r0) := by rw [hpair]
        _ = (K * p0 - L * u) * r2 -
            (K * r0 - L * r2) * u := by ring
        _ = E * b * r2 - E * f * u := by rw [← hbrow, ← hfrow]
        _ = E * (b * r2 - f * u) := by ring
    exact (mul_left_cancel₀ (ne_of_gt hEpos) hmul)
  have hL : h * L = b * r0 - f * p0 := by
    have hmul : E * (h * L) = E * (b * r0 - f * p0) := by
      calc
        E * (h * L) = L * (E * h) := by ring
        _ = L * (p0 * r2 - u * r0) := by rw [hpair]
        _ = (K * r0 - E * f) * p0 -
            (K * p0 - E * b) * r0 := by
              rw [hbrow, hfrow]
              ring
        _ = E * (b * r0 - f * p0) := by ring
    exact (mul_left_cancel₀ (ne_of_gt hEpos) hmul)
  have hsum :
      h * (K + L) = b * (r0 + r2) - f * (p0 + u) := by
    nlinarith [hK, hL]
  have hdiff : r0 + r2 - (p0 + u) = j + g := by
    nlinarith [hE_P, hE_R, hp1]
  have hlower :
      (h + m) * (r0 + r2) + m * (j + g) ≤ h * (K + L) := by
    calc
      (h + m) * (r0 + r2) + m * (j + g) ≤
          (h + m) * (r0 + r2) + f * (j + g) :=
        by
          calc
            (h + m) * (r0 + r2) + m * (j + g) =
                m * (j + g) + (h + m) * (r0 + r2) := by ring
            _ ≤ f * (j + g) + (h + m) * (r0 + r2) :=
              add_le_add_left hfsmall _
            _ = (h + m) * (r0 + r2) + f * (j + g) := by ring
      _ = (f + h + m) * (r0 + r2) - f * (p0 + u) := by
        rw [← hdiff]
        ring
      _ ≤ b * (r0 + r2) - f * (p0 + u) :=
        sub_le_sub_right hbmul _
      _ = h * (K + L) := hsum.symm
  rw [hZ, hE_R]
  nlinarith [hlower]

/-- Complete homogeneous scalar endpoint for the hard type-717 branch:
the opposite hull triangle `BCD` has area at least `3m`. -/
theorem hullFive300_cab717_z_three
    {m E p0 p1 u r0 s r2 j g h b f K L Z : ℝ}
    (hm : 0 < m)
    (hu : m ≤ u) (hj : m ≤ j) (hg : m ≤ g)
    (hh : m ≤ h) (hs : m ≤ s)
    (hf : m ≤ f) (hr0 : m ≤ r0) (hr2floor : m ≤ r2)
    (hE_P : E = p0 + p1 + u)
    (hE_R : E = r0 + s + r2)
    (hp1 : p1 = s + j + g)
    (hsector : r2 = u + j + h)
    (hcentralPair : j * r0 = g * r2 + h * s)
    (hpair : E * h = p0 * r2 - u * r0)
    (hbrow : E * b = K * p0 - L * u)
    (hfrow : E * f = K * r0 - L * r2)
    (hDPR : f + h + m ≤ b)
    (hZ : Z = K + L - E)
    (hcap : 2 * E ≤ 21 * m) :
    3 * m ≤ Z := by
  have hcore := hullFive300_cab717_homogeneous_core hm hu hj hg hh hs
    hsector hcentralPair hE_R hcap
  have houter := hullFive300_cab717_outer_z_lower hm hf hr0 hr2floor
    hj hg hs hE_P hE_R hp1 hsector hpair hbrow hfrow hDPR hZ
  have hhpos : 0 < h := lt_of_lt_of_le hm hh
  have hsurplus :
      (5 / 2 : ℝ) * m ^ 2 ≤ h * (Z - 3 * m) := by
    nlinarith [hcore, houter]
  have hnonneg : 0 ≤ h * (Z - 3 * m) := by
    have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
    nlinarith
  by_contra hnot
  have hneg : Z - 3 * m < 0 := by linarith
  have : h * (Z - 3 * m) < 0 := mul_neg_of_pos_of_neg hhpos hneg
  linarith

/-- Final two-branch scalar closure used by the geometry adapter.

`W=[ABD]` is a positive hull ear and `H=E+Z+W`.  If the central triangle is
large, its unconditional `17m/2` lower bound and the two usual hull ears
close directly.  In the remaining branch `hullFive300_cab717_z_three`
supplies the stronger opposite-triangle floor. -/
theorem hullFive300_cab717_hull_bound
    {m E p0 p1 u r0 s r2 j g h b f K L Z W H T F : ℝ}
    (hm : 0 < m)
    (hu : m ≤ u) (hj : m ≤ j) (hg : m ≤ g)
    (hh : m ≤ h) (hs : m ≤ s)
    (hf : m ≤ f) (hr0 : m ≤ r0) (hr2floor : m ≤ r2)
    (hW : m ≤ W) (hT : m ≤ T) (hF : m ≤ F)
    (hEfloor : (17 / 2 : ℝ) * m ≤ E)
    (hE_P : E = p0 + p1 + u)
    (hE_R : E = r0 + s + r2)
    (hp1 : p1 = s + j + g)
    (hsector : r2 = u + j + h)
    (hcentralPair : j * r0 = g * r2 + h * s)
    (hpair : E * h = p0 * r2 - u * r0)
    (hbrow : E * b = K * p0 - L * u)
    (hfrow : E * f = K * r0 - L * r2)
    (hDPR : f + h + m ≤ b)
    (hZ : Z = K + L - E)
    (hHullCentral : H = E + Z + W)
    (hHullEar : H = E + T + F) :
    25 * m ≤ 2 * H := by
  by_cases hcap : 2 * E ≤ 21 * m
  · have hZthree := hullFive300_cab717_z_three hm hu hj hg hh hs hf
      hr0 hr2floor hE_P hE_R hp1 hsector hcentralPair hpair hbrow hfrow
      hDPR hZ hcap
    nlinarith [hEfloor, hW, hHullCentral]
  · have hlarge : 21 * m < 2 * E := lt_of_not_ge hcap
    nlinarith [hT, hF, hHullEar]

end Heilbronn8.TriHull
