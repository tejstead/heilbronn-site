import Heilbronn8.HullSixOneFiveScalar

/-!
# Raw-bracket adapter for the hull-six `1 + 5` scalar lemma

This file records the exact algebraic boundary between the geometry and
`HullSixOneFiveScalar`.  It deliberately does not depend on a particular
encoding of planar points or oriented area.

For a counterclockwise hull cycle `(U,B₁,B₂,B₃,B₄,B₅)`, let
`P,Q` be the two non-hull points and let `m > 0`.  Choose the orientation
of `P,Q` so that `[P,Q,U] > 0` and `[P,Q,Bᵢ] < 0`, and put
`Uraw = [P,Q,U]`, `Aᵢ = [P,Bᵢ,Bᵢ₊₁]`, and
`Bᵢraw = -[P,Q,Bᵢ]`.

No concrete labeled hull cycle is asserted here.  A residual branch must
separately supply its cycle, the `1 + 5` sign split, and the identification
of `U,B₁,…,B₅,P,Q` before this adapter can be instantiated.

Then the four `Q`-fan areas are exactly
`Aᵢ + Bᵢ₊₁raw - Bᵢraw`.  If
`Eᵢ = [Bᵢ₋₁,Bᵢ,Bᵢ₊₁]`, the three ear identities are

`Bᵢraw * Eᵢ = Aᵢ₋₁ * (Bᵢraw - Bᵢ₊₁raw)
                    + Aᵢ * (Bᵢraw - Bᵢ₋₁raw)`.

For the edge crossed by the ray `UP`, put `Sᵢ = [P,U,Bᵢ]`; for
the edge crossed by `UQ`, put `Tᵢ = [Q,U,Bᵢ]`.  With the chain in
the order above, a crossing is normalized by
`Sᵢ ≥ m, Sᵢ₊₁ ≤ -m`, respectively
`Tᵢ ≥ m, Tᵢ₊₁ ≤ -m`.  The two required product identities are

`Uraw * Aᵢ = Bᵢ₊₁raw * Sᵢ - Bᵢraw * Sᵢ₊₁`,

`Uraw * (Aᵢ + Bᵢ₊₁raw - Bᵢraw)
  = Bᵢ₊₁raw * Tᵢ - Bᵢraw * Tᵢ₊₁`.

Both are the two-dimensional Plücker identity.  The sign floors turn them
into the two crossing inequalities expected by the scalar theorem.
-/

namespace Heilbronn8

/- Raw positive quantities before division by the common triangle floor. -/
structure HullSixOneFiveRawData where
  m : ℝ
  A₁ : ℝ
  A₂ : ℝ
  A₃ : ℝ
  A₄ : ℝ
  B₁ : ℝ
  B₂ : ℝ
  B₃ : ℝ
  B₄ : ℝ
  B₅ : ℝ
  E₂ : ℝ
  E₃ : ℝ
  E₄ : ℝ
  hm : 0 < m
  hA₁ : m ≤ A₁
  hA₂ : m ≤ A₂
  hA₃ : m ≤ A₃
  hA₄ : m ≤ A₄
  hB₁ : m ≤ B₁
  hB₂ : m ≤ B₂
  hB₃ : m ≤ B₃
  hB₄ : m ≤ B₄
  hB₅ : m ≤ B₅
  hC₁ : m ≤ A₁ + B₂ - B₁
  hC₂ : m ≤ A₂ + B₃ - B₂
  hC₃ : m ≤ A₃ + B₄ - B₃
  hC₄ : m ≤ A₄ + B₅ - B₄
  hE₂ : m ≤ E₂
  hE₃ : m ≤ E₃
  hE₄ : m ≤ E₄
  ear₂_identity :
    B₂ * E₂ = A₁ * (B₂ - B₃) + A₂ * (B₂ - B₁)
  ear₃_identity :
    B₃ * E₃ = A₂ * (B₃ - B₄) + A₃ * (B₃ - B₂)
  ear₄_identity :
    B₄ * E₄ = A₃ * (B₄ - B₅) + A₄ * (B₄ - B₃)

namespace HullSixOneFiveRawData

def aRawAt (R : HullSixOneFiveRawData) : Fin 4 → ℝ :=
  ![R.A₁, R.A₂, R.A₃, R.A₄]

def bRawAt (R : HullSixOneFiveRawData) : Fin 5 → ℝ :=
  ![R.B₁, R.B₂, R.B₃, R.B₄, R.B₅]

def cRawAt (R : HullSixOneFiveRawData) : Fin 4 → ℝ :=
  ![R.A₁ + R.B₂ - R.B₁, R.A₂ + R.B₃ - R.B₂,
    R.A₃ + R.B₄ - R.B₃, R.A₄ + R.B₅ - R.B₄]

private lemma normalized_ear
    {m Aleft Aright Bleft B Bnext E : ℝ}
    (hm : 0 < m) (hB : m ≤ B) (hE : m ≤ E)
    (hid : B * E =
      Aleft * (B - Bnext) + Aright * (B - Bleft)) :
    B / m ≤
      (Aleft / m) * (B / m - Bnext / m) +
        (Aright / m) * (B / m - Bleft / m) := by
  have hBn : 1 ≤ B / m := (le_div_iff₀ hm).2 (by simpa using hB)
  have hEn : 1 ≤ E / m := (le_div_iff₀ hm).2 (by simpa using hE)
  have hmul : B / m ≤ (B / m) * (E / m) := by
    have := mul_le_mul_of_nonneg_left hEn (by linarith only [hBn])
    simpa using this
  calc
    B / m ≤ (B / m) * (E / m) := hmul
    _ = (Aleft / m) * (B / m - Bnext / m) +
          (Aright / m) * (B / m - Bleft / m) := by
      field_simp [ne_of_gt hm]
      nlinarith only [hid]

/-- Divide the raw determinant package by its common lower bound. -/
noncomputable def normalize (R : HullSixOneFiveRawData) : HullSixOneFiveData where
  a₁ := R.A₁ / R.m
  a₂ := R.A₂ / R.m
  a₃ := R.A₃ / R.m
  a₄ := R.A₄ / R.m
  b₁ := R.B₁ / R.m
  b₂ := R.B₂ / R.m
  b₃ := R.B₃ / R.m
  b₄ := R.B₄ / R.m
  b₅ := R.B₅ / R.m
  ha₁ := (le_div_iff₀ R.hm).2 (by simpa using R.hA₁)
  ha₂ := (le_div_iff₀ R.hm).2 (by simpa using R.hA₂)
  ha₃ := (le_div_iff₀ R.hm).2 (by simpa using R.hA₃)
  ha₄ := (le_div_iff₀ R.hm).2 (by simpa using R.hA₄)
  hb₁ := (le_div_iff₀ R.hm).2 (by simpa using R.hB₁)
  hb₂ := (le_div_iff₀ R.hm).2 (by simpa using R.hB₂)
  hb₃ := (le_div_iff₀ R.hm).2 (by simpa using R.hB₃)
  hb₄ := (le_div_iff₀ R.hm).2 (by simpa using R.hB₄)
  hb₅ := (le_div_iff₀ R.hm).2 (by simpa using R.hB₅)
  hc₁ := by
    rw [show R.A₁ / R.m + R.B₂ / R.m - R.B₁ / R.m =
      (R.A₁ + R.B₂ - R.B₁) / R.m by ring]
    exact (le_div_iff₀ R.hm).2 (by simpa using R.hC₁)
  hc₂ := by
    rw [show R.A₂ / R.m + R.B₃ / R.m - R.B₂ / R.m =
      (R.A₂ + R.B₃ - R.B₂) / R.m by ring]
    exact (le_div_iff₀ R.hm).2 (by simpa using R.hC₂)
  hc₃ := by
    rw [show R.A₃ / R.m + R.B₄ / R.m - R.B₃ / R.m =
      (R.A₃ + R.B₄ - R.B₃) / R.m by ring]
    exact (le_div_iff₀ R.hm).2 (by simpa using R.hC₃)
  hc₄ := by
    rw [show R.A₄ / R.m + R.B₅ / R.m - R.B₄ / R.m =
      (R.A₄ + R.B₅ - R.B₄) / R.m by ring]
    exact (le_div_iff₀ R.hm).2 (by simpa using R.hC₄)
  ear₂ := normalized_ear R.hm R.hB₂ R.hE₂ R.ear₂_identity
  ear₃ := normalized_ear R.hm R.hB₃ R.hE₃ R.ear₃_identity
  ear₄ := normalized_ear R.hm R.hB₄ R.hE₄ R.ear₄_identity

/-- The normalized `Q`-fan entry is the corresponding raw determinant divided
by the common triangle floor. -/
lemma normalize_cAt (R : HullSixOneFiveRawData) (i : Fin 4) :
    R.normalize.cAt i = R.cRawAt i / R.m := by
  fin_cases i <;>
    simp [normalize, HullSixOneFiveData.cAt, cRawAt] <;>
    field_simp [ne_of_gt R.hm] <;>
    ring

/-- Every entry of the raw five-term line-level vector has the common
triangle floor. -/
lemma hBRawAt (R : HullSixOneFiveRawData) (i : Fin 5) :
    R.m ≤ R.bRawAt i := by
  fin_cases i
  · simpa [bRawAt] using R.hB₁
  · simpa [bRawAt] using R.hB₂
  · simpa [bRawAt] using R.hB₃
  · simpa [bRawAt] using R.hB₄
  · simpa [bRawAt] using R.hB₅

/-- The order of the two ray crossings is already a one-line consequence of
the affine cocycle identity.  In geometry, take
`S i = [P,U,B i]` and `T i = [Q,U,B i]`.  Then
`T i = S i + [P,Q,U] - [P,Q,B i] = S i + U + B i`.

Convexity is used only to say that the `S` signs form a positive prefix (and,
dually, that `T (l+1)` is negative just after its crossing).  No enumeration
of the ten pairs `(k,l)` is needed. -/
theorem ordered_crossings_of_shift
    (R : HullSixOneFiveRawData) (U : ℝ) (hU : R.m ≤ U)
    (S T : Fin 5 → ℝ)
    (hshift : ∀ i, T i = S i + U + R.bRawAt i)
    (k l : Fin 4)
    (hS_prefix : ∀ i : Fin 5, i.val ≤ k.val → R.m ≤ S i)
    (hT_after : T l.succ ≤ -R.m) :
    k ≤ l := by
  by_contra hkl
  have hindex : l.succ.val ≤ k.val := by
    have hlk : l < k := lt_of_not_ge hkl
    have hval : l.val < k.val := hlk
    simpa using hval
  have hS := hS_prefix l.succ hindex
  have hB := R.hBRawAt l.succ
  have hEq := hshift l.succ
  linarith [R.hm]

/-- A raw Plucker product identity and the four signed triangle floors imply
the normalized crossing inequality used by the scalar theorem. -/
lemma raw_crossing_le
    {m U A Bleft Bright Sleft Sright : ℝ}
    (hm : 0 < m) (hBleft : m ≤ Bleft) (hBright : m ≤ Bright)
    (hSleft : m ≤ Sleft) (hSright : Sright ≤ -m)
    (hplucker : U * A = Bright * Sleft - Bleft * Sright) :
    Bleft / m + Bright / m ≤ (U / m) * (A / m) := by
  have hBleftN : 1 ≤ Bleft / m :=
    (le_div_iff₀ hm).2 (by simpa using hBleft)
  have hBrightN : 1 ≤ Bright / m :=
    (le_div_iff₀ hm).2 (by simpa using hBright)
  have hSleftN : 1 ≤ Sleft / m :=
    (le_div_iff₀ hm).2 (by simpa using hSleft)
  have hSrightN : 1 ≤ (-Sright) / m :=
    (le_div_iff₀ hm).2 (by linarith only [hSright])
  have hleftTerm : Bright / m ≤ (Bright / m) * (Sleft / m) := by
    have := mul_le_mul_of_nonneg_left hSleftN (by linarith only [hBrightN])
    simpa using this
  have hrightTerm : Bleft / m ≤ (Bleft / m) * ((-Sright) / m) := by
    have := mul_le_mul_of_nonneg_left hSrightN (by linarith only [hBleftN])
    simpa using this
  calc
    Bleft / m + Bright / m ≤
        (Bright / m) * (Sleft / m) +
          (Bleft / m) * ((-Sright) / m) := by
      linarith only [hleftTerm, hrightTerm]
    _ = (U / m) * (A / m) := by
      field_simp [ne_of_gt hm]
      nlinarith only [hplucker]

/-- Compact raw-bracket form of the geometric adapter.

The two pairs `SPleft, SPright` and `TQleft, TQright` are the signed spoke
areas on the two crossed lower-chain edges.  Thus the only genuinely
geometric work left outside this theorem is:

1. identify the two crossed edges and prove `k ≤ l`;
2. prove the four spoke sign floors;
3. discharge the two displayed Plücker identities (normally by `ring`);
4. choose the chain direction so that `B₅ ≤ B₁`.
-/
theorem crossingParameter_ge_five_fourths_raw
    (R : HullSixOneFiveRawData)
    (horder : R.B₅ ≤ R.B₁)
    (harea : R.A₁ / R.m + R.A₂ / R.m +
      R.A₃ / R.m + R.A₄ / R.m < 17 / 2)
    (k l : Fin 4) (hkl : k ≤ l)
    (U SPleft SPright TQleft TQright : ℝ)
    (hSPleft : R.m ≤ SPleft) (hSPright : SPright ≤ -R.m)
    (hTQleft : R.m ≤ TQleft) (hTQright : TQright ≤ -R.m)
    (hpluckerP : U * R.aRawAt k =
      R.bRawAt k.succ * SPleft - R.bRawAt k.castSucc * SPright)
    (hpluckerQ : U * R.cRawAt l =
      R.bRawAt l.succ * TQleft - R.bRawAt l.castSucc * TQright) :
    5 / 4 ≤ U / R.m := by
  let D := R.normalize
  have horderD : D.b₅ ≤ D.b₁ := by
    dsimp [D, normalize]
    exact (div_le_div_iff_of_pos_right R.hm).2 horder
  have hareaD : D.area < 17 / 2 := by
    simpa [D, normalize, HullSixOneFiveData.area] using harea
  have hcrossA : D.adjacentSum k ≤ (U / R.m) * D.aAt k := by
    have h := raw_crossing_le R.hm
      (R.hBRawAt k.castSucc) (R.hBRawAt k.succ)
      hSPleft hSPright hpluckerP
    fin_cases k <;>
      simpa [D, normalize, HullSixOneFiveData.adjacentSum,
        HullSixOneFiveData.aAt, aRawAt, bRawAt] using h
  have hcrossC : D.adjacentSum l ≤ (U / R.m) * D.cAt l := by
    have h := raw_crossing_le R.hm
      (R.hBRawAt l.castSucc) (R.hBRawAt l.succ)
      hTQleft hTQright hpluckerQ
    rw [show D.cAt l = R.cRawAt l / R.m by
      simpa [D] using R.normalize_cAt l]
    fin_cases l <;>
      simpa [D, normalize, HullSixOneFiveData.adjacentSum,
        bRawAt] using h
  exact D.crossingParameter_ge_five_fourths horderD hareaD
    k l hkl (U / R.m) hcrossA hcrossC

end HullSixOneFiveRawData

end Heilbronn8
