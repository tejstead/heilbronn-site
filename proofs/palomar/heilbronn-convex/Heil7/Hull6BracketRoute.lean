import Heil7.CanonicalUpper

/-!
# The exact hull-six radial-bracket seam

This source-only scratch module isolates the one genuinely nonlinear input in
the hull-six case.  If `R` is the unique interior point and

`b i j = sig (V i) (V j) R`,

then skew-symmetry and the Grassmann--Pluecker relation are identities.  The
triangle floors through `R`, all twenty hull-triangle floors, and the six positive
boundary brackets are exactly the information available from `minTri`,
`HullCCW`, and `InHullN`.  Thus `H6BracketCore` is a scalar statement with no
hidden geometric premise.  The theorem below proves the complete point-to-
bracket adapter and matches the `HullCaseBounds.h6` field.

No assertion of `H6BracketCore` is made here.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- The remaining normalized scalar theorem for a convex hexagon and one
interior point, written homogeneously at floor `m`.

The Pluecker relation is included for every four radial indices rather than
only for cyclically ordered indices, which makes this interface insensitive to
the eventual chamber proof. -/
def H6BracketCore : Prop :=
  ∀ (m : ℝ) (b : Fin 6 → Fin 6 → ℝ),
    0 < m →
    (∀ i j, b i j = -b j i) →
    (∀ i j k l,
      b i j * b k l - b i k * b j l + b i l * b j k = 0) →
    (∀ i j, i ≠ j → m ≤ |b i j|) →
    (∀ i j k, i < j → j < k →
      m ≤ b i j + b j k - b i k) →
    (∀ i : Fin 6, 0 < b i (i + 1)) →
    9 * m ≤
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0

/-- Every hypothesis of `H6BracketCore` is forced by the canonical hull-six
geometry.  Consequently a proof of that one scalar proposition supplies the
`HullCaseBounds.h6` field verbatim. -/
theorem hullSix_of_bracketCore (core : H6BracketCore) :
    ∀ (v : Configuration7), HullCCW v 6 →
      (∀ p : Fin 7, 6 ≤ (p : ℕ) → InHullN v 6 p) →
      9 * minTri v ≤ fanArea v 6 := by
  intro v hccw hin
  rcases eq_or_lt_of_le (minTri_nonneg v) with hzero | hm
  · have h012 := hccw 0 1 2 (by decide) (by decide) (by norm_num)
    have h023 := hccw 0 2 3 (by decide) (by decide) (by norm_num)
    have h034 := hccw 0 3 4 (by decide) (by decide) (by norm_num)
    have h045 := hccw 0 4 5 (by decide) (by decide) (by norm_num)
    rw [← hzero]
    simp only [zero_mul, fanArea]
    linarith
  · let b : Fin 6 → Fin 6 → ℝ :=
      fun i j => sig (v i.castSucc) (v j.castSucc) (v 6)
    have hcast6 : ∀ i : Fin 6, i.castSucc ≠ (6 : Fin 7) := by
      intro i hieq
      have hval := congrArg Fin.val hieq
      change i.val = 6 at hval
      omega
    have hskew : ∀ i j, b i j = -b j i := by
      intro i j
      simp only [b, sig]
      ring
    have hpluecker : ∀ i j k l,
        b i j * b k l - b i k * b j l + b i l * b j k = 0 := by
      intro i j k l
      simp only [b, sig]
      ring
    have hradial : ∀ i j, i ≠ j → minTri v ≤ |b i j| := by
      intro i j hij
      exact minTri_le_of_distinct v i.castSucc j.castSucc 6
        ((Fin.castSucc_injective 6).ne hij) (hcast6 i) (hcast6 j)
    have hhull : ∀ i j k : Fin 6, i < j → j < k →
        minTri v ≤ b i j + b j k - b i k := by
      intro i j k hij hjk
      have hpos : 0 < sig (v i.castSucc) (v j.castSucc) (v k.castSucc) :=
        hccw i.castSucc j.castSucc k.castSucc
          (by simpa using hij) (by simpa using hjk) (by simpa using k.isLt)
      have hfloor := minTri_le_of_distinct v
        i.castSucc j.castSucc k.castSucc
        ((Fin.castSucc_injective 6).ne (ne_of_lt hij))
        ((Fin.castSucc_injective 6).ne (ne_of_lt (lt_trans hij hjk)))
        ((Fin.castSucc_injective 6).ne (ne_of_lt hjk))
      rw [abs_of_pos hpos] at hfloor
      have hid :
          b i j + b j k - b i k =
            sig (v i.castSucc) (v j.castSucc) (v k.castSucc) := by
        simp only [b, sig]
        ring
      rwa [hid]
    have hp6 := hin 6 (by norm_num)
    have hedge : ∀ i : Fin 6, 0 < b i (i + 1) := by
      intro i
      fin_cases i
      · simpa [b] using hp6.1 0 (by norm_num)
      · simpa [b] using hp6.1 1 (by norm_num)
      · simpa [b] using hp6.1 2 (by norm_num)
      · simpa [b] using hp6.1 3 (by norm_num)
      · simpa [b] using hp6.1 4 (by norm_num)
      · simpa [b] using hp6.2 5 (by norm_num)
    have hscalar := core (minTri v) b hm hskew hpluecker hradial hhull hedge
    have hsum :
        b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 =
          fanArea v 6 := by
      have hcast0 : ((0 : Fin 6).castSucc : Fin 7) = 0 := by decide
      have hcast1 : ((1 : Fin 6).castSucc : Fin 7) = 1 := by decide
      have hcast2 : ((2 : Fin 6).castSucc : Fin 7) = 2 := by decide
      have hcast3 : ((3 : Fin 6).castSucc : Fin 7) = 3 := by decide
      have hcast4 : ((4 : Fin 6).castSucc : Fin 7) = 4 := by decide
      have hcast5 : ((5 : Fin 6).castSucc : Fin 7) = 5 := by decide
      simp only [b]
      rw [hcast0, hcast1, hcast2, hcast3, hcast4, hcast5]
      simp only [fanArea, sig]
      ring
    rwa [hsum] at hscalar

end HeilbronnChallenge.N7Upper
