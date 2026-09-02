/- Unified convex Heilbronn challenge for n = 3, 4, 5, 6, 7, 8. -/
import Mathlib

namespace HeilbronnChallenge

/-! ## Common definitions -/
/-- Twice the signed area of the triangle `pqr`. -/
def sig (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

/-- Increasing triples of distinct indices. -/
def triples (n : Nat) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter fun t ↦ t.1 < t.2.1 ∧ t.2.1 < t.2.2

instance : Fact ((triples 3).Nonempty) := ⟨by decide⟩
instance : Fact ((triples 4).Nonempty) := ⟨by decide⟩
instance : Fact ((triples 5).Nonempty) := ⟨by decide⟩
instance : Fact ((triples 6).Nonempty) := ⟨by decide⟩
instance : Fact ((triples 7).Nonempty) := ⟨by decide⟩
instance : Fact ((triples 8).Nonempty) := ⟨by decide⟩

/-- Minimum absolute doubled triangle area. -/
noncomputable def minTri {n : Nat} [Fact ((triples n).Nonempty)]
    (v : Fin n → ℝ × ℝ) : ℝ :=
  (triples n).inf' Fact.out fun t ↦
    |sig (v t.1) (v t.2.1) (v t.2.2)|

/-- A normalized score realized by a unit-hull configuration. -/
def AdmissibleScore (n : Nat) [Fact ((triples n).Nonempty)] (r : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ 1 ∧
    ∃ p : Fin n → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * r

/-- The convex Heilbronn function. -/
noncomputable def h_convex (n : Nat) [Fact ((triples n).Nonempty)] : ℝ :=
  sSup {r : ℝ | AdmissibleScore n r}

/-- A nonsingular affine map of the plane. -/
structure NonsingularAffine where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  tx : ℝ
  ty : ℝ
  det_ne : a * d - b * c ≠ 0

def NonsingularAffine.map (T : NonsingularAffine) (p : ℝ × ℝ) : ℝ × ℝ :=
  (T.a * p.1 + T.b * p.2 + T.tx,
    T.c * p.1 + T.d * p.2 + T.ty)

/-- Equivalence by arbitrary relabeling and any nonsingular affine map. -/
def AffineEquivalent {n : Nat} (v u : Fin n → ℝ × ℝ) : Prop :=
  ∃ (sigma : Equiv.Perm (Fin n)) (T : NonsingularAffine),
    u = fun i ↦ T.map (v (sigma i))

/-- An orientation-preserving affine map of the plane. -/
structure PosAffine where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  tx : ℝ
  ty : ℝ
  det_pos : 0 < a * d - b * c

def PosAffine.map (T : PosAffine) (p : ℝ × ℝ) : ℝ × ℝ :=
  (T.a * p.1 + T.b * p.2 + T.tx,
    T.c * p.1 + T.d * p.2 + T.ty)

/-- Equivalence by arbitrary relabeling and a positive-determinant affine map. -/
def GaugeEquivalent {n : Nat} (v u : Fin n → ℝ × ℝ) : Prop :=
  ∃ (sigma : Equiv.Perm (Fin n)) (T : PosAffine),
    u = fun i ↦ T.map (v (sigma i))

/-! ## n = 3 -/
def P3 (x : ℝ) : ℝ := x - 1
noncomputable def v3 : ℝ := 1

theorem heilbronn_convex_three_upper_bound
    (p : Fin 3 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v3 := by
  sorry
theorem heilbronn_convex_three_attained :
    ∃ p : Fin 3 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v3 := by
  sorry
theorem heilbronn_convex_three : h_convex 3 = v3 := by
  sorry
theorem heilbronn_convex_three_unique
    (p q : Fin 3 → ℝ × ℝ)
    (hpvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hqvol : MeasureTheory.volume (convexHull ℝ (Set.range q)) = 1)
    (hpopt : minTri p = 2 * v3) (hqopt : minTri q = 2 * v3) :
    AffineEquivalent p q := by
  sorry
/-! ## n = 4 -/
def P4 (x : ℝ) : ℝ := 2 * x - 1
noncomputable def v4 : ℝ := 1 / 2

theorem heilbronn_convex_four_upper_bound
    (p : Fin 4 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v4 := by
  sorry
theorem heilbronn_convex_four_attained :
    ∃ p : Fin 4 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v4 := by
  sorry
theorem heilbronn_convex_four : h_convex 4 = v4 := by
  sorry
theorem heilbronn_convex_four_unique
    (p q : Fin 4 → ℝ × ℝ)
    (hpvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hqvol : MeasureTheory.volume (convexHull ℝ (Set.range q)) = 1)
    (hpopt : minTri p = 2 * v4) (hqopt : minTri q = 2 * v4) :
    AffineEquivalent p q := by
  sorry
/-! ## n = 5 -/
def P5 (x : ℝ) : ℝ := 5 * x ^ 2 - 5 * x + 1

/-- The selected root is the unique root of `P5` in its narrow bracket. -/
theorem P5_root_existsUnique :
    ∃! x : ℝ, 276 / 1000 < x ∧ x < 277 / 1000 ∧ P5 x = 0 := by
  sorry
noncomputable def v5 : ℝ := Classical.choose P5_root_existsUnique.exists

theorem heilbronn_convex_five_upper_bound
    (p : Fin 5 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v5 := by
  sorry
theorem heilbronn_convex_five_attained :
    ∃ p : Fin 5 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v5 := by
  sorry
theorem heilbronn_convex_five : h_convex 5 = v5 := by
  sorry
theorem heilbronn_convex_five_unique
    (p q : Fin 5 → ℝ × ℝ)
    (hpvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hqvol : MeasureTheory.volume (convexHull ℝ (Set.range q)) = 1)
    (hpopt : minTri p = 2 * v5) (hqopt : minTri q = 2 * v5) :
    AffineEquivalent p q := by
  sorry
/-! ## n = 6 -/
def P6 (x : ℝ) : ℝ := 6 * x - 1
noncomputable def v6 : ℝ := 1 / 6

theorem heilbronn_convex_six_upper_bound
    (p : Fin 6 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v6 := by
  sorry
theorem heilbronn_convex_six_attained :
    ∃ p : Fin 6 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v6 := by
  sorry
theorem heilbronn_convex_six : h_convex 6 = v6 := by
  sorry
theorem heilbronn_convex_six_unique
    (p q : Fin 6 → ℝ × ℝ)
    (hpvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hqvol : MeasureTheory.volume (convexHull ℝ (Set.range q)) = 1)
    (hpopt : minTri p = 2 * v6) (hqopt : minTri q = 2 * v6) :
    AffineEquivalent p q := by
  sorry
/-! ## n = 7 -/
def P7 (x : ℝ) : ℝ := 9 * x - 1
noncomputable def v7 : ℝ := 1 / 9

/-- A rational parameter sequence contained in `[6/5, 5/4)`. -/
noncomputable def sevenFamilyParameter (k : ℕ) : ℝ :=
  5 / 4 - 1 / (20 * ((k : ℝ) + 1))

/-- The explicit real-parameter family of seven-point configurations. -/
noncomputable def sevenFamilyAt (t : ℝ) : Fin 7 → ℝ × ℝ :=
  ![(-((2 : ℝ) / 3) * (1 / t), -2 / 3),
    (-1 / 3, -(2 * t) / 3),
    (((2 : ℝ) / 3) * (1 / t), 0),
    (2 / 3, t / 3),
    (0, 2 / 3),
    (-1 / 3, t / 3),
    (0, 0)]

/-- A countably infinite, pairwise affine-inequivalent subfamily. -/
noncomputable def sevenFamily (k : ℕ) : Fin 7 → ℝ × ℝ :=
  sevenFamilyAt (sevenFamilyParameter k)

theorem heilbronn_convex_seven_upper_bound
    (p : Fin 7 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v7 := by
  sorry
theorem heilbronn_convex_seven_attained :
    ∃ p : Fin 7 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v7 := by
  sorry
theorem heilbronn_convex_seven : h_convex 7 = v7 := by
  sorry
/-- Every member of the full real family is a unit-hull optimizer. -/
theorem heilbronn_convex_seven_family_attains
    (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 4 / 3) :
    MeasureTheory.volume
        (convexHull ℝ (Set.range (sevenFamilyAt t))) = 1 ∧
      minTri (sevenFamilyAt t) = 2 * v7 := by
  sorry
/-- The indicated real subinterval gives pairwise affine-inequivalent
optimizers, hence a continuum-parameterized family of optimizer orbits. -/
theorem heilbronn_convex_seven_real_family_inequivalent
    (s t : ℝ)
    (hs : 6 / 5 ≤ s ∧ s ≤ 5 / 4)
    (ht : 6 / 5 ≤ t ∧ t ≤ 5 / 4) :
    AffineEquivalent (sevenFamilyAt s) (sevenFamilyAt t) → s = t := by
  sorry
/-- Every unit-hull optimizer belongs to the explicit family up to an
arbitrary nonsingular affine map and relabeling. -/
theorem heilbronn_convex_seven_optimizer_classification
    (p : Fin 7 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p = 2 * v7 ↔
      ∃ t : ℝ, 1 ≤ t ∧ t ≤ 4 / 3 ∧
        AffineEquivalent (sevenFamilyAt t) p := by
  sorry
/-- A continuum of parameters gives pairwise affine-inequivalent unit-hull
optimizers. -/
theorem heilbronn_convex_seven_infinite_optimizers :
    Cardinal.mk (Set.Icc ((6 : ℝ) / 5) (5 / 4)) = Cardinal.continuum ∧
    (∀ t : ℝ, t ∈ Set.Icc ((6 : ℝ) / 5) (5 / 4) →
      MeasureTheory.volume
          (convexHull ℝ (Set.range (sevenFamilyAt t))) = 1 ∧
        minTri (sevenFamilyAt t) = 2 * v7) ∧
    ∀ s t : ℝ,
      s ∈ Set.Icc ((6 : ℝ) / 5) (5 / 4) →
      t ∈ Set.Icc ((6 : ℝ) / 5) (5 / 4) →
      AffineEquivalent (sevenFamilyAt s) (sevenFamilyAt t) → s = t := by
  sorry
/-! ## n = 8 -/
def P8 (x : ℝ) : ℝ :=
  2060 * x ^ 5 - 2332 * x ^ 4 + 1064 * x ^ 3 - 240 * x ^ 2 + 26 * x - 1

/-- The selected root is the unique root of `P8` in its narrow bracket. -/
theorem P8_root_existsUnique :
    ∃! x : ℝ, 79 / 1000 < x ∧ x < 81 / 1000 ∧ P8 x = 0 := by
  sorry
noncomputable def v8 : ℝ := Classical.choose P8_root_existsUnique.exists

theorem heilbronn_convex_eight_upper_bound
    (p : Fin 8 → ℝ × ℝ)
    (hvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1) :
    minTri p ≤ 2 * v8 := by
  sorry
theorem heilbronn_convex_eight_attained :
    ∃ p : Fin 8 → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * v8 := by
  sorry
theorem heilbronn_convex_eight : h_convex 8 = v8 := by
  sorry
theorem heilbronn_convex_eight_unique
    (p q : Fin 8 → ℝ × ℝ)
    (hpvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hqvol : MeasureTheory.volume (convexHull ℝ (Set.range q)) = 1)
    (hpopt : minTri p = 2 * v8) (hqopt : minTri q = 2 * v8) :
    AffineEquivalent p q := by
  sorry
end HeilbronnChallenge
