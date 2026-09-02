/-
Solution-side copy of the challenge definitions.

The official Comparator entry selects the four n = 8 declarations: polynomial
root support, exact value, attainment, and lower bound. The unified solution
also retains the proved n = 3 through n = 7 results, but those are outside the
official n = 8 entry.

`P5_root_existsUnique` and `P8_root_existsUnique` are supplied here because the
definition bodies of `v5` and `v8` name them. The P8 theorem is selected by the
official comparator; the P5 theorem supports the retained unified development.
Witness definitions are introduced later only where a proved result needs them.

The challenge and solution root modules are never imported together.
-/
import Mathlib
import HeilbronnValues

set_option linter.style.header false

namespace HeilbronnChallenge

-- Signed area (twice) of triangle pqr
def sig (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

-- Ordered triples of distinct indices from Fin n
def triples (n : Nat) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2

-- Nonemptiness witnesses (needed by inf'; verified by the kernel)
instance : Fact ((triples 3).Nonempty) := ⟨by decide⟩
instance : Fact ((triples 4).Nonempty) := ⟨by decide⟩
instance : Fact ((triples 5).Nonempty) := ⟨by decide⟩
instance : Fact ((triples 6).Nonempty) := ⟨by decide⟩
instance : Fact ((triples 7).Nonempty) := ⟨by decide⟩
instance : Fact ((triples 8).Nonempty) := ⟨by decide⟩

-- Minimum |sig| over all triples
noncomputable def minTri {n : Nat} [Fact ((triples n).Nonempty)]
    (v : Fin n → ℝ × ℝ) : ℝ :=
  (triples n).inf' Fact.out fun t =>
    |sig (v t.1) (v t.2.1) (v t.2.2)|

-- Admissible score: r is achieved as minTri/2 by some unit-hull config
def AdmissibleScore (n : Nat) [Fact ((triples n).Nonempty)] (r : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ 1 ∧
    ∃ p : Fin n → ℝ × ℝ,
      MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1 ∧
      minTri p = 2 * r

-- The Heilbronn convex function
noncomputable def h_convex (n : Nat) [Fact ((triples n).Nonempty)] : ℝ :=
  sSup {r : ℝ | AdmissibleScore n r}

-- Positive-determinant affine map
structure PosAffine where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  tx : ℝ
  ty : ℝ
  det_pos : 0 < a * d - b * c

def PosAffine.map (T : PosAffine) (p : ℝ × ℝ) : ℝ × ℝ :=
  (T.a * p.1 + T.b * p.2 + T.tx, T.c * p.1 + T.d * p.2 + T.ty)

-- Gauge equivalence: relabeling + positive-det affine map
def GaugeEquivalent {n : Nat} (v u : Fin n → ℝ × ℝ) : Prop :=
  ∃ (sigma : Equiv.Perm (Fin n)) (T : PosAffine),
    u = fun i => T.map (v (sigma i))

-- Target values ------------------------------------------------------

def P3 (x : ℝ) : ℝ := x - 1
noncomputable def v3 : ℝ := 1

def P4 (x : ℝ) : ℝ := 2 * x - 1
noncomputable def v4 : ℝ := 1 / 2

def P5 (x : ℝ) : ℝ := 5 * x ^ 2 - 5 * x + 1

theorem P5_root_existsUnique :
    ∃! x : ℝ, 276/1000 < x ∧ x < 277/1000 ∧ P5 x = 0 :=
  HeilbronnValues.v5_existsUnique

noncomputable def v5 : ℝ := Classical.choose P5_root_existsUnique.exists

def P6 (x : ℝ) : ℝ := 6 * x - 1
noncomputable def v6 : ℝ := 1 / 6

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

/-- A countably infinite, pairwise gauge-inequivalent subfamily. -/
noncomputable def sevenFamily (k : ℕ) : Fin 7 → ℝ × ℝ :=
  sevenFamilyAt (sevenFamilyParameter k)

def P8 (x : ℝ) : ℝ :=
  2060 * x ^ 5 - 2332 * x ^ 4 + 1064 * x ^ 3 - 240 * x ^ 2 + 26 * x - 1

theorem P8_root_existsUnique :
    ∃! x : ℝ, 79/1000 < x ∧ x < 81/1000 ∧ P8 x = 0 :=
  HeilbronnValues.v8_existsUnique

noncomputable def v8 : ℝ := Classical.choose P8_root_existsUnique.exists

/-! ## Closed form for `v5`

`v5` is defined by choice from a uniqueness statement, so its value has to be
recovered from that statement rather than by unfolding. Uniqueness identifies it
with the value layer's root, whose closed form is proved there. -/

theorem v5_spec : 276 / 1000 < v5 ∧ v5 < 277 / 1000 ∧ P5 v5 = 0 :=
  Classical.choose_spec P5_root_existsUnique.exists

theorem v5_eq_values : v5 = HeilbronnValues.v5 :=
  P5_root_existsUnique.unique v5_spec
    ⟨HeilbronnValues.v5_gt, HeilbronnValues.v5_lt, HeilbronnValues.v5_root⟩

theorem v5_eq : v5 = (5 - Real.sqrt 5) / 10 := by
  rw [v5_eq_values, HeilbronnValues.v5_eq]

end HeilbronnChallenge
