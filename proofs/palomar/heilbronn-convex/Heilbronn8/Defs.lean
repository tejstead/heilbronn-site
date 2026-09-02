/-
Finite geometry core for the convex Heilbronn n = 8 development.

`HullCyclePos cycle v` records all cyclic triple orientations, rather than
only the consecutive edges. This is the weak ConvexPos-style formulation
most useful to phase 2: arbitrary diagonals and cyclic subpolygons can
consume it without first deriving the other 28 orientations.
-/
import Mathlib

namespace Heilbronn8

/-- Doubled signed area of the triangle `p q r`. -/
def sig (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

lemma sig_rotate (p q r : ℝ × ℝ) : sig p q r = sig q r p := by
  simp only [sig]
  ring

lemma sig_swap (p q r : ℝ × ℝ) : sig p q r = -sig p r q := by
  simp only [sig]
  ring

lemma sig_affine_fst (a b c q r : ℝ × ℝ) (x y z : ℝ)
    (hxyz : x + y + z = 1) :
    sig (x • a + y • b + z • c) q r
      = x * sig a q r + y * sig b q r + z * sig c q r := by
  have hz : z = 1 - x - y := by
    linarith
  subst hz
  simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, smul_eq_mul]
  ring

/-- The 56 increasing triples of `Fin 8`. -/
def triples : Finset (Fin 8 × Fin 8 × Fin 8) :=
  Finset.univ.filter fun t =>
    t.1 < t.2.1 ∧ t.2.1 < t.2.2

lemma triples_nonempty : triples.Nonempty := by
  refine ⟨(0, 1, 2), ?_⟩
  simp [triples]

lemma triples_card : triples.card = 56 := by
  decide

/-- Doubled minimum triangle area among the 56 unordered triples. -/
noncomputable def minTri (v : Fin 8 → ℝ × ℝ) : ℝ :=
  triples.inf' triples_nonempty fun t =>
    |sig (v t.1) (v t.2.1) (v t.2.2)|

/-- A generic projection from `minTri` to an increasing triple. -/
lemma minTri_le (v : Fin 8 → ℝ × ℝ) {i j k : Fin 8}
    (hij : i < j) (hjk : j < k) :
    minTri v ≤ |sig (v i) (v j) (v k)| := by
  unfold minTri
  exact Finset.inf'_le
    (fun t : Fin 8 × Fin 8 × Fin 8 =>
      |sig (v t.1) (v t.2.1) (v t.2.2)|)
    (by
      simp [triples, hij, hjk] :
        (i, j, k) ∈ triples)

/-- Converse universal property of `minTri`. -/
lemma le_minTri (v : Fin 8 → ℝ × ℝ) {a : ℝ}
    (h : ∀ i j k : Fin 8, i < j → j < k →
      a ≤ |sig (v i) (v j) (v k)|) :
    a ≤ minTri v := by
  unfold minTri
  apply Finset.le_inf'
  intro t ht
  simp only [triples, Finset.mem_filter, Finset.mem_univ,
    true_and] at ht
  exact h t.1 t.2.1 t.2.2 ht.1 ht.2

lemma minTri_nonneg (v : Fin 8 → ℝ × ℝ) :
    0 ≤ minTri v :=
  le_minTri v fun _ _ _ _ _ => abs_nonneg _

/-- Membership in the convex hull of three points, in coordinates. -/
def InTri (p a b c : ℝ × ℝ) : Prop :=
  ∃ x y z : ℝ,
    0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
    x + y + z = 1 ∧
    p = x • a + y • b + z • c

/--
All triples occurring in the order supplied by `cycle` are weakly
counterclockwise. For a seven-point cycle this contains 35 inequalities.
-/
def CyclicPos {m : ℕ} (cycle : Fin m → Fin 8)
    (v : Fin 8 → ℝ × ℝ) : Prop :=
  ∀ i j k : Fin m, i < j → j < k →
    0 ≤ sig (v (cycle i)) (v (cycle j)) (v (cycle k))

/-- The verified seven-point hull cycle. -/
def hullCycle : Fin 7 → Fin 8 :=
  ![7, 4, 2, 0, 1, 3, 6]

/-- Weak convex position in the verified hull order. -/
def HullCyclePos (v : Fin 8 → ℝ × ℝ) : Prop :=
  CyclicPos hullCycle v

/-- Doubled hull area, using the fan from hull vertex 7. -/
def H2 (v : Fin 8 → ℝ × ℝ) : ℝ :=
  sig (v (hullCycle 0)) (v (hullCycle 1)) (v (hullCycle 2)) +
  sig (v (hullCycle 0)) (v (hullCycle 2)) (v (hullCycle 3)) +
  sig (v (hullCycle 0)) (v (hullCycle 3)) (v (hullCycle 4)) +
  sig (v (hullCycle 0)) (v (hullCycle 4)) (v (hullCycle 5)) +
  sig (v (hullCycle 0)) (v (hullCycle 5)) (v (hullCycle 6))

end Heilbronn8
