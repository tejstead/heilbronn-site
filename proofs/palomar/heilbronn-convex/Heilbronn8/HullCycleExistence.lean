import Heilbronn8.HullCycleCarrier
import Heilbronn8.HullCycleOrder
import Heilbronn8.HullCycleFanCover

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-!
# Existence of a strict finite hull cycle

This module assembles the three certificate-free pieces:

* finite extreme points give an irredundant carrier;
* orientation about an anchor orders the carrier into a strict CCW cycle;
* planar Caratheodory and one diagonal split give the anchored fan cover.
-/

/-- A geometric hull-cycle witness, including the local nonzero-size
instance required by `FanCovers`. -/
structure StrictHullCycleWitness (v : Fin 8 → ℝ × ℝ) where
  size : ℕ
  size_ge_three : 3 ≤ size
  size_le_eight : size ≤ 8
  neZero : NeZero size
  cycle : Fin size → Fin 8
  injective : Function.Injective cycle
  strictCyclicPos : StrictCyclicPos cycle v
  fanCovers : @FanCovers size neZero v cycle

/-- Positive minimum triangle area is the strict-sign branch of the
top-level dispatcher. -/
lemma allTripleSignsStrict_of_minTri_pos
    (v : Fin 8 → ℝ × ℝ) (hmin : 0 < minTri v) :
    AllTripleSignsStrict v := by
  intro i j k hij hjk hzero
  have hle := minTri_le v hij hjk
  rw [hzero, abs_zero] at hle
  linarith

/-- Every strict eight-point planar configuration has an injective strict
CCW hull cycle whose anchored fan contains all omitted configuration
points. -/
noncomputable def strictHullCycleWitness_exists
    (v : Fin 8 → ℝ × ℝ) (hstrict : AllTripleSignsStrict v) :
    StrictHullCycleWitness v := by
  classical
  let carrier := strictHullCarrier_exists v hstrict
  let hex := exists_strictCyclicPos_order_of_irredundant
    v hstrict carrier.labels carrier.card_ge_three carrier.irredundant
  let c := Classical.choose hex
  have hcData := Classical.choose_spec hex
  have hc : Function.Injective c := hcData.1
  have hcRange : Set.range c = (↑carrier.labels : Set (Fin 8)) := hcData.2.1
  have hcyc : StrictCyclicPos c v := hcData.2.2
  let hne : NeZero carrier.labels.card :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3)
      carrier.card_ge_three)⟩
  letI : NeZero carrier.labels.card := hne
  have hcontain : Set.range v ⊆
      convexHull ℝ (Set.range (v ∘ c)) := by
    rintro _ ⟨p, rfl⟩
    apply (convexHull_mono ?_) (carrier.covers p)
    rintro _ ⟨q, hqs, rfl⟩
    have hqRange : q ∈ Set.range c := by
      rw [hcRange]
      exact hqs
    obtain ⟨i, rfl⟩ := hqRange
    exact ⟨i, rfl⟩
  have hfan : FanCovers v c :=
    fanCovers_of_strictCyclicPos_of_convexHull
      v c carrier.card_ge_three hc hcyc hcontain
  exact
    { size := carrier.labels.card
      size_ge_three := carrier.card_ge_three
      size_le_eight := carrier.card_le_eight
      neZero := hne
      cycle := c
      injective := hc
      strictCyclicPos := hcyc
      fanCovers := hfan }

/-- Existential form matching consumers which do not want the bundled
witness. -/
theorem strictHullCycle_exists_of_allTripleSignsStrict
    (v : Fin 8 → ℝ × ℝ) (hstrict : AllTripleSignsStrict v) :
    ∃ (m : ℕ) (hne : NeZero m) (c : Fin m → Fin 8),
      3 ≤ m ∧ m ≤ 8 ∧ Function.Injective c ∧
        StrictCyclicPos c v ∧ @FanCovers m hne v c := by
  let w := strictHullCycleWitness_exists v hstrict
  exact ⟨w.size, w.neZero, w.cycle, w.size_ge_three,
    w.size_le_eight, w.injective, w.strictCyclicPos, w.fanCovers⟩

/-- Positive-minimum form used after a putative strict Heilbronn beat. -/
theorem strictHullCycle_exists_of_minTri_pos
    (v : Fin 8 → ℝ × ℝ) (hmin : 0 < minTri v) :
    ∃ (m : ℕ) (hne : NeZero m) (c : Fin m → Fin 8),
      3 ≤ m ∧ m ≤ 8 ∧ Function.Injective c ∧
        StrictCyclicPos c v ∧ @FanCovers m hne v c :=
  strictHullCycle_exists_of_allTripleSignsStrict v
    (allTripleSignsStrict_of_minTri_pos v hmin)

end Heilbronn8
