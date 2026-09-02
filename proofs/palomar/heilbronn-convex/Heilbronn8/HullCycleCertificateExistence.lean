import Heilbronn8.HullCycleExistence
import Heilbronn8.HullCycleGeometric

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-!
# Existence of a canonical hull-cycle certificate

The geometric hull witness is packaged as a literal list and then passed
through `HullCycleOf.ofGeometric`.  This is the final bridge between the
certificate-free convex-hull construction and the strict sign interface used
by the survivor checker.
-/

/-- Every configuration in strict general position has a canonical strict
sign certificate for some hull cycle. -/
theorem exists_hullCycleOf_ofAllTripleSignsStrict
    (v : Configuration) (hstrict : AllTripleSignsStrict v) :
    ∃ d : HullCycleData,
      HullCycleOf (StrictSignData.ofAllTripleSignsStrict v hstrict) d := by
  classical
  let w := strictHullCycleWitness_exists v hstrict
  let d : HullCycleData :=
    { cycle := List.ofFn w.cycle
      length_ge_three := by
        simpa using w.size_ge_three
      length_le_eight := by
        simpa using w.size_le_eight }
  have hlen : d.cycle.length = w.size := by
    simp [d]
  have hcastGet : d.castGet hlen = w.cycle := by
    funext i
    simp [d, HullCycleData.castGet, HullCycleData.get]
  have hget (i : Fin d.cycle.length) :
      d.get i = w.cycle (Fin.cast hlen i) := by
    simpa [HullCycleData.castGet] using
      congrFun hcastGet (Fin.cast hlen i)
  have hdInjective : Function.Injective d.get := by
    intro i j hij
    rw [hget i, hget j] at hij
    exact (Fin.cast_injective hlen) (w.injective hij)
  have hcyc : StrictCyclicPos d.get v := by
    constructor
    · intro i j k hij hjk
      have hw := w.strictCyclicPos.1
        (Fin.cast hlen i) (Fin.cast hlen j) (Fin.cast hlen k)
        ((Fin.cast_lt_cast hlen).2 hij)
        ((Fin.cast_lt_cast hlen).2 hjk)
      rwa [← hget i, ← hget j, ← hget k] at hw
    · intro i j k hij hjk
      have hw := w.strictCyclicPos.2
        (Fin.cast hlen i) (Fin.cast hlen j) (Fin.cast hlen k)
        ((Fin.cast_lt_cast hlen).2 hij)
        ((Fin.cast_lt_cast hlen).2 hjk)
      rwa [← hget i, ← hget j, ← hget k] at hw
  letI : NeZero d.cycle.length :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3)
      d.length_ge_three)⟩
  letI : NeZero w.size := w.neZero
  have hzero : Fin.cast hlen (0 : Fin d.cycle.length) = (0 : Fin w.size) := by
    apply Fin.ext
    rfl
  have hfan : FanCovers v d.get := by
    intro p hpOutside
    have hpWitness : p ∉ Set.range w.cycle := by
      rintro ⟨i, rfl⟩
      apply hpOutside
      refine ⟨Fin.cast hlen.symm i, ?_⟩
      simpa using hget (Fin.cast hlen.symm i)
    obtain ⟨i, j, hi, hij, hp⟩ := w.fanCovers p hpWitness
    refine ⟨Fin.cast hlen.symm i, Fin.cast hlen.symm j, ?_, ?_, ?_⟩
    · exact (Fin.cast_lt_cast hlen.symm).2 hi
    · exact (Fin.cast_lt_cast hlen.symm).2 hij
    · simpa [hget, hzero] using hp
  exact ⟨d, HullCycleOf.ofGeometric hstrict d hdInjective hcyc hfan⟩

/-- Positive minimum triangle area supplies the same hull-cycle certificate
through the strict-sign dispatcher. -/
theorem exists_hullCycleOf_of_minTri_pos
    (v : Configuration) (hmin : 0 < minTri v) :
    ∃ d : HullCycleData,
      HullCycleOf
        (StrictSignData.ofAllTripleSignsStrict v
          (allTripleSignsStrict_of_minTri_pos v hmin)) d :=
  exists_hullCycleOf_ofAllTripleSignsStrict v
    (allTripleSignsStrict_of_minTri_pos v hmin)

#print axioms exists_hullCycleOf_ofAllTripleSignsStrict
#print axioms exists_hullCycleOf_of_minTri_pos

end Heilbronn8
