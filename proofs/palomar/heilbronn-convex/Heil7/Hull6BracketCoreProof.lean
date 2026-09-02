import Heil7.Hull6SignReduction
import Heil7.Hull6TightChamber
import Heil7.Hull6ConsecutiveOppositeChamber
import Heil7.Hull6TwoNegativeChamber
import Heil7.Hull6OneNegativeChamber

/-!
# Completion of the hull-six bracket core

This file assembles the four scalar chamber theorems through the finite sign
reduction.  The only relabeling operation is cyclic shift of the three arrays

* `a i = b i (i+1)`,
* `d i = b i (i+2)`, and
* `c i = b i (i+3)`.

In particular, the sorted outer-triangle hypothesis is not transported under
a permutation.  It is unpacked once into the six cyclic ear caps, and those
caps are then shifted as array data.  The reflection needed in the
one-negative chamber is similarly confined to its array theorem.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

private def h6ShiftArray (r : Fin 6) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun i => x (r + i)

private lemma h6ShiftArray_sum (r : Fin 6) (a : Fin 6 → ℝ) :
    h6ShiftArray r a 0 + h6ShiftArray r a 1 +
        h6ShiftArray r a 2 + h6ShiftArray r a 3 +
        h6ShiftArray r a 4 + h6ShiftArray r a 5 =
      a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  fin_cases r
  · change a 0 + a 1 + a 2 + a 3 + a 4 + a 5 = _
    ring
  · change a 1 + a 2 + a 3 + a 4 + a 5 + a 0 = _
    ring
  · change a 2 + a 3 + a 4 + a 5 + a 0 + a 1 = _
    ring
  · change a 3 + a 4 + a 5 + a 0 + a 1 + a 2 = _
    ring
  · change a 4 + a 5 + a 0 + a 1 + a 2 + a 3 = _
    ring
  · change a 5 + a 0 + a 1 + a 2 + a 3 + a 4 = _
    ring

private lemma h6ShiftArray_rel
    (r : Fin 6) (a d c : Fin 6 → ℝ)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1)) :
    ∀ i : Fin 6,
      h6ShiftArray r d i * h6ShiftArray r d (i + 1) =
        h6ShiftArray r a i * h6ShiftArray r a (i + 2) +
          h6ShiftArray r c i * h6ShiftArray r a (i + 1) := by
  intro i
  simpa only [h6ShiftArray, add_assoc] using hrel (r + i)

private lemma h6ShiftArray_cap
    (r : Fin 6) (m : ℝ) (a d : Fin 6 → ℝ)
    (hcap : ∀ i : Fin 6, d i ≤ a i + a (i + 1) - m) :
    ∀ i : Fin 6,
      h6ShiftArray r d i ≤
        h6ShiftArray r a i + h6ShiftArray r a (i + 1) - m := by
  intro i
  simpa only [h6ShiftArray, add_assoc] using hcap (r + i)

private lemma h6ShiftArray_opp
    (r : Fin 6) (c : Fin 6 → ℝ)
    (hcopp : ∀ i : Fin 6, c (i + 3) = -c i) :
    ∀ i : Fin 6,
      h6ShiftArray r c (i + 3) = -h6ShiftArray r c i := by
  intro i
  simpa only [h6ShiftArray, add_assoc] using hcopp (r + i)

private theorem h6_tight_shifted_bound
    (m : ℝ) (a d c : Fin 6 → ℝ) (r : Fin 6)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i) (hd : ∀ i, m ≤ d i)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (hc0 : m ≤ c r)
    (hc1 : c (r + 1) ≤ -m)
    (hc2 : m ≤ c (r + 2))
    (hc3 : c (r + 3) ≤ -m)
    (hc4 : m ≤ c (r + 4))
    (hc5 : c (r + 5) ≤ -m) :
    9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  have hb := h6_tight_array_bound m
    (h6ShiftArray r a) (h6ShiftArray r d) (h6ShiftArray r c) hm
    (fun i => ha (r + i)) (fun i => hd (r + i))
    (by simpa [h6ShiftArray] using hc0)
    (by simpa [h6ShiftArray] using hc1)
    (by simpa [h6ShiftArray] using hc2)
    (by simpa [h6ShiftArray] using hc3)
    (by simpa [h6ShiftArray] using hc4)
    (by simpa [h6ShiftArray] using hc5)
    (h6ShiftArray_rel r a d c hrel)
  calc
    9 * m ≤
        h6ShiftArray r a 0 + h6ShiftArray r a 1 +
          h6ShiftArray r a 2 + h6ShiftArray r a 3 +
          h6ShiftArray r a 4 + h6ShiftArray r a 5 := hb
    _ = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := h6ShiftArray_sum r a

private theorem h6_consecutive_shifted_bound
    (m : ℝ) (a d c : Fin 6 → ℝ) (r : Fin 6)
    (hm : 0 < m)
    (ha : ∀ i, m ≤ a i) (hd : ∀ i, m ≤ d i)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (hc3 : c (r + 3) ≤ -m)
    (hc4 : c (r + 4) ≤ -m)
    (hc5 : c (r + 5) ≤ -m) :
    9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  have hb := h6_consecutive_array_bound m
    (h6ShiftArray r a) (h6ShiftArray r d) (h6ShiftArray r c) hm
    (fun i => ha (r + i)) (fun i => hd (r + i))
    (by simpa [h6ShiftArray] using hc3)
    (by simpa [h6ShiftArray] using hc4)
    (by simpa [h6ShiftArray] using hc5)
    (h6ShiftArray_rel r a d c hrel)
  calc
    9 * m ≤
        h6ShiftArray r a 0 + h6ShiftArray r a 1 +
          h6ShiftArray r a 2 + h6ShiftArray r a 3 +
          h6ShiftArray r a 4 + h6ShiftArray r a 5 := hb
    _ = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := h6ShiftArray_sum r a

private theorem h6_two_negative_shifted_bound
    (m : ℝ) (a d c : Fin 6 → ℝ) (r : Fin 6)
    (hm : 0 < m) (ha : ∀ i, m ≤ a i)
    (hcap : ∀ i : Fin 6, d i ≤ a i + a (i + 1) - m)
    (hcopp : ∀ i : Fin 6, c (i + 3) = -c i)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (hd0 : d r ≤ -m) (hd1 : d (r + 1) ≤ -m)
    (hd2 : m ≤ d (r + 2)) (hd3 : m ≤ d (r + 3))
    (hd4 : m ≤ d (r + 4)) (hd5 : m ≤ d (r + 5)) :
    9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  have hcapS := h6ShiftArray_cap r m a d hcap
  have hcoppS := h6ShiftArray_opp r c hcopp
  have hb := h6_two_negative_array_bound m
    (h6ShiftArray r a) (h6ShiftArray r d) (h6ShiftArray r c) hm
    (fun i => ha (r + i))
    (by simpa [h6ShiftArray] using hd0)
    (by simpa [h6ShiftArray] using hd1)
    (by simpa [h6ShiftArray] using hd2)
    (by simpa [h6ShiftArray] using hd3)
    (by simpa [h6ShiftArray] using hd4)
    (by simpa [h6ShiftArray] using hd5)
    (hcapS 2) (hcapS 3) (hcapS 4) (hcapS 5)
    (hcoppS 1) (hcoppS 2)
    (h6ShiftArray_rel r a d c hrel)
  calc
    9 * m ≤
        h6ShiftArray r a 0 + h6ShiftArray r a 1 +
          h6ShiftArray r a 2 + h6ShiftArray r a 3 +
          h6ShiftArray r a 4 + h6ShiftArray r a 5 := hb
    _ = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := h6ShiftArray_sum r a

private theorem h6_one_negative_shifted_bound
    (m : ℝ) (a d c : Fin 6 → ℝ) (r : Fin 6)
    (hm : 0 < m) (ha : ∀ i, m ≤ a i)
    (hcap : ∀ i : Fin 6, d i ≤ a i + a (i + 1) - m)
    (hcopp : ∀ i : Fin 6, c (i + 3) = -c i)
    (hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1))
    (hd0 : d r ≤ -m)
    (hd1 : m ≤ d (r + 1)) (hd2 : m ≤ d (r + 2))
    (hd3 : m ≤ d (r + 3)) (hd4 : m ≤ d (r + 4))
    (hd5 : m ≤ d (r + 5))
    (hc1abs : m ≤ |c (r + 1)|) :
    9 * m ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
  have hcapS := h6ShiftArray_cap r m a d hcap
  have hcoppS := h6ShiftArray_opp r c hcopp
  have hb := h6_one_negative_array_bound_any_c1 m
    (h6ShiftArray r a) (h6ShiftArray r d) (h6ShiftArray r c) hm
    (fun i => ha (r + i))
    (by simpa [h6ShiftArray] using hd0)
    (by simpa [h6ShiftArray] using hd1)
    (by simpa [h6ShiftArray] using hd2)
    (by simpa [h6ShiftArray] using hd3)
    (by simpa [h6ShiftArray] using hd4)
    (by simpa [h6ShiftArray] using hd5)
    (by simpa [h6ShiftArray] using hc1abs)
    (hcapS 1) (hcapS 2) (hcapS 3) (hcapS 4) (hcapS 5)
    (hcoppS 0) (hcoppS 1) (hcoppS 2)
    (h6ShiftArray_rel r a d c hrel)
  calc
    9 * m ≤
        h6ShiftArray r a 0 + h6ShiftArray r a 1 +
          h6ShiftArray r a 2 + h6ShiftArray r a 3 +
          h6ShiftArray r a 4 + h6ShiftArray r a 5 := hb
    _ = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := h6ShiftArray_sum r a

/-- The scalar hull-six bracket core, with every sign chamber discharged. -/
theorem h6_bracket_core_proved : H6BracketCore := by
  unfold H6BracketCore
  intro m b hm hskew hgp hradial hhull hedge
  let a : Fin 6 → ℝ := fun i => b i (i + 1)
  let d : Fin 6 → ℝ := fun i => b i (i + 2)
  let c : Fin 6 → ℝ := fun i => b i (i + 3)
  have ha : ∀ i, m ≤ a i := by
    intro i
    have hp : 0 < a i := by simpa [a] using hedge i
    have hf := hradial i (i + 1) (by fin_cases i <;> decide)
    change m ≤ |a i| at hf
    rwa [abs_of_pos hp] at hf
  have hdPosFloor : ∀ i, 0 < d i → m ≤ d i := by
    intro i hi
    have hf := hradial i (i + 2) (by fin_cases i <;> decide)
    change m ≤ |d i| at hf
    rwa [abs_of_pos hi] at hf
  have hdNegFloor : ∀ i, d i < 0 → d i ≤ -m := by
    intro i hi
    have hf := hradial i (i + 2) (by fin_cases i <;> decide)
    change m ≤ |d i| at hf
    rw [abs_of_neg hi] at hf
    linarith
  have hcPosFloor : ∀ i, 0 < c i → m ≤ c i := by
    intro i hi
    have hf := hradial i (i + 3) (by fin_cases i <;> decide)
    change m ≤ |c i| at hf
    rwa [abs_of_pos hi] at hf
  have hcNegFloor : ∀ i, c i < 0 → c i ≤ -m := by
    intro i hi
    have hf := hradial i (i + 3) (by fin_cases i <;> decide)
    change m ≤ |c i| at hf
    rw [abs_of_neg hi] at hf
    linarith
  have hcAbs : ∀ i, m ≤ |c i| := by
    intro i
    have hf := hradial i (i + 3) (by fin_cases i <;> decide)
    simpa [c] using hf
  have hcap : ∀ i : Fin 6, d i ≤ a i + a (i + 1) - m := by
    intro i
    fin_cases i
    · have ho := hhull 0 1 2 (by decide) (by decide)
      change b 0 2 ≤ b 0 1 + b 1 2 - m
      linarith
    · have ho := hhull 1 2 3 (by decide) (by decide)
      change b 1 3 ≤ b 1 2 + b 2 3 - m
      linarith
    · have ho := hhull 2 3 4 (by decide) (by decide)
      change b 2 4 ≤ b 2 3 + b 3 4 - m
      linarith
    · have ho := hhull 3 4 5 (by decide) (by decide)
      change b 3 5 ≤ b 3 4 + b 4 5 - m
      linarith
    · have ho := hhull 0 4 5 (by decide) (by decide)
      have hs40 := hskew 4 0
      have hs50 := hskew 5 0
      change b 4 0 ≤ b 4 5 + b 5 0 - m
      linarith
    · have ho := hhull 0 1 5 (by decide) (by decide)
      have hs51 := hskew 5 1
      have hs50 := hskew 5 0
      change b 5 1 ≤ b 5 0 + b 0 1 - m
      linarith
  have hcopp : ∀ i : Fin 6, c (i + 3) = -c i := by
    intro i
    fin_cases i
    · change b 3 0 = -b 0 3
      exact hskew 3 0
    · change b 4 1 = -b 1 4
      exact hskew 4 1
    · change b 5 2 = -b 2 5
      exact hskew 5 2
    · change b 0 3 = -b 3 0
      exact hskew 0 3
    · change b 1 4 = -b 4 1
      exact hskew 1 4
    · change b 2 5 = -b 5 2
      exact hskew 2 5
  have hc03 : c 3 = -c 0 := by simpa using hcopp 0
  have hc14 : c 4 = -c 1 := by simpa using hcopp 1
  have hc25 : c 5 = -c 2 := by simpa using hcopp 2
  have hrel : ∀ i : Fin 6,
      d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1) := by
    intro i
    fin_cases i
    · have hp := hgp 0 1 2 3
      change b 0 2 * b 1 3 = b 0 1 * b 2 3 + b 0 3 * b 1 2
      linarith
    · have hp := hgp 1 2 3 4
      change b 1 3 * b 2 4 = b 1 2 * b 3 4 + b 1 4 * b 2 3
      linarith
    · have hp := hgp 2 3 4 5
      change b 2 4 * b 3 5 = b 2 3 * b 4 5 + b 2 5 * b 3 4
      linarith
    · have hp := hgp 3 4 5 0
      change b 3 5 * b 4 0 = b 3 4 * b 5 0 + b 3 0 * b 4 5
      linarith
    · have hp := hgp 4 5 0 1
      change b 4 0 * b 5 1 = b 4 5 * b 0 1 + b 4 1 * b 5 0
      linarith
    · have hp := hgp 5 0 1 2
      change b 5 1 * b 0 2 = b 5 0 * b 1 2 + b 5 2 * b 0 1
      linarith
  refine h6_sign_reduction m b hm hskew hgp hradial hhull hedge ?_ ?_ ?_ ?_
  · intro hdall hcalt
    have hdall' : H6DAllPositive d := by simpa [d] using hdall
    rcases hdall' with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    have hdFloor : ∀ i, m ≤ d i := by
      intro i
      fin_cases i
      · exact hdPosFloor 0 hd0
      · exact hdPosFloor 1 hd1
      · exact hdPosFloor 2 hd2
      · exact hdPosFloor 3 hd3
      · exact hdPosFloor 4 hd4
      · exact hdPosFloor 5 hd5
    have hcalt' : H6CAlternating c := by simpa [c] using hcalt
    rcases hcalt' with hcase | hcase
    · rcases hcase with ⟨hc0, hc1, hc2⟩
      have hb := h6_tight_shifted_bound m a d c 0 hm ha hdFloor hrel
        (hcPosFloor 0 hc0) (hcNegFloor 1 hc1) (hcPosFloor 2 hc2)
        (hcNegFloor 3 (by linarith only [hc03, hc0]))
        (hcPosFloor 4 (by linarith only [hc14, hc1]))
        (hcNegFloor 5 (by linarith only [hc25, hc2]))
      simpa [a] using hb
    · rcases hcase with ⟨hc0, hc1, hc2⟩
      have hb := h6_tight_shifted_bound m a d c 1 hm ha hdFloor hrel
        (by simpa using hcPosFloor 1 hc1)
        (by simpa using hcNegFloor 2 hc2)
        (by simpa using hcPosFloor 3 (by linarith only [hc03, hc0]))
        (by simpa using hcNegFloor 4 (by linarith only [hc14, hc1]))
        (by simpa using hcPosFloor 5 (by linarith only [hc25, hc2]))
        (by simpa using hcNegFloor 0 hc0)
      simpa [a] using hb
  · intro hdall hcblock
    have hdall' : H6DAllPositive d := by simpa [d] using hdall
    rcases hdall' with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
    have hdFloor : ∀ i, m ≤ d i := by
      intro i
      fin_cases i
      · exact hdPosFloor 0 hd0
      · exact hdPosFloor 1 hd1
      · exact hdPosFloor 2 hd2
      · exact hdPosFloor 3 hd3
      · exact hdPosFloor 4 hd4
      · exact hdPosFloor 5 hd5
    have hcblock' : H6CBlock c := by simpa [c] using hcblock
    rcases hcblock' with hcase | hcase | hcase | hcase | hcase | hcase
    · rcases hcase with ⟨hc0, hc1, hc2⟩
      have hb := h6_consecutive_shifted_bound m a d c 0 hm ha hdFloor hrel
        (hcNegFloor 3 (by linarith only [hc03, hc0]))
        (hcNegFloor 4 (by linarith only [hc14, hc1]))
        (hcNegFloor 5 (by linarith only [hc25, hc2]))
      simpa [a] using hb
    · rcases hcase with ⟨hc0, hc1, hc2⟩
      have hb := h6_consecutive_shifted_bound m a d c 5 hm ha hdFloor hrel
        (by simpa using hcNegFloor 2 hc2)
        (by simpa using hcNegFloor 3 (by linarith only [hc03, hc0]))
        (by simpa using hcNegFloor 4 (by linarith only [hc14, hc1]))
      simpa [a] using hb
    · rcases hcase with ⟨hc0, hc1, hc2⟩
      have hb := h6_consecutive_shifted_bound m a d c 4 hm ha hdFloor hrel
        (by simpa using hcNegFloor 1 hc1)
        (by simpa using hcNegFloor 2 hc2)
        (by simpa using hcNegFloor 3 (by linarith only [hc03, hc0]))
      simpa [a] using hb
    · rcases hcase with ⟨hc0, hc1, hc2⟩
      have hb := h6_consecutive_shifted_bound m a d c 3 hm ha hdFloor hrel
        (by simpa using hcNegFloor 0 hc0)
        (by simpa using hcNegFloor 1 hc1)
        (by simpa using hcNegFloor 2 hc2)
      simpa [a] using hb
    · rcases hcase with ⟨hc0, hc1, hc2⟩
      have hb := h6_consecutive_shifted_bound m a d c 2 hm ha hdFloor hrel
        (by simpa using hcNegFloor 5 (by linarith only [hc25, hc2]))
        (by simpa using hcNegFloor 0 hc0)
        (by simpa using hcNegFloor 1 hc1)
      simpa [a] using hb
    · rcases hcase with ⟨hc0, hc1, hc2⟩
      have hb := h6_consecutive_shifted_bound m a d c 1 hm ha hdFloor hrel
        (by simpa using hcNegFloor 4 (by linarith only [hc14, hc1]))
        (by simpa using hcNegFloor 5 (by linarith only [hc25, hc2]))
        (by simpa using hcNegFloor 0 hc0)
      simpa [a] using hb
  · intro hone
    have hone' : H6DOneNegative d := by simpa [d] using hone
    rcases hone' with hcase | hcase | hcase | hcase | hcase | hcase
    · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hb := h6_one_negative_shifted_bound m a d c 0 hm ha hcap hcopp hrel
        (hdNegFloor 0 hd0) (hdPosFloor 1 hd1) (hdPosFloor 2 hd2)
        (hdPosFloor 3 hd3) (hdPosFloor 4 hd4) (hdPosFloor 5 hd5)
        (by simpa using hcAbs 1)
      simpa [a] using hb
    · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hb := h6_one_negative_shifted_bound m a d c 1 hm ha hcap hcopp hrel
        (by simpa using hdNegFloor 1 hd1)
        (by simpa using hdPosFloor 2 hd2)
        (by simpa using hdPosFloor 3 hd3)
        (by simpa using hdPosFloor 4 hd4)
        (by simpa using hdPosFloor 5 hd5)
        (by simpa using hdPosFloor 0 hd0)
        (by simpa using hcAbs 2)
      simpa [a] using hb
    · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hb := h6_one_negative_shifted_bound m a d c 2 hm ha hcap hcopp hrel
        (by simpa using hdNegFloor 2 hd2)
        (by simpa using hdPosFloor 3 hd3)
        (by simpa using hdPosFloor 4 hd4)
        (by simpa using hdPosFloor 5 hd5)
        (by simpa using hdPosFloor 0 hd0)
        (by simpa using hdPosFloor 1 hd1)
        (by simpa using hcAbs 3)
      simpa [a] using hb
    · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hb := h6_one_negative_shifted_bound m a d c 3 hm ha hcap hcopp hrel
        (by simpa using hdNegFloor 3 hd3)
        (by simpa using hdPosFloor 4 hd4)
        (by simpa using hdPosFloor 5 hd5)
        (by simpa using hdPosFloor 0 hd0)
        (by simpa using hdPosFloor 1 hd1)
        (by simpa using hdPosFloor 2 hd2)
        (by simpa using hcAbs 4)
      simpa [a] using hb
    · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hb := h6_one_negative_shifted_bound m a d c 4 hm ha hcap hcopp hrel
        (by simpa using hdNegFloor 4 hd4)
        (by simpa using hdPosFloor 5 hd5)
        (by simpa using hdPosFloor 0 hd0)
        (by simpa using hdPosFloor 1 hd1)
        (by simpa using hdPosFloor 2 hd2)
        (by simpa using hdPosFloor 3 hd3)
        (by simpa using hcAbs 5)
      simpa [a] using hb
    · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hb := h6_one_negative_shifted_bound m a d c 5 hm ha hcap hcopp hrel
        (by simpa using hdNegFloor 5 hd5)
        (by simpa using hdPosFloor 0 hd0)
        (by simpa using hdPosFloor 1 hd1)
        (by simpa using hdPosFloor 2 hd2)
        (by simpa using hdPosFloor 3 hd3)
        (by simpa using hdPosFloor 4 hd4)
        (by simpa using hcAbs 0)
      simpa [a] using hb
  · intro htwo
    have htwo' : H6DTwoConsecutiveNegative d := by simpa [d] using htwo
    rcases htwo' with hcase | hcase | hcase | hcase | hcase | hcase
    · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hb := h6_two_negative_shifted_bound m a d c 0 hm ha hcap hcopp hrel
        (hdNegFloor 0 hd0) (hdNegFloor 1 hd1)
        (hdPosFloor 2 hd2) (hdPosFloor 3 hd3)
        (hdPosFloor 4 hd4) (hdPosFloor 5 hd5)
      simpa [a] using hb
    · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hb := h6_two_negative_shifted_bound m a d c 1 hm ha hcap hcopp hrel
        (by simpa using hdNegFloor 1 hd1)
        (by simpa using hdNegFloor 2 hd2)
        (by simpa using hdPosFloor 3 hd3)
        (by simpa using hdPosFloor 4 hd4)
        (by simpa using hdPosFloor 5 hd5)
        (by simpa using hdPosFloor 0 hd0)
      simpa [a] using hb
    · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hb := h6_two_negative_shifted_bound m a d c 2 hm ha hcap hcopp hrel
        (by simpa using hdNegFloor 2 hd2)
        (by simpa using hdNegFloor 3 hd3)
        (by simpa using hdPosFloor 4 hd4)
        (by simpa using hdPosFloor 5 hd5)
        (by simpa using hdPosFloor 0 hd0)
        (by simpa using hdPosFloor 1 hd1)
      simpa [a] using hb
    · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hb := h6_two_negative_shifted_bound m a d c 3 hm ha hcap hcopp hrel
        (by simpa using hdNegFloor 3 hd3)
        (by simpa using hdNegFloor 4 hd4)
        (by simpa using hdPosFloor 5 hd5)
        (by simpa using hdPosFloor 0 hd0)
        (by simpa using hdPosFloor 1 hd1)
        (by simpa using hdPosFloor 2 hd2)
      simpa [a] using hb
    · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hb := h6_two_negative_shifted_bound m a d c 4 hm ha hcap hcopp hrel
        (by simpa using hdNegFloor 4 hd4)
        (by simpa using hdNegFloor 5 hd5)
        (by simpa using hdPosFloor 0 hd0)
        (by simpa using hdPosFloor 1 hd1)
        (by simpa using hdPosFloor 2 hd2)
        (by simpa using hdPosFloor 3 hd3)
      simpa [a] using hb
    · rcases hcase with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
      have hb := h6_two_negative_shifted_bound m a d c 5 hm ha hcap hcopp hrel
        (by simpa using hdNegFloor 5 hd5)
        (by simpa using hdNegFloor 0 hd0)
        (by simpa using hdPosFloor 1 hd1)
        (by simpa using hdPosFloor 2 hd2)
        (by simpa using hdPosFloor 3 hd3)
        (by simpa using hdPosFloor 4 hd4)
      simpa [a] using hb

/-- The geometric hull-six field obtained from the proved bracket core. -/
theorem hullSix_bound_proved :
    ∀ (v : Configuration7), HullCCW v 6 →
      (∀ p : Fin 7, 6 ≤ (p : ℕ) → InHullN v 6 p) →
      9 * minTri v ≤ fanArea v 6 :=
  hullSix_of_bracketCore h6_bracket_core_proved

end HeilbronnChallenge.N7Upper
