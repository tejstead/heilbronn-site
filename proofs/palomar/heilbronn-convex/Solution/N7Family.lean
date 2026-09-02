/-
An explicit infinite family for the convex Heilbronn problem at n = 7.

This is source-only scaffolding for later integration into the Palomar package.
It deliberately imports that package's definitions instead of introducing a
second notion of `minTri` or affine equivalence.

Provenance: Yang and Zeng (1995) prove the sharp global bound 1/9, but do not
state this family or an optimizer classification.  The family below is the
rational-coordinate form of the exact family independently derived in
`heilbronn-site/build/families.py`.  Thus the coordinate and inequivalence
arguments here are new elementary derivations, not claims from that paper.
-/
import Solution.AffineDefs
import Solution.N7

set_option linter.style.header false

namespace HeilbronnChallenge

open MeasureTheory

/-- The unit-own-hull-area family.  At `t = 1` this is exactly `cfg7`.

Before applying the diagonal area normalization, the two nonzero orbits are
```
(-2,-2), (2,0), (0,2)
(-t,-2t), (2t,t), (-t,t),
```
under `(x,y) |-> (-y,x-y)`.  Their unnormalized hexagon has area `9*t`.
The displayed coordinates apply `(x,y) |-> (x/(3*t),y/3)`, so the hull has
area one whenever `t > 0`. -/
noncomputable def cfg7Family (t : ℝ) : Fin 7 → ℝ × ℝ :=
  ![(-((2 : ℝ) / 3) * (1 / t), -2 / 3), (-1 / 3, -(2 * t) / 3),
    (((2 : ℝ) / 3) * (1 / t), 0), (2 / 3, t / 3), (0, 2 / 3),
    (-1 / 3, t / 3), (0, 0)]

/-- The six hull vertices of `cfg7Family`, in counter-clockwise order. -/
noncomputable def hex7Family (t : ℝ) : Fin 6 → ℝ × ℝ :=
  ![(-((2 : ℝ) / 3) * (1 / t), -2 / 3), (-1 / 3, -(2 * t) / 3),
    (((2 : ℝ) / 3) * (1 / t), 0), (2 / 3, t / 3), (0, 2 / 3),
    (-1 / 3, t / 3)]

@[simp] lemma cfg7Family_zero (t : ℝ) :
    cfg7Family t 0 = (-((2 : ℝ) / 3) * (1 / t), -2 / 3) := rfl
@[simp] lemma cfg7Family_one (t : ℝ) :
    cfg7Family t 1 = (-1 / 3, -(2 * t) / 3) := rfl
@[simp] lemma cfg7Family_two (t : ℝ) :
    cfg7Family t 2 = (((2 : ℝ) / 3) * (1 / t), 0) := rfl
@[simp] lemma cfg7Family_three (t : ℝ) :
    cfg7Family t 3 = (2 / 3, t / 3) := rfl
@[simp] lemma cfg7Family_four (t : ℝ) :
    cfg7Family t 4 = (0, 2 / 3) := rfl
@[simp] lemma cfg7Family_five (t : ℝ) :
    cfg7Family t 5 = (-1 / 3, t / 3) := rfl
@[simp] lemma cfg7Family_six (t : ℝ) : cfg7Family t 6 = (0, 0) := rfl

@[simp] lemma hex7Family_zero (t : ℝ) :
    hex7Family t 0 = (-((2 : ℝ) / 3) * (1 / t), -2 / 3) := rfl
@[simp] lemma hex7Family_one (t : ℝ) :
    hex7Family t 1 = (-1 / 3, -(2 * t) / 3) := rfl
@[simp] lemma hex7Family_two (t : ℝ) :
    hex7Family t 2 = (((2 : ℝ) / 3) * (1 / t), 0) := rfl
@[simp] lemma hex7Family_three (t : ℝ) :
    hex7Family t 3 = (2 / 3, t / 3) := rfl
@[simp] lemma hex7Family_four (t : ℝ) :
    hex7Family t 4 = (0, 2 / 3) := rfl
@[simp] lemma hex7Family_five (t : ℝ) :
    hex7Family t 5 = (-1 / 3, t / 3) := rfl

theorem cfg7Family_one_eq : cfg7Family 1 = cfg7 := by
  funext i
  rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [cfg7] <;> norm_num

/-! ## Exact coordinate spectrum -/

/-- All thirty-five signed doubled triangle areas.  The only hypothesis is
needed to clear the coordinate denominator. -/
theorem cfg7Family_sigs (t : ℝ) (ht : t ≠ 0) :
    sig (cfg7Family t 0) (cfg7Family t 1) (cfg7Family t 2) =
        2 * (3 * t - 2) / (9 * t) ∧
    sig (cfg7Family t 0) (cfg7Family t 1) (cfg7Family t 3) = t / 3 ∧
    sig (cfg7Family t 0) (cfg7Family t 1) (cfg7Family t 4) = 4 / (9 * t) ∧
    sig (cfg7Family t 0) (cfg7Family t 1) (cfg7Family t 5) = -(t - 2) / 3 ∧
    sig (cfg7Family t 0) (cfg7Family t 1) (cfg7Family t 6) = 2 / 9 ∧
    sig (cfg7Family t 0) (cfg7Family t 2) (cfg7Family t 3) = 4 / (9 * t) ∧
    sig (cfg7Family t 0) (cfg7Family t 2) (cfg7Family t 4) = 4 / (3 * t) ∧
    sig (cfg7Family t 0) (cfg7Family t 2) (cfg7Family t 5) =
        2 * (3 * t + 2) / (9 * t) ∧
    sig (cfg7Family t 0) (cfg7Family t 2) (cfg7Family t 6) = 4 / (9 * t) ∧
    sig (cfg7Family t 0) (cfg7Family t 3) (cfg7Family t 4) =
        2 * (3 * t + 2) / (9 * t) ∧
    sig (cfg7Family t 0) (cfg7Family t 3) (cfg7Family t 5) = (t + 2) / 3 ∧
    sig (cfg7Family t 0) (cfg7Family t 3) (cfg7Family t 6) = 2 / 9 ∧
    sig (cfg7Family t 0) (cfg7Family t 4) (cfg7Family t 5) =
        2 * (3 * t - 2) / (9 * t) ∧
    sig (cfg7Family t 0) (cfg7Family t 4) (cfg7Family t 6) = -4 / (9 * t) ∧
    sig (cfg7Family t 0) (cfg7Family t 5) (cfg7Family t 6) = -4 / 9 ∧
    sig (cfg7Family t 1) (cfg7Family t 2) (cfg7Family t 3) = -(t - 2) / 3 ∧
    sig (cfg7Family t 1) (cfg7Family t 2) (cfg7Family t 4) =
        2 * (3 * t + 2) / (9 * t) ∧
    sig (cfg7Family t 1) (cfg7Family t 2) (cfg7Family t 5) = (t + 2) / 3 ∧
    sig (cfg7Family t 1) (cfg7Family t 2) (cfg7Family t 6) = 4 / 9 ∧
    sig (cfg7Family t 1) (cfg7Family t 3) (cfg7Family t 4) = (t + 2) / 3 ∧
    sig (cfg7Family t 1) (cfg7Family t 3) (cfg7Family t 5) = t ∧
    sig (cfg7Family t 1) (cfg7Family t 3) (cfg7Family t 6) = t / 3 ∧
    sig (cfg7Family t 1) (cfg7Family t 4) (cfg7Family t 5) = t / 3 ∧
    sig (cfg7Family t 1) (cfg7Family t 4) (cfg7Family t 6) = -2 / 9 ∧
    sig (cfg7Family t 1) (cfg7Family t 5) (cfg7Family t 6) = -t / 3 ∧
    sig (cfg7Family t 2) (cfg7Family t 3) (cfg7Family t 4) =
        2 * (3 * t - 2) / (9 * t) ∧
    sig (cfg7Family t 2) (cfg7Family t 3) (cfg7Family t 5) = t / 3 ∧
    sig (cfg7Family t 2) (cfg7Family t 3) (cfg7Family t 6) = 2 / 9 ∧
    sig (cfg7Family t 2) (cfg7Family t 4) (cfg7Family t 5) = 4 / (9 * t) ∧
    sig (cfg7Family t 2) (cfg7Family t 4) (cfg7Family t 6) = 4 / (9 * t) ∧
    sig (cfg7Family t 2) (cfg7Family t 5) (cfg7Family t 6) = 2 / 9 ∧
    sig (cfg7Family t 3) (cfg7Family t 4) (cfg7Family t 5) = -(t - 2) / 3 ∧
    sig (cfg7Family t 3) (cfg7Family t 4) (cfg7Family t 6) = 4 / 9 ∧
    sig (cfg7Family t 3) (cfg7Family t 5) (cfg7Family t 6) = t / 3 ∧
    sig (cfg7Family t 4) (cfg7Family t 5) (cfg7Family t 6) = 2 / 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sig, cfg7Family_zero, cfg7Family_one, cfg7Family_two,
      cfg7Family_three, cfg7Family_four, cfg7Family_five, cfg7Family_six] <;>
    field_simp [ht] <;> ring

/-! ## A finite maximum, used only as an affine invariant -/

/-- Maximum doubled triangle area over the same thirty-five triples as
`minTri`. -/
noncomputable def maxTri7 (v : Fin 7 → ℝ × ℝ) : ℝ :=
  (triples 7).sup' Fact.out fun q ↦
    |sig (v q.1) (v q.2.1) (v q.2.2)|

lemma le_maxTri7 (v : Fin 7 → ℝ × ℝ) (i j k : Fin 7)
    (hij : i < j) (hjk : j < k) :
    |sig (v i) (v j) (v k)| ≤ maxTri7 v := by
  unfold maxTri7
  exact Finset.le_sup'
    (fun q : Fin 7 × Fin 7 × Fin 7 ↦
      |sig (v q.1) (v q.2.1) (v q.2.2)|)
    (mem_triples hij hjk)

lemma maxTri7_le (v : Fin 7 → ℝ × ℝ) (r : ℝ)
    (h : ∀ q ∈ triples 7, |sig (v q.1) (v q.2.1) (v q.2.2)| ≤ r) :
    maxTri7 v ≤ r := by
  exact Finset.sup'_le Fact.out _ h

/-! The remaining integration lemmas are intentionally stated below in their
final API shape.  Their proofs are filled in incrementally without changing
the public statements. -/

/-- Every member of the full parameter interval has optimal doubled minimum
triangle area. -/
theorem minTri_cfg7Family (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 4 / 3) :
    minTri (cfg7Family t) = 2 / 9 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have htu : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0.ne'
  have hu0 : 0 ≤ 1 / t := one_div_nonneg.mpr ht0.le
  have huLo : (3 : ℝ) / 4 ≤ 1 / t :=
    (le_div_iff₀ ht0).2 (by nlinarith [ht.2])
  have huHi : 1 / t ≤ 1 :=
    (div_le_iff₀ ht0).2 (by nlinarith [ht.1])
  apply le_antisymm
  · have h := minTri_le (cfg7Family t) 0 1 6 (by decide) (by decide)
    have hs :
        sig (cfg7Family t 0) (cfg7Family t 1) (cfg7Family t 6) = 2 / 9 := by
      simp only [sig, cfg7Family_zero, cfg7Family_one, cfg7Family_six]
      ring_nf
      nlinarith [htu]
    rwa [hs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 9)] at h
  · apply le_minTri
    intro q hq
    have hmem : q.1 < q.2.1 ∧ q.2.1 < q.2.2 := by
      simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    rcases triple_cases7 q.1 q.2.1 q.2.2 hmem.1 hmem.2 with
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ <;>
    · rw [q0, q1, q2]
      simp only [sig, cfg7Family_zero, cfg7Family_one, cfg7Family_two,
        cfg7Family_three, cfg7Family_four, cfg7Family_five, cfg7Family_six]
      rw [le_abs]
      first
      | left; ring_nf; nlinarith [htu]
      | right; ring_nf; nlinarith [htu]

set_option maxHeartbeats 800000

/-- On this rational subinterval, the largest doubled triangle area is the
parameter itself. -/
theorem maxTri7_cfg7Family (t : ℝ) (ht : 6 / 5 ≤ t ∧ t ≤ 5 / 4) :
    maxTri7 (cfg7Family t) = t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have htu : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0.ne'
  have hu0 : 0 ≤ 1 / t := one_div_nonneg.mpr ht0.le
  have huHi : 1 / t ≤ (5 : ℝ) / 6 :=
    (div_le_iff₀ ht0).2 (by nlinarith [ht.1])
  apply le_antisymm
  · apply maxTri7_le
    intro q hq
    have hmem : q.1 < q.2.1 ∧ q.2.1 < q.2.2 := by
      simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    rcases triple_cases7 q.1 q.2.1 q.2.2 hmem.1 hmem.2 with
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ |
      ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ <;>
    · rw [q0, q1, q2]
      simp only [sig, cfg7Family_zero, cfg7Family_one, cfg7Family_two,
        cfg7Family_three, cfg7Family_four, cfg7Family_five, cfg7Family_six]
      rw [abs_le]
      constructor <;> ring_nf <;> nlinarith [htu]
  · have h := le_maxTri7 (cfg7Family t) 1 3 5 (by decide) (by decide)
    have hs :
        sig (cfg7Family t 1) (cfg7Family t 3) (cfg7Family t 5) = t := by
      simp only [sig, cfg7Family_one, cfg7Family_three, cfg7Family_five]
      ring
    rwa [hs, abs_of_nonneg ht0.le] at h

set_option maxHeartbeats 200000

/-! ## Hull normalization -/

theorem hex7Family_strict (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 4 / 3) :
    ∀ i j k : Fin 6, i < j → j < k →
      0 < sig (hex7Family t i) (hex7Family t j) (hex7Family t k) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have h9t : 0 < (9 : ℝ) * t := by positivity
  have h3t : 0 < (3 : ℝ) * t := by positivity
  have hA : 0 < (6 * t - 4) / (9 * t) := div_pos (by nlinarith [ht.1]) h9t
  have hB : 0 < t / 3 := div_pos ht0 (by norm_num)
  have hC : 0 < (4 : ℝ) / (9 * t) := div_pos (by norm_num) h9t
  have hD : 0 < (2 - t) / 3 := div_pos (by nlinarith [ht.2]) (by norm_num)
  have hE : 0 < (4 : ℝ) / (3 * t) := div_pos (by norm_num) h3t
  have hF : 0 < (6 * t + 4) / (9 * t) := div_pos (by nlinarith) h9t
  have hG : 0 < (t + 2) / 3 := div_pos (by nlinarith) (by norm_num)
  intro i j k hij hjk
  rcases triple_cases6 i j k hij hjk with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals simp only [sig, hex7Family_zero, hex7Family_one,
    hex7Family_two, hex7Family_three, hex7Family_four, hex7Family_five]
  · convert hA using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hB using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hC using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hD using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hC using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hE using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hF using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hF using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hG using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hA using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hD using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hF using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hG using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hG using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert ht0 using 1 <;> ring
  · convert hB using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hA using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hB using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hC using 1 <;> field_simp [ht0.ne'] <;> ring
  · convert hD using 1 <;> field_simp [ht0.ne'] <;> ring

theorem volume_convexHull_hex7Family (t : ℝ)
    (ht : 1 ≤ t ∧ t ≤ 4 / 3) :
    volume (convexHull ℝ (Set.range (hex7Family t))) = 1 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have hfan :
      (HullBridge.sig (hex7Family t 0) (hex7Family t 1) (hex7Family t 2) +
       HullBridge.sig (hex7Family t 0) (hex7Family t 2) (hex7Family t 3) +
       HullBridge.sig (hex7Family t 0) (hex7Family t 3) (hex7Family t 4) +
       HullBridge.sig (hex7Family t 0) (hex7Family t 4) (hex7Family t 5)) / 2 =
        (1 : ℝ) := by
    simp only [HullBridge.sig, hex7Family_zero, hex7Family_one,
      hex7Family_two, hex7Family_three, hex7Family_four, hex7Family_five]
    field_simp [ht0.ne'] <;> ring
  calc
    volume (convexHull ℝ (Set.range (hex7Family t))) =
        ENNReal.ofReal
          ((HullBridge.sig (hex7Family t 0) (hex7Family t 1) (hex7Family t 2) +
            HullBridge.sig (hex7Family t 0) (hex7Family t 2) (hex7Family t 3) +
            HullBridge.sig (hex7Family t 0) (hex7Family t 3) (hex7Family t 4) +
            HullBridge.sig (hex7Family t 0) (hex7Family t 4) (hex7Family t 5)) / 2) :=
      HullBridge.volume_convexHull_strictCCW6 (hex7Family t)
        (hex7Family_strict t ht)
    _ = 1 := by rw [hfan]; norm_num

theorem interior_mem7Family (t : ℝ) :
    ((0 : ℝ), (0 : ℝ)) ∈ convexHull ℝ (Set.range (hex7Family t)) := by
  have hconv := convex_convexHull ℝ (Set.range (hex7Family t))
  have h0 : hex7Family t 0 ∈ convexHull ℝ (Set.range (hex7Family t)) :=
    subset_convexHull ℝ _ ⟨0, rfl⟩
  have h2 : hex7Family t 2 ∈ convexHull ℝ (Set.range (hex7Family t)) :=
    subset_convexHull ℝ _ ⟨2, rfl⟩
  have h4 : hex7Family t 4 ∈ convexHull ℝ (Set.range (hex7Family t)) :=
    subset_convexHull ℝ _ ⟨4, rfl⟩
  have hm := hconv h0 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  have hf := hconv hm h4 (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (2 : ℝ) / 3 + 1 / 3 = 1)
  have hval :
      ((2 : ℝ) / 3) • (((1 : ℝ) / 2) • hex7Family t 0 +
        ((1 : ℝ) / 2) • hex7Family t 2) +
        ((1 : ℝ) / 3) • hex7Family t 4 = ((0 : ℝ), (0 : ℝ)) := by
    apply Prod.ext <;>
      simp only [hex7Family_zero, hex7Family_two, hex7Family_four,
        Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] <;>
      ring
  rwa [hval] at hf

theorem range_cfg7Family (t : ℝ) :
    Set.range (cfg7Family t) =
      insert ((0 : ℝ), (0 : ℝ)) (Set.range (hex7Family t)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨i, rfl⟩
    rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Set.mem_insert_of_mem _ ⟨0, rfl⟩
    · exact Set.mem_insert_of_mem _ ⟨1, rfl⟩
    · exact Set.mem_insert_of_mem _ ⟨2, rfl⟩
    · exact Set.mem_insert_of_mem _ ⟨3, rfl⟩
    · exact Set.mem_insert_of_mem _ ⟨4, rfl⟩
    · exact Set.mem_insert_of_mem _ ⟨5, rfl⟩
    · exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_range] at hx
    rcases hx with rfl | ⟨j, rfl⟩
    · exact ⟨6, rfl⟩
    · rcases fin6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩

theorem hull_eq7Family (t : ℝ) :
    convexHull ℝ (Set.range (cfg7Family t)) =
      convexHull ℝ (Set.range (hex7Family t)) := by
  rw [range_cfg7Family]
  apply Set.Subset.antisymm
  · exact convexHull_min
      (Set.insert_subset_iff.mpr
        ⟨interior_mem7Family t, subset_convexHull ℝ _⟩)
      (convex_convexHull ℝ _)
  · exact convexHull_mono (Set.subset_insert _ _)

theorem volume_convexHull_cfg7Family (t : ℝ)
    (ht : 1 ≤ t ∧ t ≤ 4 / 3) :
    volume (convexHull ℝ (Set.range (cfg7Family t))) = 1 := by
  rw [hull_eq7Family, volume_convexHull_hex7Family t ht]

/-! ## Affine and relabeling invariants -/

theorem sig_nonsingularAffine (T : NonsingularAffine) (p q r : ℝ × ℝ) :
    sig (T.map p) (T.map q) (T.map r) = T.det * sig p q r := by
  simp only [sig, NonsingularAffine.map, NonsingularAffine.det]
  ring

lemma abs_sig_nonsingularAffine (T : NonsingularAffine) (p q r : ℝ × ℝ) :
    |sig (T.map p) (T.map q) (T.map r)| = |T.det| * |sig p q r| := by
  rw [sig_nonsingularAffine, abs_mul]

def PosAffine.det (T : PosAffine) : ℝ := T.a * T.d - T.b * T.c

lemma PosAffine.det_pos' (T : PosAffine) : 0 < T.det := T.det_pos

theorem sig_posAffine (T : PosAffine) (p q r : ℝ × ℝ) :
    sig (T.map p) (T.map q) (T.map r) = T.det * sig p q r := by
  simp only [sig, PosAffine.map, PosAffine.det]
  ring

lemma abs_sig_posAffine (T : PosAffine) (p q r : ℝ × ℝ) :
    |sig (T.map p) (T.map q) (T.map r)| = T.det * |sig p q r| := by
  rw [sig_posAffine, abs_mul, abs_of_pos T.det_pos']

private lemma minTri7_le_perm (v : Fin 7 → ℝ × ℝ)
    (s : Equiv.Perm (Fin 7)) : minTri v ≤ minTri (v ∘ s) := by
  apply le_minTri
  intro q hq
  have ho : q.1 < q.2.1 ∧ q.2.1 < q.2.2 := by
    simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using hq
  exact minTri_le_of_distinct v (s q.1) (s q.2.1) (s q.2.2)
    (s.injective.ne (ne_of_lt ho.1))
    (s.injective.ne (ne_of_lt (ho.1.trans ho.2)))
    (s.injective.ne (ne_of_lt ho.2))

theorem minTri7_perm (v : Fin 7 → ℝ × ℝ) (s : Equiv.Perm (Fin 7)) :
    minTri (v ∘ s) = minTri v := by
  apply le_antisymm
  · have h := minTri7_le_perm (v ∘ s) s.symm
    have heq : (v ∘ s) ∘ s.symm = v := by
      funext i
      change v (s (s.symm i)) = v i
      rw [s.apply_symm_apply]
    rwa [heq] at h
  · exact minTri7_le_perm v s

private lemma abs_sig_le_maxTri7_of_distinct (v : Fin 7 → ℝ × ℝ)
    (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    |sig (v i) (v j) (v k)| ≤ maxTri7 v := by
  rcases lt_trichotomy i j with hij' | he | hij'
  · rcases lt_trichotomy j k with hjk' | he | hjk'
    · exact le_maxTri7 v i j k hij' hjk'
    · exact absurd he hjk
    · rcases lt_trichotomy i k with hik' | he | hik'
      · calc
          |sig (v i) (v j) (v k)| = |sig (v i) (v k) (v j)| :=
            (abs_sig_swap (v i) (v j) (v k)).symm
          _ ≤ maxTri7 v := le_maxTri7 v i k j hik' hjk'
      · exact absurd he hik
      · calc
          |sig (v i) (v j) (v k)| = |sig (v k) (v i) (v j)| :=
            abs_sig_rotate (v k) (v i) (v j)
          _ ≤ maxTri7 v := le_maxTri7 v k i j hik' hij'
  · exact absurd he hij
  · rcases lt_trichotomy i k with hik' | he | hik'
    · calc
        |sig (v i) (v j) (v k)| = |sig (v j) (v i) (v k)| :=
          (abs_sig_swap12 (v i) (v j) (v k)).symm
        _ ≤ maxTri7 v := le_maxTri7 v j i k hij' hik'
    · exact absurd he hik
    · rcases lt_trichotomy j k with hjk' | he | hjk'
      · calc
          |sig (v i) (v j) (v k)| = |sig (v j) (v k) (v i)| :=
            (abs_sig_rotate (v i) (v j) (v k)).symm
          _ ≤ maxTri7 v := le_maxTri7 v j k i hjk' hik'
      · exact absurd he hjk
      · calc
          |sig (v i) (v j) (v k)| = |sig (v k) (v j) (v i)| :=
            (abs_sig_reverse (v i) (v j) (v k)).symm
          _ ≤ maxTri7 v := le_maxTri7 v k j i hjk' hij'

private lemma maxTri7_perm_le (v : Fin 7 → ℝ × ℝ)
    (s : Equiv.Perm (Fin 7)) : maxTri7 (v ∘ s) ≤ maxTri7 v := by
  apply maxTri7_le
  intro q hq
  have ho : q.1 < q.2.1 ∧ q.2.1 < q.2.2 := by
    simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using hq
  exact abs_sig_le_maxTri7_of_distinct v (s q.1) (s q.2.1) (s q.2.2)
    (s.injective.ne (ne_of_lt ho.1))
    (s.injective.ne (ne_of_lt (ho.1.trans ho.2)))
    (s.injective.ne (ne_of_lt ho.2))

theorem maxTri7_perm (v : Fin 7 → ℝ × ℝ) (s : Equiv.Perm (Fin 7)) :
    maxTri7 (v ∘ s) = maxTri7 v := by
  apply le_antisymm
  · exact maxTri7_perm_le v s
  · have h := maxTri7_perm_le (v ∘ s) s.symm
    have heq : (v ∘ s) ∘ s.symm = v := by
      funext i
      change v (s (s.symm i)) = v i
      rw [s.apply_symm_apply]
    rwa [heq] at h

theorem minTri7_posAffine (v : Fin 7 → ℝ × ℝ) (T : PosAffine) :
    minTri (fun i ↦ T.map (v i)) = T.det * minTri v := by
  apply le_antisymm
  · obtain ⟨q, hq, hmin⟩ :=
      Finset.exists_mem_eq_inf'
        (show (triples 7).Nonempty from Fact.out)
        (fun q : Fin 7 × Fin 7 × Fin 7 ↦
          |sig (v q.1) (v q.2.1) (v q.2.2)|)
    have hmin' : minTri v = |sig (v q.1) (v q.2.1) (v q.2.2)| := by
      simpa only [minTri] using hmin
    calc
      minTri (fun i ↦ T.map (v i)) ≤
          |sig (T.map (v q.1)) (T.map (v q.2.1)) (T.map (v q.2.2))| := by
        unfold minTri
        exact Finset.inf'_le _ hq
      _ = T.det * |sig (v q.1) (v q.2.1) (v q.2.2)| :=
        abs_sig_posAffine T _ _ _
      _ = T.det * minTri v := by rw [← hmin']
  · apply le_minTri
    intro q hq
    rw [abs_sig_posAffine]
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ hq) T.det_pos'.le

theorem maxTri7_posAffine (v : Fin 7 → ℝ × ℝ) (T : PosAffine) :
    maxTri7 (fun i ↦ T.map (v i)) = T.det * maxTri7 v := by
  apply le_antisymm
  · apply maxTri7_le
    intro q hq
    rw [abs_sig_posAffine]
    exact mul_le_mul_of_nonneg_left
      (Finset.le_sup'
        (fun q : Fin 7 × Fin 7 × Fin 7 ↦
          |sig (v q.1) (v q.2.1) (v q.2.2)|) hq)
      T.det_pos'.le
  · obtain ⟨q, hq, hmax⟩ :=
      Finset.exists_mem_eq_sup'
        (show (triples 7).Nonempty from Fact.out)
        (fun q : Fin 7 × Fin 7 × Fin 7 ↦
          |sig (v q.1) (v q.2.1) (v q.2.2)|)
    have hmax' : maxTri7 v = |sig (v q.1) (v q.2.1) (v q.2.2)| := by
      simpa only [maxTri7] using hmax
    have hq' : q.1 < q.2.1 ∧ q.2.1 < q.2.2 := by
      simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    calc
      T.det * maxTri7 v = T.det * |sig (v q.1) (v q.2.1) (v q.2.2)| := by
        rw [hmax']
      _ = |sig (T.map (v q.1)) (T.map (v q.2.1)) (T.map (v q.2.2))| :=
        (abs_sig_posAffine T _ _ _).symm
      _ ≤ maxTri7 (fun i ↦ T.map (v i)) := by
        exact le_maxTri7 (fun i : Fin 7 ↦ T.map (v i)) q.1 q.2.1 q.2.2
          hq'.1 hq'.2

theorem minTri7_nonsingularAffine (v : Fin 7 → ℝ × ℝ)
    (T : NonsingularAffine) :
    minTri (fun i ↦ T.map (v i)) = |T.det| * minTri v := by
  apply le_antisymm
  · obtain ⟨q, hq, hmin⟩ :=
      Finset.exists_mem_eq_inf'
        (show (triples 7).Nonempty from Fact.out)
        (fun q : Fin 7 × Fin 7 × Fin 7 ↦
          |sig (v q.1) (v q.2.1) (v q.2.2)|)
    have hmin' : minTri v = |sig (v q.1) (v q.2.1) (v q.2.2)| := by
      simpa only [minTri] using hmin
    calc
      minTri (fun i ↦ T.map (v i)) ≤
          |sig (T.map (v q.1)) (T.map (v q.2.1)) (T.map (v q.2.2))| := by
        unfold minTri
        exact Finset.inf'_le _ hq
      _ = |T.det| * |sig (v q.1) (v q.2.1) (v q.2.2)| :=
        abs_sig_nonsingularAffine T _ _ _
      _ = |T.det| * minTri v := by rw [← hmin']
  · apply le_minTri
    intro q hq
    rw [abs_sig_nonsingularAffine]
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ hq) (abs_nonneg T.det)

theorem maxTri7_nonsingularAffine (v : Fin 7 → ℝ × ℝ)
    (T : NonsingularAffine) :
    maxTri7 (fun i ↦ T.map (v i)) = |T.det| * maxTri7 v := by
  apply le_antisymm
  · apply maxTri7_le
    intro q hq
    rw [abs_sig_nonsingularAffine]
    exact mul_le_mul_of_nonneg_left
      (Finset.le_sup'
        (fun q : Fin 7 × Fin 7 × Fin 7 ↦
          |sig (v q.1) (v q.2.1) (v q.2.2)|) hq)
      (abs_nonneg T.det)
  · obtain ⟨q, hq, hmax⟩ :=
      Finset.exists_mem_eq_sup'
        (show (triples 7).Nonempty from Fact.out)
        (fun q : Fin 7 × Fin 7 × Fin 7 ↦
          |sig (v q.1) (v q.2.1) (v q.2.2)|)
    have hmax' : maxTri7 v = |sig (v q.1) (v q.2.1) (v q.2.2)| := by
      simpa only [maxTri7] using hmax
    have hq' : q.1 < q.2.1 ∧ q.2.1 < q.2.2 := by
      simpa only [triples, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    calc
      |T.det| * maxTri7 v =
          |T.det| * |sig (v q.1) (v q.2.1) (v q.2.2)| := by rw [hmax']
      _ = |sig (T.map (v q.1)) (T.map (v q.2.1)) (T.map (v q.2.2))| :=
        (abs_sig_nonsingularAffine T _ _ _).symm
      _ ≤ maxTri7 (fun i ↦ T.map (v i)) := by
        exact le_maxTri7 (fun i : Fin 7 ↦ T.map (v i)) q.1 q.2.1 q.2.2
          hq'.1 hq'.2

/-- Distinct parameters in the invariant subinterval give genuinely distinct
solutions, even after arbitrary relabeling and positive-determinant affine
maps. -/
theorem cfg7Family_not_gaugeEquivalent {s t : ℝ}
    (hs : 6 / 5 ≤ s ∧ s ≤ 5 / 4) (ht : 6 / 5 ≤ t ∧ t ≤ 5 / 4)
    (hst : s ≠ t) : ¬ GaugeEquivalent (cfg7Family s) (cfg7Family t) := by
  intro hg
  rcases hg with ⟨σ, T, hmap⟩
  have hs' : 1 ≤ s ∧ s ≤ 4 / 3 := by constructor <;> nlinarith [hs.1, hs.2]
  have ht' : 1 ≤ t ∧ t ≤ 4 / 3 := by constructor <;> nlinarith [ht.1, ht.2]
  have hmin : minTri (cfg7Family t) = T.det * minTri (cfg7Family s) := by
    rw [hmap, minTri7_posAffine]
    rw [show (fun i ↦ cfg7Family s (σ i)) = cfg7Family s ∘ σ by rfl,
      minTri7_perm]
  rw [minTri_cfg7Family t ht', minTri_cfg7Family s hs'] at hmin
  have hdet : T.det = 1 := by nlinarith
  have hmax : maxTri7 (cfg7Family t) = T.det * maxTri7 (cfg7Family s) := by
    rw [hmap, maxTri7_posAffine]
    rw [show (fun i ↦ cfg7Family s (σ i)) = cfg7Family s ∘ σ by rfl,
      maxTri7_perm]
  rw [maxTri7_cfg7Family t ht, maxTri7_cfg7Family s hs, hdet, one_mul] at hmax
  exact hst hmax.symm

/-- Distinct parameters in the invariant subinterval remain inequivalent when
orientation-reversing nonsingular affine maps are also allowed. -/
theorem cfg7Family_not_affineEquivalent {s t : ℝ}
    (hs : 6 / 5 ≤ s ∧ s ≤ 5 / 4) (ht : 6 / 5 ≤ t ∧ t ≤ 5 / 4)
    (hst : s ≠ t) : ¬ AffineEquivalent (cfg7Family s) (cfg7Family t) := by
  intro ha
  rcases ha with ⟨σ, T, hmap⟩
  have hs' : 1 ≤ s ∧ s ≤ 4 / 3 := by constructor <;> nlinarith [hs.1, hs.2]
  have ht' : 1 ≤ t ∧ t ≤ 4 / 3 := by constructor <;> nlinarith [ht.1, ht.2]
  have hmin : minTri (cfg7Family t) = |T.det| * minTri (cfg7Family s) := by
    rw [hmap, minTri7_nonsingularAffine]
    rw [show (fun i ↦ cfg7Family s (σ i)) = cfg7Family s ∘ σ by rfl,
      minTri7_perm]
  rw [minTri_cfg7Family t ht', minTri_cfg7Family s hs'] at hmin
  have hdet : |T.det| = 1 := by nlinarith
  have hmax : maxTri7 (cfg7Family t) = |T.det| * maxTri7 (cfg7Family s) := by
    rw [hmap, maxTri7_nonsingularAffine]
    rw [show (fun i ↦ cfg7Family s (σ i)) = cfg7Family s ∘ σ by rfl,
      maxTri7_perm]
  rw [maxTri7_cfg7Family t ht, maxTri7_cfg7Family s hs, hdet, one_mul] at hmax
  exact hst hmax.symm

/-- On the invariant parameter interval, affine equivalence determines the
parameter. -/
theorem cfg7Family_affineEquivalent_injective {s t : ℝ}
    (hs : 6 / 5 ≤ s ∧ s ≤ 5 / 4) (ht : 6 / 5 ≤ t ∧ t ≤ 5 / 4)
    (ha : AffineEquivalent (cfg7Family s) (cfg7Family t)) : s = t := by
  by_contra hst
  exact (cfg7Family_not_affineEquivalent hs ht hst) ha

/-! ## A countably infinite subfamily -/

/-- An injective sequence staying in `[6/5,5/4)`. -/
noncomputable def cfg7Parameter (n : ℕ) : ℝ :=
  5 / 4 - 1 / (20 * ((n : ℝ) + 1))

theorem cfg7Parameter_bounds (n : ℕ) :
    6 / 5 ≤ cfg7Parameter n ∧ cfg7Parameter n ≤ 5 / 4 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < (20 : ℝ) * ((n : ℝ) + 1) := by positivity
  have hfrac :
      1 / ((20 : ℝ) * ((n : ℝ) + 1)) ≤ 1 / 20 := by
    apply (div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 20)).2
    nlinarith
  have hfrac0 : 0 ≤ 1 / ((20 : ℝ) * ((n : ℝ) + 1)) :=
    one_div_nonneg.mpr hd.le
  unfold cfg7Parameter
  constructor <;> nlinarith

theorem cfg7Parameter_injective : Function.Injective cfg7Parameter := by
  intro m n h
  have hrec :
      1 / ((20 : ℝ) * ((m : ℝ) + 1)) =
        1 / ((20 : ℝ) * ((n : ℝ) + 1)) := by
    unfold cfg7Parameter at h
    linarith
  have hden :
      (20 : ℝ) * ((m : ℝ) + 1) =
        (20 : ℝ) * ((n : ℝ) + 1) := by
    simpa only [one_div, inv_inj] using hrec
  have hcast : (m : ℝ) = (n : ℝ) := by nlinarith
  exact_mod_cast hcast

/-- Final theorem shape requested by the unified challenge: infinitely many
pairwise affine-inequivalent unit-hull optimal configurations. -/
theorem heilbronn_convex_seven_infinite_family :
    ∃ F : ℕ → (Fin 7 → ℝ × ℝ),
      (∀ n, volume (convexHull ℝ (Set.range (F n))) = 1 ∧
        minTri (F n) = 2 * v7) ∧
      (∀ m n, AffineEquivalent (F m) (F n) → m = n) := by
  refine ⟨fun n ↦ cfg7Family (cfg7Parameter n), ?_, ?_⟩
  · intro n
    have hb := cfg7Parameter_bounds n
    have hb' : 1 ≤ cfg7Parameter n ∧ cfg7Parameter n ≤ 4 / 3 := by
      constructor <;> nlinarith [hb.1, hb.2]
    refine ⟨volume_convexHull_cfg7Family (cfg7Parameter n) hb', ?_⟩
    rw [minTri_cfg7Family (cfg7Parameter n) hb', v7]
    norm_num
  · intro m n hg
    apply cfg7Parameter_injective
    exact cfg7Family_affineEquivalent_injective
      (cfg7Parameter_bounds m) (cfg7Parameter_bounds n) hg

end HeilbronnChallenge
