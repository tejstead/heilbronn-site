import Heilbronn8.HullSixOneFiveArea
import Heilbronn8.HullSixOneFiveAdapterAudit
import Heilbronn8.Survivors.Join.HullSixVariationExclusion

/-!
# Residual-to-scalar adapter for the hull-six `1 + 5` chamber

This file performs the determinant bookkeeping that is common to every
geometric `1 + 5` branch.  Start with a compact hull-six residual whose cycle
has already been rotated and whose line orientation has already been chosen
so that `cycle 0` has positive `PQ`-level and `cycle 1,...,cycle 5` have
negative level.  The four scalar `A` values are the `P`-fan areas on the four
edges of the five-vertex block.  The five scalar `B` values are the negatives
of those five line levels.

The constructor below proves all floors, base-change formulas, and ear
identities required by `HullSixOneFiveRawData`.  The first-transition theorem
then constructs and orders the two ray crossings.  Thus the only remaining
geometric seam is transport from a cyclic sign block to this rotated,
oriented frame.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-- Position `i` in the five-vertex block is position `i+1` in the rotated
six-cycle. -/
def hullSixOneFiveLowerIndex (i : Fin 5) : Fin 6 :=
  ⟨i.val + 1, by omega⟩

/-- The three-point identity which turns a consecutive hull ear into the
scalar ear relation. -/
lemma sig_oneFive_ear_identity
    (p q l0 l1 l2 : Real × Real) :
    (-sig p q l1) * sig l0 l1 l2 =
      sig p l0 l1 * ((-sig p q l1) - (-sig p q l2)) +
        sig p l1 l2 * ((-sig p q l1) - (-sig p q l0)) := by
  simp only [sig]
  ring

/-- The Plucker identity on an edge crossed by a ray from `u` through `p`.
The same formula may be used with `q` in place of `p`. -/
lemma sig_oneFive_crossing_identity
    (p q u l0 l1 : Real × Real) :
    sig p q u * sig p l0 l1 =
      (-sig p q l1) * sig p u l0 -
        (-sig p q l0) * sig p u l1 := by
  simp only [sig]
  ring

/-- The corresponding Plucker identity for the ray from `u` through `q`,
written with the `Q`-fan expressed in the raw scalar coordinates based at
`p`. -/
lemma sig_oneFive_crossing_identity_q
    (p q u l0 l1 : Real × Real) :
    sig p q u *
        (sig p l0 l1 + (-sig p q l1) - (-sig p q l0)) =
      (-sig p q l1) * sig q u l0 -
        (-sig p q l0) * sig q u l1 := by
  simp only [sig]
  ring

private lemma signedFloor_cases {m t : ℝ}
    (hm : 0 < m) (hfloor : m ≤ |t|) :
    m ≤ t ∨ t ≤ -m := by
  by_cases ht : 0 ≤ t
  · left
    rwa [abs_of_nonneg ht] at hfloor
  · right
    have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht'] at hfloor
    linarith

/-- In a five-term nonzero sign sequence which starts positive and ends
negative, the first negative entry determines a crossed edge. -/
lemma finFive_firstTransition
    {m : ℝ} (hm : 0 < m) (S : Fin 5 → ℝ)
    (hfloor : ∀ i, m ≤ |S i|)
    (hfirst : m ≤ S 0) (hlast : S 4 ≤ -m) :
    ∃ k : Fin 4,
      (∀ i : Fin 5, i.val ≤ k.val → m ≤ S i) ∧
      m ≤ S k.castSucc ∧ S k.succ ≤ -m := by
  rcases signedFloor_cases hm (hfloor 1) with h₁ | h₁
  · rcases signedFloor_cases hm (hfloor 2) with h₂ | h₂
    · rcases signedFloor_cases hm (hfloor 3) with h₃ | h₃
      · refine ⟨3, ?_, ?_, ?_⟩
        · intro i hi
          fin_cases i
          · exact hfirst
          · exact h₁
          · exact h₂
          · exact h₃
          · norm_num at hi
        · simpa using h₃
        · simpa using hlast
      · refine ⟨2, ?_, ?_, ?_⟩
        · intro i hi
          fin_cases i
          · exact hfirst
          · exact h₁
          · exact h₂
          · norm_num at hi
          · norm_num at hi
        · simpa using h₂
        · simpa using h₃
    · refine ⟨1, ?_, ?_, ?_⟩
      · intro i hi
        fin_cases i
        · exact hfirst
        · exact h₁
        · norm_num at hi
        · norm_num at hi
        · norm_num at hi
      · simpa using h₁
      · simpa using h₂
  · refine ⟨0, ?_, ?_, ?_⟩
    · intro i hi
      fin_cases i
      · exact hfirst
      · norm_num at hi
      · norm_num at hi
      · norm_num at hi
      · norm_num at hi
    · simpa using hfirst
    · simpa using h₁

namespace HullSixCompactCrossChordResidual

private lemma lowerLevelMagnitude_floor
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (hlower : ∀ i : Fin 5,
      sig (v p) (v q) (v (cycle (hullSixOneFiveLowerIndex i))) < 0)
    (i : Fin 5) :
    minTri v ≤
      -sig (v p) (v q) (v (cycle (hullSixOneFiveLowerIndex i))) := by
  have hfloor := R.lineLevel_floor (hullSixOneFiveLowerIndex i)
  rw [abs_of_neg (hlower i)] at hfloor
  exact hfloor

private lemma pLowerEdge_floor
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (i : Fin 4) :
    minTri v ≤
      sig (v p)
        (v (cycle (hullSixOneFiveLowerIndex i.castSucc)))
        (v (cycle (hullSixOneFiveLowerIndex i.succ))) := by
  fin_cases i
  · simpa [hullSixOneFiveLowerIndex] using
      (minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective p
        R.p_outside (1 : Fin 6) (R.p_boundary_pos 1))
  · simpa [hullSixOneFiveLowerIndex] using
      (minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective p
        R.p_outside (2 : Fin 6) (R.p_boundary_pos 2))
  · simpa [hullSixOneFiveLowerIndex] using
      (minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective p
        R.p_outside (3 : Fin 6) (R.p_boundary_pos 3))
  · simpa [hullSixOneFiveLowerIndex] using
      (minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective p
        R.p_outside (4 : Fin 6) (R.p_boundary_pos 4))

private lemma qLowerEdge_floor
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (i : Fin 4) :
    minTri v ≤
      sig (v q)
        (v (cycle (hullSixOneFiveLowerIndex i.castSucc)))
        (v (cycle (hullSixOneFiveLowerIndex i.succ))) := by
  fin_cases i
  · simpa [hullSixOneFiveLowerIndex] using
      (minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective q
        R.q_outside (1 : Fin 6) (R.q_boundary_pos 1))
  · simpa [hullSixOneFiveLowerIndex] using
      (minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective q
        R.q_outside (2 : Fin 6) (R.q_boundary_pos 2))
  · simpa [hullSixOneFiveLowerIndex] using
      (minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective q
        R.q_outside (3 : Fin 6) (R.q_boundary_pos 3))
  · simpa [hullSixOneFiveLowerIndex] using
      (minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective q
        R.q_outside (4 : Fin 6) (R.q_boundary_pos 4))

private lemma cycleTriple_floor
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (i j k : Fin 6) (hij : i < j) (hjk : j < k) :
    minTri v ≤ sig (v (cycle i)) (v (cycle j)) (v (cycle k)) := by
  have hik : i < k := hij.trans hjk
  exact minTri_le_pos_sig_of_pairwise_ne v
    (R.cycle_injective.ne (ne_of_lt hij))
    (R.cycle_injective.ne (ne_of_lt hik))
    (R.cycle_injective.ne (ne_of_lt hjk))
    (R.cycle_strict.pos i j k hij hjk)

/-- Convert a normalized geometric `1 + 5` residual into the raw scalar
package.  Positivity of the isolated level is not needed for this constructor;
it enters later as the scalar crossing parameter.

The only extra hypothesis is the already-normalized sign pattern on the five
lower vertices. -/
noncomputable def oneFiveRawData
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (hlower : ∀ i : Fin 5,
      sig (v p) (v q) (v (cycle (hullSixOneFiveLowerIndex i))) < 0) :
    HullSixOneFiveRawData where
  m := minTri v
  A₁ := sig (v p) (v (cycle 1)) (v (cycle 2))
  A₂ := sig (v p) (v (cycle 2)) (v (cycle 3))
  A₃ := sig (v p) (v (cycle 3)) (v (cycle 4))
  A₄ := sig (v p) (v (cycle 4)) (v (cycle 5))
  B₁ := -sig (v p) (v q) (v (cycle 1))
  B₂ := -sig (v p) (v q) (v (cycle 2))
  B₃ := -sig (v p) (v q) (v (cycle 3))
  B₄ := -sig (v p) (v q) (v (cycle 4))
  B₅ := -sig (v p) (v q) (v (cycle 5))
  E₂ := sig (v (cycle 1)) (v (cycle 2)) (v (cycle 3))
  E₃ := sig (v (cycle 2)) (v (cycle 3)) (v (cycle 4))
  E₄ := sig (v (cycle 3)) (v (cycle 4)) (v (cycle 5))
  hm := R.minTri_pos
  hA₁ := by simpa [hullSixOneFiveLowerIndex] using R.pLowerEdge_floor 0
  hA₂ := by simpa [hullSixOneFiveLowerIndex] using R.pLowerEdge_floor 1
  hA₃ := by simpa [hullSixOneFiveLowerIndex] using R.pLowerEdge_floor 2
  hA₄ := by simpa [hullSixOneFiveLowerIndex] using R.pLowerEdge_floor 3
  hB₁ := by
    simpa [hullSixOneFiveLowerIndex] using
      R.lowerLevelMagnitude_floor hlower 0
  hB₂ := by
    simpa [hullSixOneFiveLowerIndex] using
      R.lowerLevelMagnitude_floor hlower 1
  hB₃ := by
    simpa [hullSixOneFiveLowerIndex] using
      R.lowerLevelMagnitude_floor hlower 2
  hB₄ := by
    simpa [hullSixOneFiveLowerIndex] using
      R.lowerLevelMagnitude_floor hlower 3
  hB₅ := by
    simpa [hullSixOneFiveLowerIndex] using
      R.lowerLevelMagnitude_floor hlower 4
  hC₁ := by
    have h : minTri v ≤
        sig (v q) (v (cycle 1)) (v (cycle 2)) := by
      simpa [hullSixOneFiveLowerIndex] using R.qLowerEdge_floor 0
    have hbase := sig_crossChord_base_change
      (v p) (v q) (v (cycle 1)) (v (cycle 2))
    nlinarith only [h, hbase]
  hC₂ := by
    have h : minTri v ≤
        sig (v q) (v (cycle 2)) (v (cycle 3)) := by
      simpa [hullSixOneFiveLowerIndex] using R.qLowerEdge_floor 1
    have hbase := sig_crossChord_base_change
      (v p) (v q) (v (cycle 2)) (v (cycle 3))
    nlinarith only [h, hbase]
  hC₃ := by
    have h : minTri v ≤
        sig (v q) (v (cycle 3)) (v (cycle 4)) := by
      simpa [hullSixOneFiveLowerIndex] using R.qLowerEdge_floor 2
    have hbase := sig_crossChord_base_change
      (v p) (v q) (v (cycle 3)) (v (cycle 4))
    nlinarith only [h, hbase]
  hC₄ := by
    have h : minTri v ≤
        sig (v q) (v (cycle 4)) (v (cycle 5)) := by
      simpa [hullSixOneFiveLowerIndex] using R.qLowerEdge_floor 3
    have hbase := sig_crossChord_base_change
      (v p) (v q) (v (cycle 4)) (v (cycle 5))
    nlinarith only [h, hbase]
  hE₂ := R.cycleTriple_floor 1 2 3 (by decide) (by decide)
  hE₃ := R.cycleTriple_floor 2 3 4 (by decide) (by decide)
  hE₄ := R.cycleTriple_floor 3 4 5 (by decide) (by decide)
  ear₂_identity := sig_oneFive_ear_identity
    (v p) (v q) (v (cycle 1)) (v (cycle 2)) (v (cycle 3))
  ear₃_identity := sig_oneFive_ear_identity
    (v p) (v q) (v (cycle 2)) (v (cycle 3)) (v (cycle 4))
  ear₄_identity := sig_oneFive_ear_identity
    (v p) (v q) (v (cycle 3)) (v (cycle 4)) (v (cycle 5))

/-- Exact normalized hull decomposition for the rotated `1 + 5` frame.
The two displayed transition caps are based at opposite interior points;
base change on the closing edge contributes precisely `B₅ + U`. -/
theorem oneFive_hullArea_div_eq
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (hlower : ∀ i : Fin 5,
      sig (v p) (v q) (v (cycle (hullSixOneFiveLowerIndex i))) < 0) :
    let raw := R.oneFiveRawData hlower
    let D := raw.normalize
    doubledHullArea v / minTri v =
      D.area + D.b₅ +
        sig (v p) (v (cycle 0)) (v (cycle 1)) / minTri v +
        sig (v q) (v (cycle 5)) (v (cycle 0)) / minTri v +
        sig (v p) (v q) (v (cycle 0)) / minTri v := by
  dsimp
  have hbase := sig_crossChord_base_change
    (v p) (v q) (v (cycle 5)) (v (cycle 0))
  have hHull : doubledHullArea v =
      sig (v p) (v (cycle 0)) (v (cycle 1)) +
      sig (v p) (v (cycle 1)) (v (cycle 2)) +
      sig (v p) (v (cycle 2)) (v (cycle 3)) +
      sig (v p) (v (cycle 3)) (v (cycle 4)) +
      sig (v p) (v (cycle 4)) (v (cycle 5)) +
      sig (v p) (v (cycle 5)) (v (cycle 0)) := by
    calc
      doubledHullArea v = fanSum v cycle := R.hull_area_eq
      _ = _ := fanSum_six_eq_boundary v cycle (v p)
  dsimp [oneFiveRawData, HullSixOneFiveRawData.normalize,
    HullSixOneFiveData.area]
  field_simp [ne_of_gt R.minTri_pos]
  nlinarith only [hbase, hHull]

/-- The left transition cap in the decomposition has the unit normalized
floor. -/
theorem oneFive_leftCap_floor
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q) :
    1 ≤ sig (v p) (v (cycle 0)) (v (cycle 1)) / minTri v := by
  have hraw := minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective p
    R.p_outside (0 : Fin 6) (R.p_boundary_pos 0)
  exact (le_div_iff₀ R.minTri_pos).2 (by simpa using hraw)

/-- The right transition cap based at `Q` has the unit normalized floor. -/
theorem oneFive_rightCap_floor
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q) :
    1 ≤ sig (v q) (v (cycle 5)) (v (cycle 0)) / minTri v := by
  have hraw := minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective q
    R.q_outside (5 : Fin 6) (R.q_boundary_pos 5)
  exact (le_div_iff₀ R.minTri_pos).2 (by simpa using hraw)

private lemma pSpoke_floor
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (i : Fin 5) :
    minTri v ≤
      |sig (v p) (v (cycle 0))
        (v (cycle (hullSixOneFiveLowerIndex i)))| := by
  apply minTri_le_abs_sig_of_pairwise_ne v
  · intro hp
    exact R.p_outside ⟨0, hp.symm⟩
  · intro hp
    exact R.p_outside ⟨hullSixOneFiveLowerIndex i, hp.symm⟩
  · apply R.cycle_injective.ne
    show (0 : Fin 6) ≠ hullSixOneFiveLowerIndex i
    intro hi
    have := congrArg Fin.val hi
    simp [hullSixOneFiveLowerIndex] at this

private lemma qSpoke_floor
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (i : Fin 5) :
    minTri v ≤
      |sig (v q) (v (cycle 0))
        (v (cycle (hullSixOneFiveLowerIndex i)))| := by
  apply minTri_le_abs_sig_of_pairwise_ne v
  · intro hq
    exact R.q_outside ⟨0, hq.symm⟩
  · intro hq
    exact R.q_outside ⟨hullSixOneFiveLowerIndex i, hq.symm⟩
  · apply R.cycle_injective.ne
    show (0 : Fin 6) ≠ hullSixOneFiveLowerIndex i
    intro hi
    have := congrArg Fin.val hi
    simp [hullSixOneFiveLowerIndex] at this

/-- The first spoke sign change for `P` and for `Q` gives an ordered pair of
crossed lower-chain edges.  The order is forced by
`T i = S i + U + B i`, so no chamber enumeration is needed. -/
theorem oneFive_orderedSpokeCrossings
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (hisolated :
      0 < sig (v p) (v q) (v (cycle 0)))
    (hlower : ∀ i : Fin 5,
      sig (v p) (v q) (v (cycle (hullSixOneFiveLowerIndex i))) < 0) :
    ∃ k l : Fin 4, k ≤ l ∧
      minTri v ≤ sig (v p) (v (cycle 0))
        (v (cycle (hullSixOneFiveLowerIndex k.castSucc))) ∧
      sig (v p) (v (cycle 0))
        (v (cycle (hullSixOneFiveLowerIndex k.succ))) ≤ -minTri v ∧
      minTri v ≤ sig (v q) (v (cycle 0))
        (v (cycle (hullSixOneFiveLowerIndex l.castSucc))) ∧
      sig (v q) (v (cycle 0))
        (v (cycle (hullSixOneFiveLowerIndex l.succ))) ≤ -minTri v := by
  let raw := R.oneFiveRawData hlower
  let U := sig (v p) (v q) (v (cycle 0))
  let S : Fin 5 → ℝ := fun i =>
    sig (v p) (v (cycle 0))
      (v (cycle (hullSixOneFiveLowerIndex i)))
  let T : Fin 5 → ℝ := fun i =>
    sig (v q) (v (cycle 0))
      (v (cycle (hullSixOneFiveLowerIndex i)))
  have hU : minTri v ≤ U := by
    have hfloor := R.lineLevel_floor 0
    rw [abs_of_pos hisolated] at hfloor
    simpa [U] using hfloor
  have hSfirst : minTri v ≤ S 0 := by
    simpa [S, hullSixOneFiveLowerIndex] using
      (minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective p
        R.p_outside (0 : Fin 6) (R.p_boundary_pos 0))
  have hwrap : (5 : Fin 6) + 1 = 0 := by decide
  have hSlast : S 4 ≤ -minTri v := by
    have hfloor := minTri_le_sixCycle_boundary_sig v cycle
      R.cycle_injective p R.p_outside (5 : Fin 6) (R.p_boundary_pos 5)
    have hfloor₀ : minTri v ≤
        sig (v p) (v (cycle 5)) (v (cycle 0)) := by
      simpa only [hwrap] using hfloor
    have hid : S 4 =
        -sig (v p) (v (cycle 5)) (v (cycle 0)) := by
      dsimp [S, hullSixOneFiveLowerIndex]
      simp only [sig]
      ring
    rw [hid]
    linarith only [hfloor₀]
  have hTfirst : minTri v ≤ T 0 := by
    simpa [T, hullSixOneFiveLowerIndex] using
      (minTri_le_sixCycle_boundary_sig v cycle R.cycle_injective q
        R.q_outside (0 : Fin 6) (R.q_boundary_pos 0))
  have hTlast : T 4 ≤ -minTri v := by
    have hfloor := minTri_le_sixCycle_boundary_sig v cycle
      R.cycle_injective q R.q_outside (5 : Fin 6) (R.q_boundary_pos 5)
    have hfloor₀ : minTri v ≤
        sig (v q) (v (cycle 5)) (v (cycle 0)) := by
      simpa only [hwrap] using hfloor
    have hid : T 4 =
        -sig (v q) (v (cycle 5)) (v (cycle 0)) := by
      dsimp [T, hullSixOneFiveLowerIndex]
      simp only [sig]
      ring
    rw [hid]
    linarith only [hfloor₀]
  obtain ⟨k, hSprefix, hSk, hSnext⟩ :=
    finFive_firstTransition R.minTri_pos S R.pSpoke_floor hSfirst hSlast
  obtain ⟨l, _hTprefix, hTl, hTnext⟩ :=
    finFive_firstTransition R.minTri_pos T R.qSpoke_floor hTfirst hTlast
  have hbRaw (i : Fin 5) :
      raw.bRawAt i =
        -sig (v p) (v q)
          (v (cycle (hullSixOneFiveLowerIndex i))) := by
    fin_cases i <;>
      simp [raw, oneFiveRawData, HullSixOneFiveRawData.bRawAt,
        hullSixOneFiveLowerIndex]
  have hshift : ∀ i, T i = S i + U + raw.bRawAt i := by
    intro i
    have hbase := sig_crossChord_base_change
      (v p) (v q) (v (cycle 0))
        (v (cycle (hullSixOneFiveLowerIndex i)))
    calc
      T i = S i + U -
          sig (v p) (v q)
            (v (cycle (hullSixOneFiveLowerIndex i))) := by
        simpa [T, S, U] using hbase
      _ = S i + U + raw.bRawAt i := by rw [hbRaw i] <;> ring
  have hUraw : raw.m ≤ U := by
    change minTri v ≤ U
    exact hU
  have hkl : k ≤ l := raw.ordered_crossings_of_shift U
    hUraw S T hshift k l hSprefix hTnext
  exact ⟨k, l, hkl, hSk, hSnext, hTl, hTnext⟩

/-- Complete closure of an already rotated and oriented `1 + 5` residual.
The scalar expression is the exact normalized hull area, and the order-free
scalar theorem handles whichever lower-chain endpoint has the smaller line
level. -/
theorem oneFive_normalized_twentyFive_minTri_le_twice_hullArea
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (hisolated :
      0 < sig (v p) (v q) (v (cycle 0)))
    (hlower : ∀ i : Fin 5,
      sig (v p) (v q) (v (cycle (hullSixOneFiveLowerIndex i))) < 0) :
    25 * minTri v ≤ 2 * doubledHullArea v := by
  let raw := R.oneFiveRawData hlower
  let D := raw.normalize
  let U := sig (v p) (v q) (v (cycle 0))
  let u := U / minTri v
  let leftCap :=
    sig (v p) (v (cycle 0)) (v (cycle 1)) / minTri v
  let rightCap :=
    sig (v q) (v (cycle 5)) (v (cycle 0)) / minTri v
  obtain ⟨k, l, hkl, hPk, hPkNext, hQl, hQlNext⟩ :=
    R.oneFive_orderedSpokeCrossings hisolated hlower
  have hpluckerP :
      U * raw.aRawAt k =
        raw.bRawAt k.succ *
            sig (v p) (v (cycle 0))
              (v (cycle (hullSixOneFiveLowerIndex k.castSucc))) -
          raw.bRawAt k.castSucc *
            sig (v p) (v (cycle 0))
              (v (cycle (hullSixOneFiveLowerIndex k.succ))) := by
    have hid := sig_oneFive_crossing_identity
      (v p) (v q) (v (cycle 0))
      (v (cycle (hullSixOneFiveLowerIndex k.castSucc)))
      (v (cycle (hullSixOneFiveLowerIndex k.succ)))
    fin_cases k <;>
      simpa [raw, U, oneFiveRawData, HullSixOneFiveRawData.aRawAt,
        HullSixOneFiveRawData.bRawAt, hullSixOneFiveLowerIndex] using hid
  have hpluckerQ :
      U * raw.cRawAt l =
        raw.bRawAt l.succ *
            sig (v q) (v (cycle 0))
              (v (cycle (hullSixOneFiveLowerIndex l.castSucc))) -
          raw.bRawAt l.castSucc *
            sig (v q) (v (cycle 0))
              (v (cycle (hullSixOneFiveLowerIndex l.succ))) := by
    have hid := sig_oneFive_crossing_identity_q
      (v p) (v q) (v (cycle 0))
      (v (cycle (hullSixOneFiveLowerIndex l.castSucc)))
      (v (cycle (hullSixOneFiveLowerIndex l.succ)))
    fin_cases l <;>
      simpa [raw, U, oneFiveRawData, HullSixOneFiveRawData.cRawAt,
        HullSixOneFiveRawData.bRawAt, hullSixOneFiveLowerIndex] using hid
  have hcrossA : D.adjacentSum k ≤ u * D.aAt k := by
    have h := HullSixOneFiveRawData.raw_crossing_le raw.hm
      (raw.hBRawAt k.castSucc) (raw.hBRawAt k.succ)
      hPk hPkNext hpluckerP
    have huEq : u = U / raw.m := by
      dsimp only [u]
      change U / minTri v = U / minTri v
      rfl
    rw [huEq]
    fin_cases k <;>
      simpa [D, HullSixOneFiveRawData.normalize,
        HullSixOneFiveData.adjacentSum, HullSixOneFiveData.aAt,
        HullSixOneFiveRawData.aRawAt,
        HullSixOneFiveRawData.bRawAt] using h
  have hcrossC : D.adjacentSum l ≤ u * D.cAt l := by
    have h := HullSixOneFiveRawData.raw_crossing_le raw.hm
      (raw.hBRawAt l.castSucc) (raw.hBRawAt l.succ)
      hQl hQlNext hpluckerQ
    have huEq : u = U / raw.m := by
      dsimp only [u]
      change U / minTri v = U / minTri v
      rfl
    rw [huEq]
    rw [show D.cAt l = raw.cRawAt l / raw.m by
      simpa [D] using raw.normalize_cAt l]
    fin_cases l <;>
      simpa [D, HullSixOneFiveRawData.normalize,
        HullSixOneFiveData.adjacentSum,
        HullSixOneFiveRawData.bRawAt] using h
  have hU : minTri v ≤ U := by
    have hfloor := R.lineLevel_floor 0
    rw [abs_of_pos hisolated] at hfloor
    simpa [U] using hfloor
  have hu : 1 ≤ u := by
    exact (le_div_iff₀ R.minTri_pos).2 (by simpa [u] using hU)
  have hleftCap : 1 ≤ leftCap := by
    simpa [leftCap, raw, oneFiveRawData] using R.oneFive_leftCap_floor
  have hrightCap : 1 ≤ rightCap := by
    simpa [rightCap, raw, oneFiveRawData] using R.oneFive_rightCap_floor
  have hExpr := D.hullExpression_ge_twenty_five_halves_orderFree
    k l hkl u leftCap rightCap hu hleftCap hrightCap hcrossA hcrossC
  have hHull :
      doubledHullArea v / minTri v =
        D.area + D.b₅ + leftCap + rightCap + u := by
    simpa [raw, D, U, u, leftCap, rightCap] using
      R.oneFive_hullArea_div_eq hlower
  have hratio : 25 / 2 ≤ doubledHullArea v / minTri v := by
    calc
      25 / 2 ≤ D.area + D.b₅ + leftCap + rightCap + u := hExpr
      _ = doubledHullArea v / minTri v := hHull.symm
  have hmul : (25 / 2) * minTri v ≤ doubledHullArea v :=
    (le_div_iff₀ R.minTri_pos).1 hratio
  nlinarith only [hmul]

/-- An already normalized `1 + 5` sign block cannot occur in a beating
compact residual. -/
theorem oneFive_normalized_false
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual v cycle p q)
    (hisolated :
      0 < sig (v p) (v q) (v (cycle 0)))
    (hlower : ∀ i : Fin 5,
      sig (v p) (v q) (v (cycle (hullSixOneFiveLowerIndex i))) < 0) :
    False := by
  have hbound :=
    R.oneFive_normalized_twentyFive_minTri_le_twice_hullArea
      hisolated hlower
  have hcut :
      (2 / 25 : ℝ) * doubledHullArea v < minTri v :=
    R.cut_margin
  nlinarith

end HullSixCompactCrossChordResidual

end Heilbronn8
