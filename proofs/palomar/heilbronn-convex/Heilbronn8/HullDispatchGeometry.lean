import Heilbronn8.HullArea
import Heilbronn8.Compose
import Heilbronn8.Radon
import Heilbronn8.CoverGeometry

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace Heilbronn8

/-!
# Hull dispatch for generated sign cells

The emitter supplies:

* a strict orientation oracle for the leaf's realized sign word;
* the hull cycle as an explicit list;
* short proofs that the cycle and its fan-containment witnesses agree with
  that oracle.

Lean derives `StrictCyclicPos`, `FanCovers`, and hence `IsHullArea`.  The
Cover-side interface then requires the declared fan to equal the `H` used by
`Beats` before any beat row can be replayed.
-/

/--
A realized strict sign cell.

The emitted `ccw` function is the oriented lookup into the leaf's 56-entry
sign word. Its soundness proof must ultimately come from the leaf's sign rows.
-/
structure StrictSignData (v : Configuration) where
  ccw : Fin 8 → Fin 8 → Fin 8 → Bool
  pos_of_eq_true : ∀ i j k : Fin 8,
    ccw i j k = true → 0 < sig (v i) (v j) (v k)

namespace StrictSignData

/-- The canonical strict oracle after the zero-sign dispatcher has ruled out
all 56 equality cases. -/
noncomputable def ofAllTripleSignsStrict (v : Configuration)
    (_hstrict : AllTripleSignsStrict v) : StrictSignData v where
  ccw i j k := decide (0 < sig (v i) (v j) (v k))
  pos_of_eq_true _ _ _ h := of_decide_eq_true h

@[simp] lemma ofAllTripleSignsStrict_ccw (v : Configuration)
    (hstrict : AllTripleSignsStrict v) (i j k : Fin 8) :
    (ofAllTripleSignsStrict v hstrict).ccw i j k = true ↔
      0 < sig (v i) (v j) (v k) := by
  simp [ofAllTripleSignsStrict]

/-- On an increasing triple the false branch of the canonical oracle is
strictly negative; the dispatcher has already excluded equality. -/
lemma ofAllTripleSignsStrict_neg_of_eq_false (v : Configuration)
    (hstrict : AllTripleSignsStrict v) {i j k : Fin 8}
    (hij : i < j) (hjk : j < k)
    (hfalse : (ofAllTripleSignsStrict v hstrict).ccw i j k = false) :
    sig (v i) (v j) (v k) < 0 := by
  have hnpos : ¬ 0 < sig (v i) (v j) (v k) := by
    simpa [ofAllTripleSignsStrict] using hfalse
  exact lt_of_le_of_ne (le_of_not_gt hnpos) (hstrict i j k hij hjk)

end StrictSignData

/--
The explicitly declared hull cycle. The length proofs are kernel-cheap for
literal emitted lists (`by decide`).
-/
structure HullCycleData where
  cycle : List (Fin 8)
  length_ge_three : 3 ≤ cycle.length
  length_le_eight : cycle.length ≤ 8

namespace HullCycleData

instance (d : HullCycleData) : NeZero d.cycle.length :=
  ⟨Nat.ne_of_gt
    (lt_of_lt_of_le (by decide : 0 < 3) d.length_ge_three)⟩

/-- The finite tuple represented by the emitted list. -/
def get (d : HullCycleData) : Fin d.cycle.length → Fin 8 :=
  d.cycle.get

/-- Transport an emitted cycle to a statically known hull size. -/
def castGet (d : HullCycleData) {m : Nat}
    (hm : d.cycle.length = m) : Fin m → Fin 8 :=
  fun i => d.get (Fin.cast hm.symm i)

/--
The exact H-expression used by the engine: the anchored fan over the declared
chirotope hull cycle.
-/
noncomputable def fanExpr
    (d : HullCycleData) (v : Configuration) : ℝ :=
  fanSum v d.get

lemma castGet_injective (d : HullCycleData) {m : Nat}
    (hm : d.cycle.length = m) (hd : d.cycle.Nodup) :
    Function.Injective (d.castGet hm) := by
  intro i j hij
  have hc : Fin.cast hm.symm i = Fin.cast hm.symm j :=
    hd.injective_get hij
  exact (Fin.cast_injective hm.symm) hc

lemma strictCyclicPos_cast {v : Configuration}
    (d : HullCycleData) {m : Nat}
    (hm : d.cycle.length = m)
    (h : StrictCyclicPos d.get v) :
    StrictCyclicPos (d.castGet hm) v := by
  constructor
  · intro i j k hij hjk
    exact h.1 _ _ _
      (by simpa using hij)
      (by simpa using hjk)
  · intro i j k hij hjk
    exact h.2 _ _ _
      (by simpa using hij)
      (by simpa using hjk)

lemma fanCovers_cast {v : Configuration}
    (d : HullCycleData) {m : Nat} [NeZero m]
    (hm : d.cycle.length = m)
    (h : FanCovers v d.get) :
    FanCovers v (d.castGet hm) := by
  intro p hp
  have hp' : p ∉ Set.range d.get := by
    rintro ⟨i, rfl⟩
    apply hp
    exact ⟨Fin.cast hm i, by simp [castGet]⟩
  obtain ⟨i, j, hi, hij, htri⟩ := h p hp'
  refine ⟨Fin.cast hm i, Fin.cast hm j, ?_, ?_, ?_⟩
  · rw [← Fin.cast_zero hm]
    exact (Fin.cast_lt_cast hm).2 hi
  · exact (Fin.cast_lt_cast hm).2 hij
  · simpa [castGet] using htri

lemma fanSum_castGet {v : Configuration}
    (d : HullCycleData) {m : Nat} [NeZero m]
    (hm : d.cycle.length = m) :
    fanSum v (d.castGet hm) = d.fanExpr v := by
  subst m
  rfl

end HullCycleData

/--
The four strict orientation facts which certify membership in one positively
oriented triangle.
-/
structure DirectInTriSigns {v : Configuration}
    (S : StrictSignData v) (p a b c : Fin 8) : Prop where
  abc : S.ccw a b c = true
  pbc : S.ccw p b c = true
  apc : S.ccw a p c = true
  abp : S.ccw a b p = true

lemma DirectInTriSigns.sound
    {v : Configuration} {S : StrictSignData v}
    {p a b c : Fin 8}
    (h : DirectInTriSigns S p a b c) :
    InTri (v p) (v a) (v b) (v c) := by
  exact inTri_of_sig (v p) (v a) (v b) (v c)
    (S.pos_of_eq_true a b c h.abc)
    (S.pos_of_eq_true p b c h.pbc).le
    (S.pos_of_eq_true a p c h.apc).le
    (S.pos_of_eq_true a b p h.abp).le

/--
A containment derivation made solely from strict determinant signs.

Usually the emitter uses `direct`. The `absorb` constructor supports cells
where the convenient certificate first places a point in an auxiliary
triangle and then absorbs that triangle into a hull-fan triangle.
-/
inductive InTriBySigns {v : Configuration}
    (S : StrictSignData v) :
    Fin 8 → Fin 8 → Fin 8 → Fin 8 → Prop
  | direct {p a b c}
      (h : DirectInTriSigns S p a b c) :
      InTriBySigns S p a b c
  | absorb {x p q r a b c}
      (hx : InTriBySigns S x p q r)
      (hp : InTriBySigns S p a b c)
      (hq : InTriBySigns S q a b c)
      (hr : InTriBySigns S r a b c) :
      InTriBySigns S x a b c

lemma InTriBySigns.sound
    {v : Configuration} {S : StrictSignData v}
    {p a b c : Fin 8}
    (h : InTriBySigns S p a b c) :
    InTri (v p) (v a) (v b) (v c) := by
  induction h with
  | direct h =>
      exact h.sound
  | absorb hx hp hq hr ihx ihp ihq ihr =>
      exact inTri_absorb ihx ihp ihq ihr

/--
The declared list is the CCW hull cycle determined by the realized strict
sign cell.

`cyclic` verifies strict convex position. `covers` verifies that every
non-cycle point belongs to a fan triangle, using only signed-containment
derivations.
-/
structure HullCycleOf {v : Configuration}
    (S : StrictSignData v) (d : HullCycleData) : Prop where
  nodup : d.cycle.Nodup
  cyclic : ∀ i j k : Fin d.cycle.length,
    i < j → j < k →
      S.ccw (d.get i) (d.get j) (d.get k) = true
  covers : ∀ p : Fin 8, p ∉ Set.range d.get →
    ∃ i j : Fin d.cycle.length,
      (0 : Fin d.cycle.length) < i ∧
      i < j ∧
      InTriBySigns S p (d.get 0) (d.get i) (d.get j)

lemma HullCycleOf.injective
    {v : Configuration} {S : StrictSignData v}
    {d : HullCycleData}
    (h : HullCycleOf S d) :
    Function.Injective d.get :=
  h.nodup.injective_get

lemma HullCycleOf.strictCyclicPos
    {v : Configuration} {S : StrictSignData v}
    {d : HullCycleData}
    (h : HullCycleOf S d) :
    StrictCyclicPos d.get v := by
  constructor
  · intro i j k hij hjk
    exact
      (S.pos_of_eq_true _ _ _
        (h.cyclic i j k hij hjk)).le
  · intro i j k hij hjk
    exact
      (S.pos_of_eq_true _ _ _
        (h.cyclic i j k hij hjk)).ne'

lemma HullCycleOf.fanCovers
    {v : Configuration} {S : StrictSignData v}
    {d : HullCycleData}
    (h : HullCycleOf S d) :
    FanCovers v d.get := by
  intro p hp
  obtain ⟨i, j, hi, hij, hs⟩ := h.covers p hp
  exact ⟨i, j, hi, hij, hs.sound⟩

/--
The engine's declared fan is the doubled hull area in the `IsHullArea` sense.

All hull sizes 3 through 8 are handled. The six branches only transport the
same list-indexed fan to the fixed arities of the existing constructors; no
geometric choice or trusted hull computation occurs here.
-/
theorem HullCycleOf.isHullArea
    {v : Configuration} {S : StrictSignData v}
    {d : HullCycleData}
    (h : HullCycleOf S d) :
    IsHullArea v (d.fanExpr v) := by
  have hge : 3 ≤ d.cycle.length :=
    d.length_ge_three
  have hle : d.cycle.length ≤ 8 :=
    d.length_le_eight
  have hsizes :
      d.cycle.length = 3 ∨
      d.cycle.length = 4 ∨
      d.cycle.length = 5 ∨
      d.cycle.length = 6 ∨
      d.cycle.length = 7 ∨
      d.cycle.length = 8 := by
    omega
  rcases hsizes with h3 | h4 | h5 | h6 | h7 | h8
  · exact IsHullArea.hull3 (d.castGet h3)
      (HullCycleData.castGet_injective d h3 h.nodup)
      (HullCycleData.strictCyclicPos_cast
        d h3 h.strictCyclicPos)
      (HullCycleData.fanCovers_cast
        d h3 h.fanCovers)
      (HullCycleData.fanSum_castGet d h3).symm
  · exact IsHullArea.hull4 (d.castGet h4)
      (HullCycleData.castGet_injective d h4 h.nodup)
      (HullCycleData.strictCyclicPos_cast
        d h4 h.strictCyclicPos)
      (HullCycleData.fanCovers_cast
        d h4 h.fanCovers)
      (HullCycleData.fanSum_castGet d h4).symm
  · exact IsHullArea.hull5 (d.castGet h5)
      (HullCycleData.castGet_injective d h5 h.nodup)
      (HullCycleData.strictCyclicPos_cast
        d h5 h.strictCyclicPos)
      (HullCycleData.fanCovers_cast
        d h5 h.fanCovers)
      (HullCycleData.fanSum_castGet d h5).symm
  · exact IsHullArea.hull6 (d.castGet h6)
      (HullCycleData.castGet_injective d h6 h.nodup)
      (HullCycleData.strictCyclicPos_cast
        d h6 h.strictCyclicPos)
      (HullCycleData.fanCovers_cast
        d h6 h.fanCovers)
      (HullCycleData.fanSum_castGet d h6).symm
  · exact IsHullArea.hull7 (d.castGet h7)
      (HullCycleData.castGet_injective d h7 h.nodup)
      (HullCycleData.strictCyclicPos_cast
        d h7 h.strictCyclicPos)
      (HullCycleData.fanCovers_cast
        d h7 h.fanCovers)
      (HullCycleData.fanSum_castGet d h7).symm
  · exact IsHullArea.hull8 (d.castGet h8)
      (HullCycleData.castGet_injective d h8 h.nodup)
      (HullCycleData.strictCyclicPos_cast
        d h8 h.strictCyclicPos)
      (HullCycleData.fanCovers_cast
        d h8 h.fanCovers)
      (HullCycleData.fanSum_castGet d h8).symm

/-!
The dominant six- and seven-hull expressions are exposed explicitly below.
The boundary identities are the polygonal versions of `split3`/`split4`;
after expanding `sig`, they are pure ring identities. The same pattern works
for sizes 3, 4, 5, and 8, while `HullCycleOf.isHullArea` already covers those
arities without requiring separate expanded formulas.
-/

lemma fanSum_six
    (v : Configuration) (c : Fin 6 → Fin 8) :
    fanSum v c =
      sig (v (c 0)) (v (c 1)) (v (c 2)) +
      sig (v (c 0)) (v (c 2)) (v (c 3)) +
      sig (v (c 0)) (v (c 3)) (v (c 4)) +
      sig (v (c 0)) (v (c 4)) (v (c 5)) := by
  have hp : fanPairs 6 =
      {((1 : Fin 6), (2 : Fin 6)),
       (2, 3), (3, 4), (4, 5)} := by
    decide
  rw [fanSum, hp]
  simp
  ring

lemma fanSum_seven
    (v : Configuration) (c : Fin 7 → Fin 8) :
    fanSum v c =
      sig (v (c 0)) (v (c 1)) (v (c 2)) +
      sig (v (c 0)) (v (c 2)) (v (c 3)) +
      sig (v (c 0)) (v (c 3)) (v (c 4)) +
      sig (v (c 0)) (v (c 4)) (v (c 5)) +
      sig (v (c 0)) (v (c 5)) (v (c 6)) := by
  have hp : fanPairs 7 =
      {((1 : Fin 7), (2 : Fin 7)),
       (2, 3), (3, 4), (4, 5), (5, 6)} := by
    decide
  rw [fanSum, hp]
  simp
  ring

lemma fanSum_six_eq_boundary
    (v : Configuration) (c : Fin 6 → Fin 8)
    (o : ℝ × ℝ) :
    fanSum v c =
      sig o (v (c 0)) (v (c 1)) +
      sig o (v (c 1)) (v (c 2)) +
      sig o (v (c 2)) (v (c 3)) +
      sig o (v (c 3)) (v (c 4)) +
      sig o (v (c 4)) (v (c 5)) +
      sig o (v (c 5)) (v (c 0)) := by
  rw [fanSum_six]
  simp only [sig]
  ring

lemma fanSum_seven_eq_boundary
    (v : Configuration) (c : Fin 7 → Fin 8)
    (o : ℝ × ℝ) :
    fanSum v c =
      sig o (v (c 0)) (v (c 1)) +
      sig o (v (c 1)) (v (c 2)) +
      sig o (v (c 2)) (v (c 3)) +
      sig o (v (c 3)) (v (c 4)) +
      sig o (v (c 4)) (v (c 5)) +
      sig o (v (c 5)) (v (c 6)) +
      sig o (v (c 6)) (v (c 0)) := by
  rw [fanSum_seven]
  simp only [sig]
  ring

end Heilbronn8
