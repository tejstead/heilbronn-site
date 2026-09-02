import Mathlib.Data.Fintype.Defs
import Heilbronn8.Survivors.Join.HullSixVariationExclusion

/-!
# Sign blocks cut out on a strict six-cycle

A line meeting the interior of a strictly convex polygon cuts its vertices
into two nonempty cyclic intervals.  For six vertices this has a particularly
small formal proof.  Four vertices in cyclic order cannot have alternating
line-level signs, by one affine-dependence identity.  A closed Boolean check
then reduces every remaining mixed sign word to a rotation of a block of
length one, two, or three, after possibly reversing the line orientation.

The finite check has only 64 input words.  It is kept separate from the real
geometry so downstream chamber arguments can consume a small normal form
without carrying a large geometric case split.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Heilbronn8

/-! ## The finite Boolean normal form -/

/-- A Boolean word on six cyclic positions uses both values. -/
def FinSixBoolMixed (word : Fin 6 → Bool) : Prop :=
  ∃ i j : Fin 6, word i ≠ word j

/-- There is no alternating subsequence at four increasing positions.

If the values at the first and third positions agree, and the values at the
second and fourth positions agree, convex geometry forces the two common
values to agree as well. -/
def FinSixBoolNoOrderedAlternation (word : Fin 6 → Bool) : Prop :=
  ∀ i0 i1 i2 i3 : Fin 6,
    i0 < i1 → i1 < i2 → i2 < i3 →
    word i0 = word i2 → word i1 = word i3 → word i0 = word i1

/-- The normalized bit at offset `i`.  The parameter `last` is the last
position of the short block, so its values zero, one, and two encode block
lengths one, two, and three. -/
def normalizedFinSixBlockBit
    (flip : Bool) (last : Fin 3) (i : Fin 6) : Bool :=
  if flip then !(decide (i.val ≤ last.val))
  else decide (i.val ≤ last.val)

/-- A mixed six-bit word with no ordered alternating quadruple is a pair of
nonempty cyclic blocks.  Rotation puts the shorter block first; complementing
the word if necessary makes its length one, two, or three.

This is a closed finite theorem, checked by kernel reduction rather than by a
generated certificate. -/
private theorem finSix_boolBlock_normalForm_closed :
    ∀ word : Fin 6 → Bool,
      FinSixBoolMixed word →
      FinSixBoolNoOrderedAlternation word →
      ∃ rotation : Fin 6, ∃ flip : Bool, ∃ last : Fin 3,
        ∀ i : Fin 6,
          word (rotation + i) = normalizedFinSixBlockBit flip last i := by
  intro word
  let b0 : Bool := word 0
  let b1 : Bool := word 1
  let b2 : Bool := word 2
  let b3 : Bool := word 3
  let b4 : Bool := word 4
  let b5 : Bool := word 5
  have hword : word = fun i =>
      match i.val with
      | 0 => b0
      | 1 => b1
      | 2 => b2
      | 3 => b3
      | 4 => b4
      | _ => b5 := by
    funext i
    fin_cases i <;> rfl
  rw [hword]
  cases b0 <;> cases b1 <;> cases b2 <;>
    cases b3 <;> cases b4 <;> cases b5 <;>
      (unfold FinSixBoolMixed FinSixBoolNoOrderedAlternation; decide)

/-- Reusable form of the closed six-bit classification. -/
theorem finSix_boolBlock_normalForm
    (word : Fin 6 → Bool)
    (hmixed : FinSixBoolMixed word)
    (hnoAlt : FinSixBoolNoOrderedAlternation word) :
    ∃ rotation : Fin 6, ∃ flip : Bool, ∃ last : Fin 3,
      ∀ i : Fin 6,
        word (rotation + i) = normalizedFinSixBlockBit flip last i :=
  finSix_boolBlock_normalForm_closed word hmixed hnoAlt

/-! ## The geometric no-alternation identity -/

/-- Affine dependence of four planar points, tested against the affine line
functional `x |-> sig p q x`. -/
lemma convexFour_lineLevel_balance
    (p q a b c d : Real × Real) :
    sig b c d * sig p q a + sig a b d * sig p q c =
      sig a c d * sig p q b + sig a b c * sig p q d := by
  simp only [sig]
  ring

/-- Four increasing vertices of a strict cyclic configuration cannot have
alternating signs with respect to any oriented line. -/
theorem StrictCyclicPos.no_ordered_lineLevel_alternation
    {v : Configuration} {cycle : Fin 6 → Fin 8}
    (hcycle : StrictCyclicPos cycle v) (p q : Real × Real)
    (i0 i1 i2 i3 : Fin 6)
    (h01 : i0 < i1) (h12 : i1 < i2) (h23 : i2 < i3) :
    ¬ (
      (0 < sig p q (v (cycle i0)) ∧
        sig p q (v (cycle i1)) < 0 ∧
        0 < sig p q (v (cycle i2)) ∧
        sig p q (v (cycle i3)) < 0) ∨
      (sig p q (v (cycle i0)) < 0 ∧
        0 < sig p q (v (cycle i1)) ∧
        sig p q (v (cycle i2)) < 0 ∧
        0 < sig p q (v (cycle i3)))) := by
  intro halternating
  have h02 : i0 < i2 := lt_trans h01 h12
  have h13 : i1 < i3 := lt_trans h12 h23
  have habc := hcycle.pos i0 i1 i2 h01 h12
  have habd := hcycle.pos i0 i1 i3 h01 h13
  have hacd := hcycle.pos i0 i2 i3 h02 h23
  have hbcd := hcycle.pos i1 i2 i3 h12 h23
  have hbalance := convexFour_lineLevel_balance p q
    (v (cycle i0)) (v (cycle i1)) (v (cycle i2)) (v (cycle i3))
  rcases halternating with hsigns | hsigns
  · have hl0 : 0 <
        sig (v (cycle i1)) (v (cycle i2)) (v (cycle i3)) *
          sig p q (v (cycle i0)) := mul_pos hbcd hsigns.1
    have hl1 : 0 <
        sig (v (cycle i0)) (v (cycle i1)) (v (cycle i3)) *
          sig p q (v (cycle i2)) := mul_pos habd hsigns.2.2.1
    have hr0 :
        sig (v (cycle i0)) (v (cycle i2)) (v (cycle i3)) *
          sig p q (v (cycle i1)) < 0 :=
      mul_neg_of_pos_of_neg hacd hsigns.2.1
    have hr1 :
        sig (v (cycle i0)) (v (cycle i1)) (v (cycle i2)) *
          sig p q (v (cycle i3)) < 0 :=
      mul_neg_of_pos_of_neg habc hsigns.2.2.2
    linarith
  · have hl0 :
        sig (v (cycle i1)) (v (cycle i2)) (v (cycle i3)) *
          sig p q (v (cycle i0)) < 0 :=
      mul_neg_of_pos_of_neg hbcd hsigns.1
    have hl1 :
        sig (v (cycle i0)) (v (cycle i1)) (v (cycle i3)) *
          sig p q (v (cycle i2)) < 0 :=
      mul_neg_of_pos_of_neg habd hsigns.2.2.1
    have hr0 : 0 <
        sig (v (cycle i0)) (v (cycle i2)) (v (cycle i3)) *
          sig p q (v (cycle i1)) := mul_pos hacd hsigns.2.1
    have hr1 : 0 <
        sig (v (cycle i0)) (v (cycle i1)) (v (cycle i2)) *
          sig p q (v (cycle i3)) := mul_pos habc hsigns.2.2.2
    linarith

/-! ## From real line levels to a normalized block -/

/-- Reversing the line orientation when `flip` is true. -/
def orientedFinSixLevel
    (levels : Fin 6 → Real) (flip : Bool) (i : Fin 6) : Real :=
  if flip then -levels i else levels i

/-- The real-valued normal form consumed by the cross-chord chamber proofs.
It is an existential proposition so extracting finite normalization witnesses
never requires eliminating a proof into data. -/
def FinSixLineSignBlock (levels : Fin 6 → Real) : Prop :=
  ∃ rotation : Fin 6, ∃ flip : Bool, ∃ last : Fin 3,
    (∀ i : Fin 6, i.val ≤ last.val →
      0 < orientedFinSixLevel levels flip (rotation + i)) ∧
    (∀ i : Fin 6, last.val < i.val →
      orientedFinSixLevel levels flip (rotation + i) < 0)

private lemma lt_zero_of_not_pos_of_ne {x : Real}
    (hne : x ≠ 0) (hnot : ¬ 0 < x) : x < 0 :=
  lt_of_le_of_ne (le_of_not_gt hnot) hne

/-- Strict cyclicity rules out Boolean alternation for the six line-level
signs. -/
theorem StrictCyclicPos.lineSignBits_noOrderedAlternation
    {v : Configuration} {cycle : Fin 6 → Fin 8}
    (hcycle : StrictCyclicPos cycle v) (p q : Real × Real)
    (hne : ∀ i : Fin 6, sig p q (v (cycle i)) ≠ 0) :
    FinSixBoolNoOrderedAlternation
      (fun i => decide (0 < sig p q (v (cycle i)))) := by
  intro i0 i1 i2 i3 h01 h12 h23 hword02 hword13
  let level : Fin 6 → Real := fun i => sig p q (v (cycle i))
  change decide (0 < level i0) = decide (0 < level i2) at hword02
  change decide (0 < level i1) = decide (0 < level i3) at hword13
  change decide (0 < level i0) = decide (0 < level i1)
  have hforbid := hcycle.no_ordered_lineLevel_alternation
    p q i0 i1 i2 i3 h01 h12 h23
  by_cases h0 : 0 < level i0
  · have hb0 : decide (0 < level i0) = true := decide_eq_true h0
    have hb2 : decide (0 < level i2) = true := by
      rw [← hword02]
      exact hb0
    cases hb1 : decide (0 < level i1) with
    | true =>
        simpa [hb0, hb1]
    | false =>
        have hb3 : decide (0 < level i3) = false := by
          rw [← hword13]
          exact hb1
        have h1neg : level i1 < 0 :=
          lt_zero_of_not_pos_of_ne (hne i1)
            (of_decide_eq_false hb1)
        have h3neg : level i3 < 0 :=
          lt_zero_of_not_pos_of_ne (hne i3)
            (of_decide_eq_false hb3)
        have h2pos : 0 < level i2 := of_decide_eq_true hb2
        exact False.elim
          (hforbid (Or.inl ⟨h0, h1neg, h2pos, h3neg⟩))
  · have h0neg : level i0 < 0 :=
      lt_zero_of_not_pos_of_ne (hne i0) h0
    have hb0 : decide (0 < level i0) = false := decide_eq_false h0
    have hb2 : decide (0 < level i2) = false := by
      rw [← hword02]
      exact hb0
    cases hb1 : decide (0 < level i1) with
    | false =>
        simpa [hb0, hb1]
    | true =>
        have hb3 : decide (0 < level i3) = true := by
          rw [← hword13]
          exact hb1
        have h1pos : 0 < level i1 := of_decide_eq_true hb1
        have h2neg : level i2 < 0 :=
          lt_zero_of_not_pos_of_ne (hne i2)
            (of_decide_eq_false hb2)
        have h3pos : 0 < level i3 := of_decide_eq_true hb3
        exact False.elim
          (hforbid (Or.inr ⟨h0neg, h1pos, h2neg, h3pos⟩))

/-- The main geometric sign-block theorem.  The only non-convexity inputs are
that all six levels are nonzero and that both signs occur. -/
theorem strictCyclicPos_six_lineSignBlock
    {v : Configuration} {cycle : Fin 6 → Fin 8}
    (hcycle : StrictCyclicPos cycle v) (p q : Real × Real)
    (hne : ∀ i : Fin 6, sig p q (v (cycle i)) ≠ 0)
    (hpos : ∃ i : Fin 6, 0 < sig p q (v (cycle i)))
    (hneg : ∃ i : Fin 6, sig p q (v (cycle i)) < 0) :
    FinSixLineSignBlock (fun i => sig p q (v (cycle i))) := by
  let levels : Fin 6 → Real := fun i => sig p q (v (cycle i))
  let word : Fin 6 → Bool := fun i => decide (0 < levels i)
  have hmixed : FinSixBoolMixed word := by
    obtain ⟨i, hi⟩ := hpos
    obtain ⟨j, hj⟩ := hneg
    refine ⟨i, j, ?_⟩
    have hit : word i = true := decide_eq_true hi
    have hjf : word j = false :=
      decide_eq_false (not_lt_of_ge hj.le)
    rw [hit, hjf]
    decide
  have hnoAlt : FinSixBoolNoOrderedAlternation word := by
    exact hcycle.lineSignBits_noOrderedAlternation p q hne
  obtain ⟨rotation, flip, last, hpattern⟩ :=
    finSix_boolBlock_normalForm word hmixed hnoAlt
  cases flip with
  | false =>
      refine ⟨rotation, false, last, ?_, ?_⟩
      · intro i hi
        have hbit := hpattern i
        have htrue : word (rotation + i) = true := by
          simpa [normalizedFinSixBlockBit, hi] using hbit
        change 0 < levels (rotation + i)
        exact of_decide_eq_true htrue
      · intro i hi
        have hnot : ¬ i.val ≤ last.val := Nat.not_le.mpr hi
        have hbit := hpattern i
        have hfalse : word (rotation + i) = false := by
          simpa [normalizedFinSixBlockBit, hnot] using hbit
        change levels (rotation + i) < 0
        exact lt_zero_of_not_pos_of_ne (hne (rotation + i))
          (of_decide_eq_false hfalse)
  | true =>
      refine ⟨rotation, true, last, ?_, ?_⟩
      · intro i hi
        have hbit := hpattern i
        have hfalse : word (rotation + i) = false := by
          simpa [normalizedFinSixBlockBit, hi] using hbit
        have hnegLevel : levels (rotation + i) < 0 :=
          lt_zero_of_not_pos_of_ne (hne (rotation + i))
            (of_decide_eq_false hfalse)
        change 0 < -levels (rotation + i)
        linarith
      · intro i hi
        have hnot : ¬ i.val ≤ last.val := Nat.not_le.mpr hi
        have hbit := hpattern i
        have htrue : word (rotation + i) = true := by
          simpa [normalizedFinSixBlockBit, hnot] using hbit
        have hposLevel : 0 < levels (rotation + i) :=
          of_decide_eq_true htrue
        change -levels (rotation + i) < 0
        linarith

/-- Hull containment supplies both line-level signs.  Only one contained
point is needed for this fact because the oriented line passes through both
`p` and `q`. -/
theorem strictCyclicPos_six_lineSignBlock_of_fanCovers
    {v : Configuration} {cycle : Fin 6 → Fin 8}
    (hcycle : StrictCyclicPos cycle v) (hcover : FanCovers v cycle)
    (p q : Fin 8) (hpOutside : p ∉ Set.range cycle)
    (hne : ∀ i : Fin 6,
      sig (v p) (v q) (v (cycle i)) ≠ 0) :
    FinSixLineSignBlock
      (fun i => sig (v p) (v q) (v (cycle i))) := by
  obtain ⟨i, j, _hi, _hij, htri⟩ := hcover p hpOutside
  have hstraddle := lineLevels_straddle_of_inTri
    (v p) (v q) (v (cycle 0)) (v (cycle i)) (v (cycle j)) htri
  have hneg : ∃ k : Fin 6,
      sig (v p) (v q) (v (cycle k)) < 0 := by
    rcases hstraddle.1 with h | h | h
    · exact ⟨0, lt_of_le_of_ne h (hne 0)⟩
    · exact ⟨i, lt_of_le_of_ne h (hne i)⟩
    · exact ⟨j, lt_of_le_of_ne h (hne j)⟩
  have hpos : ∃ k : Fin 6,
      0 < sig (v p) (v q) (v (cycle k)) := by
    rcases hstraddle.2 with h | h | h
    · exact ⟨0, lt_of_le_of_ne h (Ne.symm (hne 0))⟩
    · exact ⟨i, lt_of_le_of_ne h (Ne.symm (hne i))⟩
    · exact ⟨j, lt_of_le_of_ne h (Ne.symm (hne j))⟩
  exact strictCyclicPos_six_lineSignBlock hcycle
    (v p) (v q) hne hpos hneg

/-- The compact h=6 residual already contains exactly the hypotheses of the
sign-block theorem. -/
theorem HullSixCompactCrossChordResidual.lineSignBlock
    {v : Configuration} {cycle : Fin 6 → Fin 8} {p q : Fin 8}
    (h : HullSixCompactCrossChordResidual v cycle p q) :
    FinSixLineSignBlock
      (fun i => sig (v p) (v q) (v (cycle i))) := by
  apply strictCyclicPos_six_lineSignBlock_of_fanCovers
    h.cycle_strict h.cycle_covers p q h.p_outside
  intro i hzero
  have hfloor := h.lineLevel_floor i
  rw [hzero, abs_zero] at hfloor
  linarith [h.minTri_pos]

end Heilbronn8

