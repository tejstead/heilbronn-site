import Heilbronn8.TriHull.HullFiveOccupancyCombinatorics
import Heilbronn8.TriHull.Core

/-!
# Geometric profiles for the eleven pentagon regions

This module is the point-level half of the hull-five occupancy dispatcher.
For each cyclic anchor of a strict convex pentagon, a point is assumed to be
strictly covered by one of the three triangles in the standard anchored fan.
The chosen five fan cells automatically satisfy the shared-ear relation, and
hence are one of the eleven profiles in
`HullFiveOccupancyCombinatorics.lean`.

The later labelled-configuration adapter has only two jobs:

* obtain the five strict fan covers from its `HullCycleOf` certificate, and
* prove `HullFiveStrictCyclic` for the five cyclic rotations of the cycle.

No retained-word or box data enters this lemma.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

lemma inTriStrict_rotate_hullFive
    {p a b c : ℝ × ℝ} (h : InTriStrict p a b c) :
    InTriStrict p b c a := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hp⟩ := h
  refine ⟨y, z, x, hy, hz, hx, by linarith, ?_⟩
  rw [hp]
  module

lemma inTriStrict_rotate2_hullFive
    {p a b c : ℝ × ℝ} (h : InTriStrict p a b c) :
    InTriStrict p c a b :=
  inTriStrict_rotate_hullFive (inTriStrict_rotate_hullFive h)

/-- The cyclic rotation of a displayed five-tuple. -/
def hullFiveRotate (z : Fin 5 → ℝ × ℝ) (a : Fin 5) :
    Fin 5 → ℝ × ℝ :=
  ![z a, z (a + 1), z (a + 2), z (a + 3), z (a + 4)]

/-- All triples through the first point of a displayed five-tuple are
strictly counterclockwise. -/
def StrictAnchoredFive (z : Fin 5 → ℝ × ℝ) : Prop :=
  ∀ i j : Fin 5, (0 : Fin 5) < i → i < j →
    0 < sig (z 0) (z i) (z j)

/-- Strict convexity in every cyclicly rotated presentation. -/
def HullFiveStrictCyclic (z : Fin 5 → ℝ × ℝ) : Prop :=
  ∀ a : Fin 5, StrictAnchoredFive (hullFiveRotate z a)

/-- The three triangles of the fan based at the first displayed point. -/
def InAnchoredFiveFanCell (p : ℝ × ℝ)
    (z : Fin 5 → ℝ × ℝ) (cell : Fin 3) : Prop :=
  InTriStrict p (z 0)
    (![z 1, z 2, z 3] cell)
    (![z 2, z 3, z 4] cell)

/-- Fan-cell membership at a cyclic anchor. -/
def InHullFiveFanCell (p : ℝ × ℝ)
    (z : Fin 5 → ℝ × ℝ)
    (anchor : Fin 5) (cell : Fin 3) : Prop :=
  InAnchoredFiveFanCell p (hullFiveRotate z anchor) cell

/-- Pointwise strict coverage by all five anchored fans. -/
def HullFiveFanCoversPoint (p : ℝ × ℝ)
    (z : Fin 5 → ℝ × ℝ) : Prop :=
  ∀ anchor : Fin 5, ∃ cell : Fin 3,
    InHullFiveFanCell p z anchor cell

/-- The three open triangles in one strict anchored fan are disjoint.  This
specialized form is the one needed by the H300-ear residual: membership in
the first ear forces the finite profile cell to be `0`. -/
lemma hullFiveFanCell_eq_zero_of_mem_zero
    {p : ℝ × ℝ} {z : Fin 5 → ℝ × ℝ}
    (hcyc : HullFiveStrictCyclic z) (anchor : Fin 5)
    (cell : Fin 3)
    (hzero : InHullFiveFanCell p z anchor 0)
    (hcell : InHullFiveFanCell p z anchor cell) :
    cell = 0 := by
  let r : Fin 5 → ℝ × ℝ := hullFiveRotate z anchor
  have hD0 : 0 < sig (r 0) (r 1) (r 2) :=
    hcyc anchor 1 2 (by decide) (by decide)
  have hD1 : 0 < sig (r 0) (r 2) (r 3) :=
    hcyc anchor 2 3 (by decide) (by decide)
  have hD03 : 0 < sig (r 0) (r 2) (r 3) := hD1
  have hD04 : 0 < sig (r 0) (r 2) (r 4) :=
    hcyc anchor 2 4 (by decide) (by decide)
  have hzero' : InTriStrict p (r 0) (r 1) (r 2) := by
    simpa [r, InHullFiveFanCell, InAnchoredFiveFanCell] using hzero
  obtain ⟨_, hzeroDiag, _⟩ := inTriStrict_fan_pos hD0 hzero'
  have hdiagNeg : sig (r 0) (r 2) p < 0 := by
    rw [sig_rotate p (r 2) (r 0),
      sig_rotate (r 2) (r 0) p,
      sig_swap (r 0) p (r 2)] at hzeroDiag
    linarith
  fin_cases cell
  · rfl
  · have hcell' : InTriStrict p (r 0) (r 2) (r 3) := by
      simpa [r, InHullFiveFanCell, InAnchoredFiveFanCell] using hcell
    obtain ⟨_, _, hdiagPos'⟩ := inTriStrict_fan_pos hD1 hcell'
    have hdiagPos : 0 < sig (r 0) (r 2) p := by
      rwa [sig_rotate p (r 0) (r 2)] at hdiagPos'
    linarith
  · have hcell' : InTriStrict p (r 0) (r 3) (r 4) := by
      simpa [r, InHullFiveFanCell, InAnchoredFiveFanCell] using hcell
    obtain ⟨x, y, t, hx, hy, ht, hsum, hp⟩ := hcell'
    have hdiagPos : 0 < sig (r 0) (r 2) p := by
      rw [hp]
      have hid :
          sig (r 0) (r 2)
              (x • r 0 + y • r 3 + t • r 4) =
            y * sig (r 0) (r 2) (r 3) +
              t * sig (r 0) (r 2) (r 4) := by
        simp only [sig, Prod.smul_fst, Prod.smul_snd,
          Prod.fst_add, Prod.snd_add, smul_eq_mul]
        rw [show x = 1 - y - t by linarith]
        ring
      rw [hid]
      exact add_pos (mul_pos hy hD03) (mul_pos ht hD04)
    linarith

/-- The exact strict-interior data used to recover the standard fan cell at
each rotation.  The five boundary rows are positive, and the two anchor
diagonals do not contain the point. -/
def HullFivePointStrictInterior (p : ℝ × ℝ)
    (z : Fin 5 → ℝ × ℝ) : Prop :=
  ∀ anchor : Fin 5,
    let r := hullFiveRotate z anchor
    0 < sig (r 0) (r 1) p ∧
    0 < sig (r 1) (r 2) p ∧
    0 < sig (r 2) (r 3) p ∧
    0 < sig (r 3) (r 4) p ∧
    0 < sig (r 4) (r 0) p ∧
    sig (r 0) (r 2) p ≠ 0 ∧
    sig (r 0) (r 3) p ≠ 0

/-- Nondegeneracy of the seven lines used in each standard fan.  In a
labelled configuration this is an immediate consequence of
`AllTripleSignsStrict`. -/
def HullFivePointLineGeneric (p : ℝ × ℝ)
    (z : Fin 5 → ℝ × ℝ) : Prop :=
  ∀ anchor : Fin 5,
    let r := hullFiveRotate z anchor
    sig (r 0) (r 1) p ≠ 0 ∧
    sig (r 1) (r 2) p ≠ 0 ∧
    sig (r 2) (r 3) p ≠ 0 ∧
    sig (r 3) (r 4) p ≠ 0 ∧
    sig (r 4) (r 0) p ≠ 0 ∧
    sig (r 0) (r 2) p ≠ 0 ∧
    sig (r 0) (r 3) p ≠ 0

private lemma sig_nonneg_on_convexHull_five
    (a b : ℝ × ℝ) (s : Set (ℝ × ℝ))
    (h : ∀ x ∈ s, 0 ≤ sig a b x) :
    ∀ x ∈ convexHull ℝ s, 0 ≤ sig a b x := by
  apply convexHull_min h
  rintro x hx y hy u v hu hv huv
  change 0 ≤ sig a b x at hx
  change 0 ≤ sig a b y at hy
  change 0 ≤ sig a b (u • x + v • y)
  have heq : sig a b (u • x + v • y) =
      u * sig a b x + v * sig a b y := by
    have hthree := sig_affine_fst x y y a b u v 0 (by linarith)
    calc
      sig a b (u • x + v • y) = sig (u • x + v • y) a b :=
        (sig_rotate (u • x + v • y) a b).symm
      _ = u * sig x a b + v * sig y a b := by
        simpa only [zero_smul, add_zero, zero_mul] using hthree
      _ = u * sig a b x + v * sig a b y := by
        rw [sig_rotate x a b, sig_rotate y a b]
  rw [heq]
  exact add_nonneg (mul_nonneg hu hx) (mul_nonneg hv hy)

private lemma anchoredFive_firstEdge_nonneg
    {z : Fin 5 → ℝ × ℝ}
    (hcyc : StrictAnchoredFive z) :
    ∀ k : Fin 5, 0 ≤ sig (z 0) (z 1) (z k) := by
  intro k
  fin_cases k
  · simp [sig]
  · simp [sig]
  · exact (hcyc 1 2 (by decide) (by decide)).le
  · exact (hcyc 1 3 (by decide) (by decide)).le
  · exact (hcyc 1 4 (by decide) (by decide)).le

private lemma hullFiveRotate_covers
    (z : Fin 5 → ℝ × ℝ) (a : Fin 5) :
    ∀ k : Fin 5, ∃ t : Fin 5, hullFiveRotate z a t = z k := by
  intro k
  fin_cases a <;> fin_cases k
  all_goals first
    | exact ⟨0, rfl⟩
    | exact ⟨1, rfl⟩
    | exact ⟨2, rfl⟩
    | exact ⟨3, rfl⟩
    | exact ⟨4, rfl⟩

private lemma hullFiveRotate_edge_one
    (z : Fin 5 → ℝ × ℝ) (p : ℝ × ℝ) (a : Fin 5) :
    sig (hullFiveRotate z a 1) (hullFiveRotate z a 2) p =
      sig (hullFiveRotate z (a + 1) 0)
        (hullFiveRotate z (a + 1) 1) p := by
  fin_cases a <;> rfl

private lemma hullFiveRotate_edge_two
    (z : Fin 5 → ℝ × ℝ) (p : ℝ × ℝ) (a : Fin 5) :
    sig (hullFiveRotate z a 2) (hullFiveRotate z a 3) p =
      sig (hullFiveRotate z (a + 2) 0)
        (hullFiveRotate z (a + 2) 1) p := by
  fin_cases a <;> rfl

private lemma hullFiveRotate_edge_three
    (z : Fin 5 → ℝ × ℝ) (p : ℝ × ℝ) (a : Fin 5) :
    sig (hullFiveRotate z a 3) (hullFiveRotate z a 4) p =
      sig (hullFiveRotate z (a + 3) 0)
        (hullFiveRotate z (a + 3) 1) p := by
  fin_cases a <;> rfl

private lemma hullFiveRotate_edge_four
    (z : Fin 5 → ℝ × ℝ) (p : ℝ × ℝ) (a : Fin 5) :
    sig (hullFiveRotate z a 4) (hullFiveRotate z a 0) p =
      sig (hullFiveRotate z (a + 4) 0)
        (hullFiveRotate z (a + 4) 1) p := by
  fin_cases a <;> rfl

/-- A generic labelled point in the convex hull lies strictly to the left of
all five boundary edges. -/
theorem hullFivePointStrictInterior_of_mem_convexHull
    {p : ℝ × ℝ} {z : Fin 5 → ℝ × ℝ}
    (hcyc : HullFiveStrictCyclic z)
    (hpHull : p ∈ convexHull ℝ (Set.range z))
    (hgeneric : HullFivePointLineGeneric p z) :
    HullFivePointStrictInterior p z := by
  have hedgeNonneg (a : Fin 5) :
      0 ≤ sig (hullFiveRotate z a 0) (hullFiveRotate z a 1) p := by
    apply sig_nonneg_on_convexHull_five _ _ (Set.range z) _ p hpHull
    rintro _ ⟨k, rfl⟩
    obtain ⟨t, ht⟩ := hullFiveRotate_covers z a k
    rw [← ht]
    exact anchoredFive_firstEdge_nonneg (hcyc a) t
  have hedgePos (a : Fin 5) :
      0 < sig (hullFiveRotate z a 0) (hullFiveRotate z a 1) p :=
    lt_of_le_of_ne (hedgeNonneg a) (Ne.symm (hgeneric a).1)
  intro a
  refine ⟨hedgePos a, ?_, ?_, ?_, ?_,
    (hgeneric a).2.2.2.2.2.1, (hgeneric a).2.2.2.2.2.2⟩
  · rw [hullFiveRotate_edge_one]
    exact hedgePos (a + 1)
  · rw [hullFiveRotate_edge_two]
    exact hedgePos (a + 2)
  · rw [hullFiveRotate_edge_three]
    exact hedgePos (a + 3)
  · rw [hullFiveRotate_edge_four]
    exact hedgePos (a + 4)

/-- Converse to `inTriStrict_fan_pos`, in the orientation used by the
pentagon fan adapter. -/
lemma inTriStrict_of_positive_fan
    {p a b c : ℝ × ℝ}
    (hD : 0 < sig a b c)
    (h1 : 0 < sig p b c) (h2 : 0 < sig a p c)
    (h3 : 0 < sig a b p) :
    InTriStrict p a b c := by
  have hDne : sig a b c ≠ 0 := ne_of_gt hD
  have hsum :
      sig p b c + sig a p c + sig a b p = sig a b c := by
    simp only [sig]
    ring
  refine ⟨sig p b c / sig a b c,
    sig a p c / sig a b c,
    sig a b p / sig a b c,
    div_pos h1 hD, div_pos h2 hD, div_pos h3 hD, ?_, ?_⟩
  · rw [← add_div, ← add_div, hsum, div_self hDne]
  · have hx1 :
        p.1 * sig a b c =
          sig p b c * a.1 + sig a p c * b.1 + sig a b p * c.1 := by
      simp only [sig]
      ring
    have hx2 :
        p.2 * sig a b c =
          sig p b c * a.2 + sig a p c * b.2 + sig a b p * c.2 := by
      simp only [sig]
      ring
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      linarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      linarith

private lemma anchoredFiveFanCell_exists
    {p : ℝ × ℝ} {z : Fin 5 → ℝ × ℝ}
    (hcyc : StrictAnchoredFive z)
    (hboundary :
      0 < sig (z 0) (z 1) p ∧
      0 < sig (z 1) (z 2) p ∧
      0 < sig (z 2) (z 3) p ∧
      0 < sig (z 3) (z 4) p ∧
      0 < sig (z 4) (z 0) p)
    (hdiag : sig (z 0) (z 2) p ≠ 0 ∧
      sig (z 0) (z 3) p ≠ 0) :
    ∃ cell : Fin 3, InAnchoredFiveFanCell p z cell := by
  rcases hboundary with ⟨h01, h12, h23, h34, h40⟩
  rcases hdiag with ⟨hne02, hne03⟩
  have h012 := hcyc 1 2 (by decide) (by decide)
  have h023 := hcyc 2 3 (by decide) (by decide)
  have h034 := hcyc 3 4 (by decide) (by decide)
  rcases lt_or_gt_of_ne hne02 with h02 | h02
  · refine ⟨0, ?_⟩
    change InTriStrict p (z 0) (z 1) (z 2)
    apply inTriStrict_of_positive_fan h012
    · have heq : sig p (z 1) (z 2) = sig (z 1) (z 2) p := by
        simp only [sig]
        ring
      linarith
    · have heq : sig (z 0) p (z 2) = -sig (z 0) (z 2) p := by
        simp only [sig]
        ring
      linarith
    · exact h01
  · rcases lt_or_gt_of_ne hne03 with h03 | h03
    · refine ⟨1, ?_⟩
      change InTriStrict p (z 0) (z 2) (z 3)
      apply inTriStrict_of_positive_fan h023
      · have heq : sig p (z 2) (z 3) = sig (z 2) (z 3) p := by
          simp only [sig]
          ring
        linarith
      · have heq : sig (z 0) p (z 3) = -sig (z 0) (z 3) p := by
          simp only [sig]
          ring
        linarith
      · exact h02
    · refine ⟨2, ?_⟩
      change InTriStrict p (z 0) (z 3) (z 4)
      apply inTriStrict_of_positive_fan h034
      · have heq : sig p (z 3) (z 4) = sig (z 3) (z 4) p := by
          simp only [sig]
          ring
        linarith
      · have heq : sig (z 0) p (z 4) = sig (z 4) (z 0) p := by
          simp only [sig]
          ring
        linarith
      · exact h03

/-- Boundary halfplanes plus diagonal genericity construct all five strict
fan covers. -/
theorem hullFiveFanCoversPoint_of_strictInterior
    {p : ℝ × ℝ} {z : Fin 5 → ℝ × ℝ}
    (hcyc : HullFiveStrictCyclic z)
    (hinside : HullFivePointStrictInterior p z) :
    HullFiveFanCoversPoint p z := by
  intro anchor
  have h := hinside anchor
  exact anchoredFiveFanCell_exists (hcyc anchor)
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
    ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private lemma inTriStrict_external_right_neg
    {p A B C D : ℝ × ℝ}
    (hABD : 0 < sig A B D) (hACD : 0 < sig A C D)
    (hp : InTriStrict p A B C) :
    sig A D p < 0 := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, rfl⟩ := hp
  rw [← sig_rotate (x • A + y • B + z • C) A D,
    sig_affine_fst A B C A D x y z hsum]
  have hBAD : sig B A D = -sig A B D := by
    simp only [sig]
    ring
  have hCAD : sig C A D = -sig A C D := by
    simp only [sig]
    ring
  have hAAD : sig A A D = 0 := by
    simp [sig]
  rw [hAAD, hBAD, hCAD]
  simp only [mul_zero, zero_add]
  nlinarith

private lemma inTriStrict_external_left_pos
    {p A C D E : ℝ × ℝ}
    (hACD : 0 < sig A C D) (hACE : 0 < sig A C E)
    (hp : InTriStrict p A D E) :
    0 < sig A C p := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, rfl⟩ := hp
  rw [← sig_rotate (x • A + y • D + z • E) A C,
    sig_affine_fst A D E A C x y z hsum]
  have hDAC : sig D A C = sig A C D := by
    simp only [sig]
    ring
  have hEAC : sig E A C = sig A C E := by
    simp only [sig]
    ring
  have hAAC : sig A A C = 0 := by
    simp [sig]
  rw [hAAC, hDAC, hEAC]
  simp only [mul_zero, zero_add]
  nlinarith

/-- The two anchor diagonals have sign patterns `--`, `+-`, and `++` in
fan cells `0`, `1`, and `2`, respectively. -/
lemma inAnchoredFiveFanCell_diagonalSigns
    {p : ℝ × ℝ} {z : Fin 5 → ℝ × ℝ}
    (hcyc : StrictAnchoredFive z) {cell : Fin 3}
    (hcell : InAnchoredFiveFanCell p z cell) :
    match cell with
    | 0 => sig (z 0) (z 2) p < 0 ∧ sig (z 0) (z 3) p < 0
    | 1 => 0 < sig (z 0) (z 2) p ∧ sig (z 0) (z 3) p < 0
    | 2 => 0 < sig (z 0) (z 2) p ∧ 0 < sig (z 0) (z 3) p := by
  have h012 := hcyc 1 2 (by decide) (by decide)
  have h013 := hcyc 1 3 (by decide) (by decide)
  have h023 := hcyc 2 3 (by decide) (by decide)
  have h024 := hcyc 2 4 (by decide) (by decide)
  have h034 := hcyc 3 4 (by decide) (by decide)
  fin_cases cell
  · change InTriStrict p (z 0) (z 1) (z 2) at hcell
    obtain ⟨_, hp20, _⟩ := inTriStrict_fan_pos h012 hcell
    have h02 : sig (z 0) (z 2) p < 0 := by
      have heq : sig p (z 2) (z 0) = -sig (z 0) (z 2) p := by
        simp only [sig]
        ring
      nlinarith
    exact ⟨h02, inTriStrict_external_right_neg h013 h023 hcell⟩
  · change InTriStrict p (z 0) (z 2) (z 3) at hcell
    obtain ⟨_, hp30, hp02⟩ := inTriStrict_fan_pos h023 hcell
    have h03 : sig (z 0) (z 3) p < 0 := by
      have heq : sig p (z 3) (z 0) = -sig (z 0) (z 3) p := by
        simp only [sig]
        ring
      nlinarith
    have h02 : 0 < sig (z 0) (z 2) p := by
      have heq : sig p (z 0) (z 2) = sig (z 0) (z 2) p := by
        simp only [sig]
        ring
      nlinarith
    exact ⟨h02, h03⟩
  · change InTriStrict p (z 0) (z 3) (z 4) at hcell
    obtain ⟨_, _, hp03⟩ := inTriStrict_fan_pos h034 hcell
    have h03 : 0 < sig (z 0) (z 3) p := by
      have heq : sig p (z 0) (z 3) = sig (z 0) (z 3) p := by
        simp only [sig]
        ring
      nlinarith
    exact ⟨inTriStrict_external_left_pos h023 h024 hcell, h03⟩

lemma inAnchoredFiveFanCell_eq_zero_of_first_neg
    {p : ℝ × ℝ} {z : Fin 5 → ℝ × ℝ}
    (hcyc : StrictAnchoredFive z) {cell : Fin 3}
    (hcell : InAnchoredFiveFanCell p z cell)
    (hneg : sig (z 0) (z 2) p < 0) :
    cell = 0 := by
  have hs := inAnchoredFiveFanCell_diagonalSigns hcyc hcell
  fin_cases cell
  · rfl
  · exfalso
    exact (not_lt_of_ge hs.1.le) hneg
  · exfalso
    exact (not_lt_of_ge hs.1.le) hneg

lemma inAnchoredFiveFanCell_eq_two_of_second_pos
    {p : ℝ × ℝ} {z : Fin 5 → ℝ × ℝ}
    (hcyc : StrictAnchoredFive z) {cell : Fin 3}
    (hcell : InAnchoredFiveFanCell p z cell)
    (hpos : 0 < sig (z 0) (z 3) p) :
    cell = 2 := by
  have hs := inAnchoredFiveFanCell_diagonalSigns hcyc hcell
  fin_cases cell
  · exfalso
    exact (not_lt_of_ge hpos.le) hs.2
  · exfalso
    exact (not_lt_of_ge hpos.le) hs.2
  · rfl

private lemma hullFiveRotate_add_two_zero
    (z : Fin 5 → ℝ × ℝ) (a : Fin 5) :
    hullFiveRotate z (a + 2) 0 = hullFiveRotate z a 2 := by
  fin_cases a <;> rfl

private lemma hullFiveRotate_add_two_three
    (z : Fin 5 → ℝ × ℝ) (a : Fin 5) :
    hullFiveRotate z (a + 2) 3 = hullFiveRotate z a 0 := by
  fin_cases a <;> rfl

/-- A strict fan cover gives one of the eleven geometric point regions. -/
theorem hullFivePointRegion_of_fanCovers
    {p : ℝ × ℝ} {z : Fin 5 → ℝ × ℝ}
    (hcyc : HullFiveStrictCyclic z)
    (hcover : HullFiveFanCoversPoint p z) :
    ∃ region : HullFivePointRegion,
      ∀ anchor : Fin 5,
        InHullFiveFanCell p z anchor (region.fanCell anchor) := by
  classical
  let cell : Fin 5 → Fin 3 := fun a => Classical.choose (hcover a)
  have hcell : ∀ a : Fin 5, InHullFiveFanCell p z a (cell a) := fun a =>
    Classical.choose_spec (hcover a)
  have hcompatible : HullFiveFanProfileCompatible cell := by
    intro a
    constructor
    · intro ha
      have hcell0 : InAnchoredFiveFanCell p
          (hullFiveRotate z a) 0 := by
        simpa only [InHullFiveFanCell, ha] using hcell a
      have hsigns := inAnchoredFiveFanCell_diagonalSigns
        (hcyc a) hcell0
      have hneg : sig (hullFiveRotate z a 0)
          (hullFiveRotate z a 2) p < 0 := by
        exact hsigns.1
      have hreverse : 0 < sig (hullFiveRotate z (a + 2) 0)
          (hullFiveRotate z (a + 2) 3) p := by
        rw [hullFiveRotate_add_two_zero, hullFiveRotate_add_two_three]
        have heq : sig (hullFiveRotate z a 2)
            (hullFiveRotate z a 0) p =
            -sig (hullFiveRotate z a 0) (hullFiveRotate z a 2) p := by
          simp only [sig]
          ring
        nlinarith
      exact inAnchoredFiveFanCell_eq_two_of_second_pos
        (hcyc (a + 2)) (hcell (a + 2)) hreverse
    · intro ha
      have hcell2 : InAnchoredFiveFanCell p
          (hullFiveRotate z (a + 2)) 2 := by
        simpa only [InHullFiveFanCell, ha] using hcell (a + 2)
      have hsigns := inAnchoredFiveFanCell_diagonalSigns
        (hcyc (a + 2)) hcell2
      have hpos : 0 < sig (hullFiveRotate z (a + 2) 0)
          (hullFiveRotate z (a + 2) 3) p := by
        exact hsigns.2
      have hreverse : sig (hullFiveRotate z a 0)
          (hullFiveRotate z a 2) p < 0 := by
        rw [← hullFiveRotate_add_two_zero z a,
          ← hullFiveRotate_add_two_three z a]
        have heq : sig (hullFiveRotate z (a + 2) 3)
            (hullFiveRotate z (a + 2) 0) p =
            -sig (hullFiveRotate z (a + 2) 0)
              (hullFiveRotate z (a + 2) 3) p := by
          simp only [sig]
          ring
        nlinarith
      exact inAnchoredFiveFanCell_eq_zero_of_first_neg
        (hcyc a) (hcell a) hreverse
  obtain ⟨region, hregion⟩ :=
    hullFiveFanProfile_region cell hcompatible
  refine ⟨region, ?_⟩
  intro anchor
  rw [← hregion]
  exact hcell anchor

/-- The direct geometry-to-eleven-region adapter. -/
theorem hullFivePointRegion_of_strictInterior
    {p : ℝ × ℝ} {z : Fin 5 → ℝ × ℝ}
    (hcyc : HullFiveStrictCyclic z)
    (hinside : HullFivePointStrictInterior p z) :
    ∃ region : HullFivePointRegion,
      ∀ anchor : Fin 5,
        InHullFiveFanCell p z anchor (region.fanCell anchor) :=
  hullFivePointRegion_of_fanCovers hcyc
    (hullFiveFanCoversPoint_of_strictInterior hcyc hinside)

#print axioms hullFivePointRegion_of_fanCovers
#print axioms hullFivePointRegion_of_strictInterior

end Heilbronn8.TriHull
