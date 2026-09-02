import Mathlib

/-!
# Exact two-variable interval checker for hull-seven type 2

This file contains the small trusted part of the type-2 numerical closer.  It
defines a deterministic rational box checker and proves its soundness over the
reals.  The two root computations are kept in the separate certificate file.

Every numerical square-root lower bound is treated as untrusted data: the
Boolean leaf test explicitly checks that it is nonnegative and that its square
is at most the rational radicand.  Thus soundness does not depend on the
implementation of `Nat.sqrt` used to choose the candidate.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.TriHull

inductive HullSevenType2TwoVarBranch where
  | lower
  | upper
deriving DecidableEq, Repr

namespace HullSevenType2TwoVar

abbrev Branch := HullSevenType2TwoVarBranch

structure Box where
  xlo : ℚ
  dlo : ℚ
  xhi : ℚ
  dhi : ℚ
deriving DecidableEq, Repr

def lowerRoot : Box :=
  ⟨1, 32 / 361, 361 / 32, 361 / 32⟩

def upperRoot : Box :=
  ⟨1, 1, 19 / 4, 19 / 4⟩

def root : Branch → Box
  | .lower => lowerRoot
  | .upper => upperRoot

def dUpper (b : Box) : ℚ :=
  (b.dhi - 1 / b.xhi) * (b.dhi + 2 * b.xhi - 1 / b.xhi)

def qLower (b : Box) : ℚ :=
  b.dlo * (2 * b.xlo + b.dlo)

def ySqLower (b : Box) : ℚ :=
  1 / dUpper b + qLower b / (1 + dUpper b)

def radLower : Branch → Box → ℚ
  | .lower, b =>
      (2 * b.xlo + b.dlo + b.xlo / b.dhi) * (b.dlo + 1)
  | .upper, b =>
      (b.dlo * (2 * b.xlo + b.dlo) + b.xlo) * (1 + 1 / b.xhi)

def sqrtBits : Nat := 20

def sqrtScale : Nat := 2 ^ sqrtBits

/-- A cheap candidate for a `sqrtBits`-dyadic square-root lower bound.
Soundness uses only the separately checked predicate `lowerSquare`. -/
def sqrtLower (q : ℚ) : ℚ :=
  let numerator := q.num.toNat * sqrtScale ^ 2 / q.den
  (Nat.sqrt numerator : ℚ) / (sqrtScale : ℚ)

def LowerSquare (value lower : ℚ) : Prop :=
  0 ≤ value ∧ 0 ≤ lower ∧ lower * lower ≤ value

instance lowerSquareDecidable (value lower : ℚ) :
    Decidable (LowerSquare value lower) := by
  unfold LowerSquare
  infer_instance

def domainClosed (b : Box) : Bool :=
  decide (b.dhi ≤ 1 / b.xhi)

def orderClosed : Branch → Box → Bool
  | .lower, b => decide (b.xhi < b.dlo)
  | .upper, b => decide (b.dhi < b.xlo)

def gapCondition (branch : Branch) (b : Box) : Prop :=
  let yl := sqrtLower (ySqLower b)
  let tl := sqrtLower (radLower branch b)
  LowerSquare (ySqLower b) yl ∧
    LowerSquare (radLower branch b) tl ∧
    19 / 2 < yl * (1 + 1 / b.dhi) + 2 * tl

instance gapConditionDecidable (branch : Branch) (b : Box) :
    Decidable (gapCondition branch b) := by
  unfold gapCondition
  infer_instance

def gapClosed (branch : Branch) (b : Box) : Bool :=
  decide (gapCondition branch b)

def leafClosed (branch : Branch) (b : Box) : Bool :=
  domainClosed b || orderClosed branch b || gapClosed branch b

def xScale (branch : Branch) : ℚ :=
  (root branch).xhi - (root branch).xlo

def dScale (branch : Branch) : ℚ :=
  (root branch).dhi - (root branch).dlo

/-- The widest relative width is bisected; ties select `X`. -/
def splitX (branch : Branch) (b : Box) : Bool :=
  decide ((b.xhi - b.xlo) / xScale branch ≥
    (b.dhi - b.dlo) / dScale branch)

def xmid (b : Box) : ℚ :=
  (b.xlo + b.xhi) / 2

def dmid (b : Box) : ℚ :=
  (b.dlo + b.dhi) / 2

def xLeft (b : Box) : Box :=
  { b with xhi := xmid b }

def xRight (b : Box) : Box :=
  { b with xlo := xmid b }

def dLeft (b : Box) : Box :=
  { b with dhi := dmid b }

def dRight (b : Box) : Box :=
  { b with dlo := dmid b }

/-- Deterministic branch-and-bound reconstruction.  Fuel 26 suffices for both
frozen root computations. -/
def check (branch : Branch) : Nat → Box → Bool
  | 0, b => leafClosed branch b
  | fuel + 1, b =>
      if leafClosed branch b then true
      else if splitX branch b then
        check branch fuel (xLeft b) && check branch fuel (xRight b)
      else
        check branch fuel (dLeft b) && check branch fuel (dRight b)

/-! ## Real semantics -/

noncomputable section

def Box.Contains (b : Box) (x d : ℝ) : Prop :=
  (b.xlo : ℝ) ≤ x ∧ x ≤ (b.xhi : ℝ) ∧
    (b.dlo : ℝ) ≤ d ∧ d ≤ (b.dhi : ℝ)

def Box.Positive (b : Box) : Prop :=
  0 < (b.xlo : ℝ) ∧ 0 < (b.dlo : ℝ) ∧
    (b.xlo : ℝ) ≤ (b.xhi : ℝ) ∧
    (b.dlo : ℝ) ≤ (b.dhi : ℝ)

def delta (x d : ℝ) : ℝ :=
  (d - 1 / x) * (d + 2 * x - 1 / x)

def qValue (x d : ℝ) : ℝ :=
  d * (2 * x + d)

def ySqValue (x d : ℝ) : ℝ :=
  1 / delta x d + qValue x d / (1 + delta x d)

def radValue : Branch → ℝ → ℝ → ℝ
  | .lower, x, d => (2 * x + d + x / d) * (d + 1)
  | .upper, x, d => (d * (2 * x + d) + x) * (1 + 1 / x)

structure Feasible (branch : Branch) (b : Box)
    (x d y t : ℝ) : Prop where
  contains : b.Contains x d
  x_floor : 1 ≤ x
  domain : 1 / x < d
  order : match branch with
    | .lower => d ≤ x
    | .upper => x ≤ d
  y_nonneg : 0 ≤ y
  t_nonneg : 0 ≤ t
  y_sq : y ^ 2 = ySqValue x d
  t_sq : t ^ 2 = radValue branch x d

private lemma cast_le_of_rat_le {a b : ℚ} (h : a ≤ b) :
    (a : ℝ) ≤ (b : ℝ) :=
  Rat.cast_le.mpr h

private lemma cast_lt_of_rat_lt {a b : ℚ} (h : a < b) :
    (a : ℝ) < (b : ℝ) :=
  Rat.cast_lt.mpr h

private lemma cast_nonneg_of_rat_nonneg {a : ℚ} (h : 0 ≤ a) :
    0 ≤ (a : ℝ) :=
  Rat.cast_nonneg.mpr h

private lemma box_xhi_pos {branch : Branch} {b : Box} {x d y t : ℝ}
    (hb : b.Positive) (h : Feasible branch b x d y t) :
    0 < (b.xhi : ℝ) :=
  lt_of_lt_of_le hb.1 (h.contains.1.trans h.contains.2.1)

private lemma actual_x_pos {branch : Branch} {b : Box} {x d y t : ℝ}
    (h : Feasible branch b x d y t) : 0 < x :=
  lt_of_lt_of_le (by norm_num) h.x_floor

private lemma actual_d_pos {branch : Branch} {b : Box} {x d y t : ℝ}
    (h : Feasible branch b x d y t) : 0 < d := by
  have hx := actual_x_pos h
  have hi : 0 < 1 / x := one_div_pos.mpr hx
  exact hi.trans h.domain

private lemma delta_pos {branch : Branch} {b : Box} {x d y t : ℝ}
    (h : Feasible branch b x d y t) : 0 < delta x d := by
  have hx := actual_x_pos h
  have hf : 0 < d - 1 / x := sub_pos.mpr h.domain
  have hg : 0 < d + 2 * x - 1 / x := by nlinarith
  exact mul_pos hf hg

private lemma delta_le_dUpper {branch : Branch} {b : Box} {x d y t : ℝ}
    (hb : b.Positive) (h : Feasible branch b x d y t) :
    delta x d ≤ (dUpper b : ℝ) := by
  have hx := actual_x_pos h
  have hxhi := box_xhi_pos hb h
  have hinv : 1 / (b.xhi : ℝ) ≤ 1 / x :=
    one_div_le_one_div_of_le hx h.contains.2.1
  have hf : d - 1 / x ≤ (b.dhi : ℝ) - 1 / (b.xhi : ℝ) := by
    linarith [h.contains.2.2.2]
  have hg : d + 2 * x - 1 / x ≤
      (b.dhi : ℝ) + 2 * (b.xhi : ℝ) - 1 / (b.xhi : ℝ) := by
    linarith [h.contains.2.1, h.contains.2.2.2]
  have hf0 : 0 ≤ d - 1 / x := sub_nonneg.mpr h.domain.le
  have hF0 : 0 ≤ (b.dhi : ℝ) - 1 / (b.xhi : ℝ) := hf0.trans hf
  have hg0 : 0 ≤ d + 2 * x - 1 / x := by nlinarith
  have hm := mul_le_mul hf hg hg0 hF0
  simpa [delta, dUpper] using hm

private lemma qLower_le_qValue {branch : Branch} {b : Box} {x d y t : ℝ}
    (hb : b.Positive) (h : Feasible branch b x d y t) :
    (qLower b : ℝ) ≤ qValue x d := by
  have hdlo : 0 ≤ (b.dlo : ℝ) := hb.2.1.le
  have hxlo : 0 ≤ (b.xlo : ℝ) := hb.1.le
  have hfirst : (b.dlo : ℝ) ≤ d := h.contains.2.2.1
  have hsecond : 2 * (b.xlo : ℝ) + (b.dlo : ℝ) ≤ 2 * x + d := by
    linarith [h.contains.1, h.contains.2.2.1]
  have hlowerSecond : 0 ≤ 2 * (b.xlo : ℝ) + (b.dlo : ℝ) := by
    linarith
  have hm := mul_le_mul hfirst hsecond hlowerSecond (actual_d_pos h).le
  simpa [qLower, qValue] using hm

private lemma ySqLower_le {branch : Branch} {b : Box} {x d y t : ℝ}
    (hb : b.Positive) (h : Feasible branch b x d y t) :
    (ySqLower b : ℝ) ≤ ySqValue x d := by
  have hDpos := delta_pos h
  have hDle := delta_le_dUpper hb h
  have hrecip : 1 / (dUpper b : ℝ) ≤ 1 / delta x d :=
    one_div_le_one_div_of_le hDpos hDle
  have hqle := qLower_le_qValue hb h
  have hq0 : 0 ≤ qValue x d := by
    have hd := actual_d_pos h
    have hx := actual_x_pos h
    exact mul_nonneg hd.le (by positivity)
  have hfrac : (qLower b : ℝ) / (1 + (dUpper b : ℝ)) ≤
      qValue x d / (1 + delta x d) := by
    apply div_le_div₀ hq0 hqle
    · linarith
    · linarith
  simpa [ySqLower, ySqValue] using add_le_add hrecip hfrac

private lemma lower_rad_le {b : Box} {x d y t : ℝ}
    (hb : b.Positive) (h : Feasible .lower b x d y t) :
    (radLower .lower b : ℝ) ≤ radValue .lower x d := by
  have hx := actual_x_pos h
  have hd := actual_d_pos h
  have hdhi : 0 < (b.dhi : ℝ) :=
    lt_of_lt_of_le hd h.contains.2.2.2
  have hdlo : 0 ≤ (b.dlo : ℝ) := hb.2.1.le
  have hxfrac : (b.xlo : ℝ) / (b.dhi : ℝ) ≤ x / d := by
    exact div_le_div₀ (actual_x_pos h).le h.contains.1 hd
      h.contains.2.2.2
  have hfirst : 2 * (b.xlo : ℝ) + (b.dlo : ℝ) +
      (b.xlo : ℝ) / (b.dhi : ℝ) ≤ 2 * x + d + x / d := by
    linarith [h.contains.1, h.contains.2.2.1]
  have hsecond : (b.dlo : ℝ) + 1 ≤ d + 1 := by
    linarith [h.contains.2.2.1]
  have hlowerSecond : 0 ≤ (b.dlo : ℝ) + 1 := by linarith
  have hupperFirst : 0 ≤ 2 * x + d + x / d := by positivity
  have hm := mul_le_mul hfirst hsecond hlowerSecond hupperFirst
  simpa [radLower, radValue] using hm

private lemma upper_rad_le {b : Box} {x d y t : ℝ}
    (hb : b.Positive) (h : Feasible .upper b x d y t) :
    (radLower .upper b : ℝ) ≤ radValue .upper x d := by
  have hx := actual_x_pos h
  have hd := actual_d_pos h
  have hxhi := box_xhi_pos hb h
  have hinv : 1 / (b.xhi : ℝ) ≤ 1 / x :=
    one_div_le_one_div_of_le hx h.contains.2.1
  have hqle := qLower_le_qValue hb h
  have hfirst : (qLower b : ℝ) + (b.xlo : ℝ) ≤ qValue x d + x := by
    linarith [h.contains.1]
  have hsecond : 1 + 1 / (b.xhi : ℝ) ≤ 1 + 1 / x := by linarith
  have hlowerSecond : 0 ≤ 1 + 1 / (b.xhi : ℝ) := by positivity
  have hupperFirst : 0 ≤ qValue x d + x := by
    dsimp [qValue]
    positivity
  have hm := mul_le_mul hfirst hsecond hlowerSecond hupperFirst
  simpa [radLower, radValue, qLower, qValue] using hm

private lemma radLower_le {branch : Branch} {b : Box} {x d y t : ℝ}
    (hb : b.Positive) (h : Feasible branch b x d y t) :
    (radLower branch b : ℝ) ≤ radValue branch x d := by
  cases branch with
  | lower => exact lower_rad_le hb h
  | upper => exact upper_rad_le hb h

private lemma lower_of_sq_le_sq {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsq : a * a ≤ b ^ 2) : a ≤ b := by
  nlinarith [sq_nonneg (a + b)]

private lemma gap_sound {branch : Branch} {b : Box} {x d y t : ℝ}
    (hb : b.Positive) (hgap : gapClosed branch b = true)
    (h : Feasible branch b x d y t) :
    19 / 2 < y * (1 + 1 / d) + 2 * t := by
  have hg : gapCondition branch b := of_decide_eq_true hgap
  let yl : ℚ := sqrtLower (ySqLower b)
  let tl : ℚ := sqrtLower (radLower branch b)
  change LowerSquare (ySqLower b) yl ∧
      LowerSquare (radLower branch b) tl ∧
      19 / 2 < yl * (1 + 1 / b.dhi) + 2 * tl at hg
  have hyl0 : 0 ≤ (yl : ℝ) := cast_nonneg_of_rat_nonneg hg.1.2.1
  have htl0 : 0 ≤ (tl : ℝ) := cast_nonneg_of_rat_nonneg hg.2.1.2.1
  have hylsqRat : yl * yl ≤ ySqLower b := hg.1.2.2
  have hylsq : (yl : ℝ) * (yl : ℝ) ≤ y ^ 2 := by
    have hc : ((yl * yl : ℚ) : ℝ) ≤ (ySqLower b : ℝ) :=
      cast_le_of_rat_le hylsqRat
    rw [Rat.cast_mul] at hc
    exact (hc.trans (ySqLower_le hb h)).trans_eq h.y_sq.symm
  have htlSqRat : tl * tl ≤ radLower branch b := hg.2.1.2.2
  have htlSq : (tl : ℝ) * (tl : ℝ) ≤ t ^ 2 := by
    have hc : ((tl * tl : ℚ) : ℝ) ≤ (radLower branch b : ℝ) :=
      cast_le_of_rat_le htlSqRat
    rw [Rat.cast_mul] at hc
    exact (hc.trans (radLower_le hb h)).trans_eq h.t_sq.symm
  have hyl : (yl : ℝ) ≤ y := lower_of_sq_le_sq hyl0 h.y_nonneg hylsq
  have htl : (tl : ℝ) ≤ t := lower_of_sq_le_sq htl0 h.t_nonneg htlSq
  have hdpos := actual_d_pos h
  have hdhi : 0 < (b.dhi : ℝ) := lt_of_lt_of_le hdpos h.contains.2.2.2
  have hinv : 1 / (b.dhi : ℝ) ≤ 1 / d :=
    one_div_le_one_div_of_le hdpos h.contains.2.2.2
  have hfactor : 1 + 1 / (b.dhi : ℝ) ≤ 1 + 1 / d := by linarith
  have hlowerFactor : 0 ≤ 1 + 1 / (b.dhi : ℝ) := by positivity
  have hmul : (yl : ℝ) * (1 + 1 / (b.dhi : ℝ)) ≤
      y * (1 + 1 / d) := mul_le_mul hyl hfactor hlowerFactor h.y_nonneg
  have hstrictRat : (19 / 2 : ℚ) < yl * (1 + 1 / b.dhi) + 2 * tl := hg.2.2
  have hstrict : (19 / 2 : ℝ) <
      (yl : ℝ) * (1 + 1 / (b.dhi : ℝ)) + 2 * (tl : ℝ) := by
    have hc := cast_lt_of_rat_lt hstrictRat
    norm_num at hc ⊢
    simpa using hc
  nlinarith

private lemma domain_not_closed {branch : Branch} {b : Box} {x d y t : ℝ}
    (hb : b.Positive) (h : Feasible branch b x d y t) :
    domainClosed b = false := by
  apply Bool.eq_false_iff.mpr
  intro hc
  have hrat : b.dhi ≤ 1 / b.xhi := of_decide_eq_true hc
  have hreal : (b.dhi : ℝ) ≤ 1 / (b.xhi : ℝ) := by
    simpa using cast_le_of_rat_le hrat
  have hx := actual_x_pos h
  have hinv : 1 / (b.xhi : ℝ) ≤ 1 / x :=
    one_div_le_one_div_of_le hx h.contains.2.1
  linarith [h.contains.2.2.2, h.domain]

private lemma order_not_closed {branch : Branch} {b : Box} {x d y t : ℝ}
    (h : Feasible branch b x d y t) : orderClosed branch b = false := by
  cases branch with
  | lower =>
      apply Bool.eq_false_iff.mpr
      intro hc
      have hrat : b.xhi < b.dlo := of_decide_eq_true hc
      have hreal : (b.xhi : ℝ) < (b.dlo : ℝ) := cast_lt_of_rat_lt hrat
      linarith [h.contains.2.1, h.contains.2.2.1, h.order]
  | upper =>
      apply Bool.eq_false_iff.mpr
      intro hc
      have hrat : b.dhi < b.xlo := of_decide_eq_true hc
      have hreal : (b.dhi : ℝ) < (b.xlo : ℝ) := cast_lt_of_rat_lt hrat
      linarith [h.contains.1, h.contains.2.2.2, h.order]

private lemma leaf_sound {branch : Branch} {b : Box} {x d y t : ℝ}
    (hb : b.Positive) (hc : leafClosed branch b = true)
    (h : Feasible branch b x d y t) :
    19 / 2 < y * (1 + 1 / d) + 2 * t := by
  rw [leafClosed, domain_not_closed hb h, order_not_closed h] at hc
  simpa using gap_sound hb hc h

private lemma positive_xLeft {b : Box} (hb : b.Positive) : (xLeft b).Positive := by
  refine ⟨hb.1, hb.2.1, ?_, hb.2.2.2⟩
  dsimp [xLeft, xmid]
  push_cast
  linarith [hb.2.2.1]

private lemma positive_xRight {b : Box} (hb : b.Positive) : (xRight b).Positive := by
  refine ⟨?_, hb.2.1, ?_, hb.2.2.2⟩
  · dsimp [xRight, xmid]
    push_cast
    linarith [hb.1, hb.2.2.1]
  · dsimp [xRight, xmid]
    push_cast
    linarith [hb.2.2.1]

private lemma positive_dLeft {b : Box} (hb : b.Positive) : (dLeft b).Positive := by
  refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_⟩
  dsimp [dLeft, dmid]
  push_cast
  linarith [hb.2.2.2]

private lemma positive_dRight {b : Box} (hb : b.Positive) : (dRight b).Positive := by
  refine ⟨hb.1, ?_, hb.2.2.1, ?_⟩
  · dsimp [dRight, dmid]
    push_cast
    linarith [hb.2.1, hb.2.2.2]
  · dsimp [dRight, dmid]
    push_cast
    linarith [hb.2.2.2]

private lemma feasible_x_split {branch : Branch} {b : Box} {x d y t : ℝ}
    (h : Feasible branch b x d y t) :
    Feasible branch (xLeft b) x d y t ∨
      Feasible branch (xRight b) x d y t := by
  by_cases hx : x ≤ (xmid b : ℚ)
  · left
    refine { h with contains := ?_ }
    exact ⟨h.contains.1, hx, h.contains.2.2⟩
  · right
    refine { h with contains := ?_ }
    have hmid : ((xmid b : ℚ) : ℝ) ≤ x := le_of_not_ge hx
    exact ⟨hmid, h.contains.2.1, h.contains.2.2⟩

private lemma feasible_d_split {branch : Branch} {b : Box} {x d y t : ℝ}
    (h : Feasible branch b x d y t) :
    Feasible branch (dLeft b) x d y t ∨
      Feasible branch (dRight b) x d y t := by
  by_cases hd : d ≤ (dmid b : ℚ)
  · left
    refine { h with contains := ?_ }
    exact ⟨h.contains.1, h.contains.2.1, h.contains.2.2.1, hd⟩
  · right
    refine { h with contains := ?_ }
    have hmid : ((dmid b : ℚ) : ℝ) ≤ d := le_of_not_ge hd
    exact ⟨h.contains.1, h.contains.2.1, hmid, h.contains.2.2.2⟩

/-- Generic soundness of the deterministic checker.  No fact about
`sqrtLower` is trusted beyond the inequalities checked at each gap leaf. -/
theorem check_sound {branch : Branch} {fuel : Nat} {b : Box}
    {x d y t : ℝ} (hb : b.Positive)
    (hc : check branch fuel b = true)
    (h : Feasible branch b x d y t) :
    19 / 2 < y * (1 + 1 / d) + 2 * t := by
  induction fuel generalizing b with
  | zero =>
      exact leaf_sound hb hc h
  | succ fuel ih =>
      by_cases hleaf : leafClosed branch b = true
      · exact leaf_sound hb hleaf h
      · have hleaf0 : leafClosed branch b = false :=
          Bool.eq_false_of_not_eq_true hleaf
        rw [check, hleaf0] at hc
        simp only [Bool.false_eq_true, if_false] at hc
        by_cases hs : splitX branch b = true
        · simp only [hs, if_true] at hc
          rw [Bool.and_eq_true] at hc
          rcases feasible_x_split h with hl | hr
          · exact ih (positive_xLeft hb) hc.1 hl
          · exact ih (positive_xRight hb) hc.2 hr
        · have hs0 : splitX branch b = false := Bool.eq_false_of_not_eq_true hs
          simp only [hs0, Bool.false_eq_true, if_false] at hc
          rw [Bool.and_eq_true] at hc
          rcases feasible_d_split h with hl | hr
          · exact ih (positive_dLeft hb) hc.1 hl
          · exact ih (positive_dRight hb) hc.2 hr

end

end HullSevenType2TwoVar

end Heilbronn8.TriHull
