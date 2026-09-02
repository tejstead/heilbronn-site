import Heil7.CanonicalHullOrder7
import Heil7.CanonicalHullBridge7
import Mathlib.Data.Fintype.Sort
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Certificate-free hull classification for seven points

On the zero-minimum branch the canonical upper bound is immediate.  Otherwise
the extreme-point carrier is put in strict counter-clockwise order, extended
by its complement to a permutation of all seven labels, and identified with
the actual convex hull.  Convexity gives weak support-edge signs for the tail;
general position upgrades them to the strict signs in `InHullN`.

The final area identity dispatches only on the five possible hull sizes and
uses the public `HullBridge` fan-volume formulas.  No order-type corpus or
generated certificate enters this construction.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

open MeasureTheory Set

private lemma sig_rotate7 (a b c : ℝ × ℝ) :
    sig a b c = sig b c a := by
  simp only [sig]
  ring

private lemma volume_convexHull_eq_frontFanArea7
    (n : ℕ) (w : Configuration7) (hlo : 3 ≤ n) (hhi : n ≤ 7)
    (pts : Fin n → ℝ × ℝ)
    (hfront : ∀ i : Fin n, pts i = w (Fin.castLE hhi i))
    (hpos : ∀ i j k : Fin n, i < j → j < k →
      0 < HullBridge.sig (pts i) (pts j) (pts k)) :
    volume (convexHull ℝ (Set.range pts)) =
      ENNReal.ofReal (fanArea w n / 2) := by
  interval_cases n
  · simpa [fanArea, hfront, ← HeilbronnChallenge.sig_eq] using
      HullBridge.volume_convexHull_strictCCW3 pts hpos
  · simpa [fanArea, hfront, ← HeilbronnChallenge.sig_eq] using
      HullBridge.volume_convexHull_strictCCW4 pts hpos
  · simpa [fanArea, hfront, ← HeilbronnChallenge.sig_eq] using
      HullBridge.volume_convexHull_strictCCW5 pts hpos
  · simpa [fanArea, hfront, ← HeilbronnChallenge.sig_eq] using
      HullBridge.volume_convexHull_strictCCW6 pts hpos
  · simpa [fanArea, hfront, ← HeilbronnChallenge.sig_eq] using
      HullBridge.volume_convexHull_strictCCW7 pts hpos

private lemma fanArea_pos_of_hullCCW7
    (n : ℕ) (w : Configuration7) (hlo : 3 ≤ n) (hhi : n ≤ 7)
    (hccw : HullCCW w n) : 0 < fanArea w n := by
  interval_cases n
  · simpa [fanArea] using
      hccw 0 1 2 (by decide) (by decide) (by norm_num)
  · have h1 := hccw 0 1 2 (by decide) (by decide) (by norm_num)
    have h2 := hccw 0 2 3 (by decide) (by decide) (by norm_num)
    simp only [fanArea]
    linarith
  · have h1 := hccw 0 1 2 (by decide) (by decide) (by norm_num)
    have h2 := hccw 0 2 3 (by decide) (by decide) (by norm_num)
    have h3 := hccw 0 3 4 (by decide) (by decide) (by norm_num)
    simp only [fanArea]
    linarith
  · have h1 := hccw 0 1 2 (by decide) (by decide) (by norm_num)
    have h2 := hccw 0 2 3 (by decide) (by decide) (by norm_num)
    have h3 := hccw 0 3 4 (by decide) (by decide) (by norm_num)
    have h4 := hccw 0 4 5 (by decide) (by decide) (by norm_num)
    simp only [fanArea]
    linarith
  · have h1 := hccw 0 1 2 (by decide) (by decide) (by norm_num)
    have h2 := hccw 0 2 3 (by decide) (by decide) (by norm_num)
    have h3 := hccw 0 3 4 (by decide) (by decide) (by norm_num)
    have h4 := hccw 0 4 5 (by decide) (by decide) (by norm_num)
    have h5 := hccw 0 5 6 (by decide) (by decide) (by norm_num)
    simp only [fanArea]
    linarith

private def complSubtypeEquiv7 (s : Finset (Fin 7)) :
    {q : Fin 7 // q ∈ sᶜ} ≃ {q : Fin 7 // q ∉ s} where
  toFun q := ⟨q.1, Finset.mem_compl.mp q.2⟩
  invFun q := ⟨q.1, Finset.mem_compl.mpr q.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

/-- Every seven-point configuration has the exact hull-first classification
consumed by `nine_minTri_le_doubledHullArea`. -/
theorem hullClassified_all (v : Configuration7) : HullClassified v := by
  classical
  by_cases hmzero : minTri v = 0
  · exact Or.inl hmzero
  right
  have hmpos : 0 < minTri v :=
    lt_of_le_of_ne (minTri_nonneg v) (Ne.symm hmzero)
  have hstrict : AllTripleNonzero7 v :=
    allTripleNonzero7_of_minTri_pos v hmpos
  let carrier := strictHullCarrier7_exists v hstrict
  let s : Finset (Fin 7) := carrier.labels
  let h : ℕ := s.card
  let t : ℕ := sᶜ.card
  have hlo : 3 ≤ h := by
    simpa [h, s] using carrier.card_ge_three
  have hhi : h ≤ 7 := by
    simpa [h, s] using carrier.card_le_seven
  letI : NeZero h := ⟨by omega⟩

  obtain ⟨eHull, hcycle⟩ :=
    exists_strictCCW_order7_of_irredundant v hstrict s hlo (by
      intro q hqs
      simpa [s] using carrier.irredundant q hqs)

  have hsum : h + t = 7 := by
    simpa [h, t] using Finset.card_add_card_compl s
  let eTailRaw : Fin t ≃ {q : Fin 7 // q ∈ sᶜ} :=
    (sᶜ.orderIsoOfFin (k := t) rfl).toEquiv
  let eTail : Fin t ≃ {q : Fin 7 // q ∉ s} :=
    eTailRaw.trans (complSubtypeEquiv7 s)
  let targetParts : Fin h ⊕ Fin t ≃ Fin 7 :=
    (Equiv.sumCongr eHull eTail).trans
      (Equiv.Set.sumCompl (↑s : Set (Fin 7)))
  let sourceParts : Fin 7 ≃ Fin h ⊕ Fin t :=
    (finCongr hsum).symm.trans finSumFinEquiv.symm
  let σ : Equiv.Perm (Fin 7) := sourceParts.trans targetParts

  have hsource_front (i : Fin h) :
      sourceParts (Fin.castLE hhi i) = Sum.inl i := by
    change finSumFinEquiv.symm
        ((finCongr hsum).symm (Fin.castLE hhi i)) = Sum.inl i
    have heq : (finCongr hsum).symm (Fin.castLE hhi i) =
        Fin.castAdd t i := by
      apply Fin.ext
      rfl
    rw [heq]
    exact finSumFinEquiv_symm_apply_castAdd i
  have hsigma_front (i : Fin h) :
      σ (Fin.castLE hhi i) = (eHull i : Fin 7) := by
    change targetParts (sourceParts (Fin.castLE hhi i)) = _
    rw [hsource_front]
    change (Equiv.Set.sumCompl (↑s : Set (Fin 7)))
      (Sum.inl (eHull i)) = _
    exact Equiv.Set.sumCompl_apply_inl (↑s : Set (Fin 7)) (eHull i)
  have hsigma_tail_not_mem (p : Fin 7) (hp : h ≤ (p : ℕ)) :
      σ p ∉ s := by
    intro hpMem
    generalize hz : sourceParts p = z
    cases z with
    | inl i =>
        have hpi : p = Fin.castLE hhi i := by
          apply sourceParts.injective
          rw [hz, hsource_front]
        have hpval := congrArg Fin.val hpi
        change p.val = i.val at hpval
        omega
    | inr j =>
        have hs : σ p = (eTail j : Fin 7) := by
          change targetParts (sourceParts p) = _
          rw [hz]
          change (Equiv.Set.sumCompl (↑s : Set (Fin 7)))
            (Sum.inr (eTail j)) = _
          exact Equiv.Set.sumCompl_apply_inr
            (↑s : Set (Fin 7)) (eTail j)
        exact (eTail j).property (by simpa [← hs] using hpMem)

  let w : Configuration7 := v ∘ σ
  have hccw : HullCCW w h := by
    intro i j k hij hjk hk
    let ii : Fin h := ⟨i.val, by omega⟩
    let jj : Fin h := ⟨j.val, by omega⟩
    let kk : Fin h := ⟨k.val, hk⟩
    have hiFront : i = Fin.castLE hhi ii := by
      apply Fin.ext
      rfl
    have hjFront : j = Fin.castLE hhi jj := by
      apply Fin.ext
      rfl
    have hkFront : k = Fin.castLE hhi kk := by
      apply Fin.ext
      rfl
    have hw_i : w i = v (eHull ii) := by
      rw [hiFront]
      exact congrArg v (hsigma_front ii)
    have hw_j : w j = v (eHull jj) := by
      rw [hjFront]
      exact congrArg v (hsigma_front jj)
    have hw_k : w k = v (eHull kk) := by
      rw [hkFront]
      exact congrArg v (hsigma_front kk)
    rw [hw_i, hw_j, hw_k]
    exact hcycle ii jj kk (by exact hij) (by exact hjk)

  have hedge_nonneg (i j r : Fin h) (hij : i < j)
      (hnext : i.val + 1 = j.val) :
      0 ≤ sig (v (eHull i)) (v (eHull j)) (v (eHull r)) := by
    rcases lt_trichotomy r i with hri | hri | hir
    · have hp := hcycle r i j hri hij
      rw [sig_rotate7 (v (eHull r)) (v (eHull i)) (v (eHull j))] at hp
      exact hp.le
    · subst r
      simp [sig]
    · rcases lt_trichotomy r j with hrj | hrj | hjr
      · omega
      · subst r
        simp [sig]
      · exact (hcycle i j r hij hjr).le
  have hclosing_nonneg (j r : Fin h) (hjlast : j.val + 1 = h) :
      0 ≤ sig (v (eHull j)) (v (eHull 0)) (v (eHull r)) := by
    by_cases hr0 : r = 0
    · subst r
      simp [sig]
    by_cases hrj : r = j
    · subst r
      simp [sig]
    have h0r : (0 : Fin h) < r := Fin.pos_iff_ne_zero.mpr hr0
    have hrjlt : r < j := by
      change r.val < j.val
      omega
    have hp := hcycle 0 r j h0r hrjlt
    have hrot : sig (v (eHull j)) (v (eHull 0)) (v (eHull r)) =
        sig (v (eHull 0)) (v (eHull r)) (v (eHull j)) := by
      simp only [sig]
      ring
    rw [hrot]
    exact hp.le

  have hsupported_edge (q : Fin 7) (hq : q ∉ s)
      (i j : Fin h) (hij : i < j) (hnext : i.val + 1 = j.val) :
      0 < sig (v (eHull i)) (v (eHull j)) (v q) := by
    have hnonneg :
        0 ≤ sig (v (eHull i)) (v (eHull j)) (v q) := by
      apply HullBridge.sig_nonneg_on_convexHull
        (v (eHull i)) (v (eHull j))
        (v '' (↑s : Set (Fin 7)))
      · rintro _ ⟨r, hrs, rfl⟩
        obtain ⟨ri, hri⟩ := eHull.surjective ⟨r, hrs⟩
        have hrval : (eHull ri : Fin 7) = r :=
          congrArg Subtype.val hri
        rw [← hrval]
        exact hedge_nonneg i j ri hij hnext
      · simpa [s] using carrier.covers q
    have hijLabels : (eHull i : Fin 7) ≠ (eHull j : Fin 7) := by
      intro heq
      exact (ne_of_lt hij) (eHull.injective (Subtype.ext heq))
    have hiq : (eHull i : Fin 7) ≠ q := by
      intro heq
      apply hq
      rw [← heq]
      exact (eHull i).property
    have hjq : (eHull j : Fin 7) ≠ q := by
      intro heq
      apply hq
      rw [← heq]
      exact (eHull j).property
    have hne := hstrict (eHull i) (eHull j) q hijLabels hiq hjq
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hsupported_closing (q : Fin 7) (hq : q ∉ s)
      (j : Fin h) (hjlast : j.val + 1 = h) :
      0 < sig (v (eHull j)) (v (eHull 0)) (v q) := by
    have hnonneg :
        0 ≤ sig (v (eHull j)) (v (eHull 0)) (v q) := by
      apply HullBridge.sig_nonneg_on_convexHull
        (v (eHull j)) (v (eHull 0))
        (v '' (↑s : Set (Fin 7)))
      · rintro _ ⟨r, hrs, rfl⟩
        obtain ⟨ri, hri⟩ := eHull.surjective ⟨r, hrs⟩
        have hrval : (eHull ri : Fin 7) = r :=
          congrArg Subtype.val hri
        rw [← hrval]
        exact hclosing_nonneg j ri hjlast
      · simpa [s] using carrier.covers q
    have hj0 : (eHull j : Fin 7) ≠ (eHull 0 : Fin 7) := by
      intro heq
      have hej : j = 0 := eHull.injective (Subtype.ext heq)
      subst j
      simp only [Fin.val_zero] at hjlast
      omega
    have hjq : (eHull j : Fin 7) ≠ q := by
      intro heq
      apply hq
      rw [← heq]
      exact (eHull j).property
    have h0q : (eHull 0 : Fin 7) ≠ q := by
      intro heq
      apply hq
      rw [← heq]
      exact (eHull 0).property
    have hne := hstrict (eHull j) (eHull 0) q hj0 hjq h0q
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

  have hin : ∀ p : Fin 7, h ≤ (p : ℕ) → InHullN w h p := by
    intro p hp
    have hqout : σ p ∉ s := hsigma_tail_not_mem p hp
    constructor
    · intro i hi
      let ii : Fin h := ⟨i.val, by omega⟩
      let jj : Fin h := ⟨i.val + 1, hi⟩
      have hiFront : i = Fin.castLE hhi ii := by
        apply Fin.ext
        rfl
      have hsuccFront : i + 1 = Fin.castLE hhi jj := by
        apply Fin.ext
        change (i.val + 1) % 7 = i.val + 1
        rw [Nat.mod_eq_of_lt]
        omega
      have hw_i : w i = v (eHull ii) := by
        rw [hiFront]
        exact congrArg v (hsigma_front ii)
      have hw_succ : w (i + 1) = v (eHull jj) := by
        rw [hsuccFront]
        exact congrArg v (hsigma_front jj)
      rw [hw_i, hw_succ]
      have hiijj : ii < jj := by
        change i.val < i.val + 1
        exact Nat.lt_succ_self _
      exact hsupported_edge (σ p) hqout ii jj hiijj rfl
    · intro j hj
      let jj : Fin h := ⟨j.val, by omega⟩
      have hjFront : j = Fin.castLE hhi jj := by
        apply Fin.ext
        rfl
      have hzeroFront : (0 : Fin 7) =
          Fin.castLE hhi (0 : Fin h) := by
        apply Fin.ext
        rfl
      have hw_j : w j = v (eHull jj) := by
        rw [hjFront]
        exact congrArg v (hsigma_front jj)
      have hw_zero : w 0 = v (eHull (0 : Fin h)) := by
        rw [hzeroFront]
        exact congrArg v (hsigma_front 0)
      rw [hw_j, hw_zero]
      exact hsupported_closing (σ p) hqout jj hj

  let pts : Fin h → ℝ × ℝ :=
    fun i ↦ w (Fin.castLE hhi i)
  have hpts (i : Fin h) : pts i = v (eHull i) := by
    exact congrArg v (hsigma_front i)
  have hptsCCW : ∀ i j k : Fin h, i < j → j < k →
      0 < HullBridge.sig (pts i) (pts j) (pts k) := by
    intro i j k hij hjk
    rw [hpts, hpts, hpts]
    exact hcycle i j k hij hjk
  have himage : v '' (↑s : Set (Fin 7)) = Set.range pts := by
    apply Set.Subset.antisymm
    · rintro _ ⟨q, hqs, rfl⟩
      obtain ⟨i, hi⟩ := eHull.surjective ⟨q, hqs⟩
      refine ⟨i, ?_⟩
      rw [hpts]
      exact congrArg v (congrArg Subtype.val hi)
    · rintro _ ⟨i, rfl⟩
      refine ⟨eHull i, (eHull i).property, ?_⟩
      exact (hpts i).symm
  have hcontain : Set.range v ⊆
      convexHull ℝ (Set.range pts) := by
    rintro _ ⟨p, rfl⟩
    rw [← himage]
    simpa [s] using carrier.covers p
  have hcycle_subset : Set.range pts ⊆ Set.range v := by
    rintro _ ⟨i, rfl⟩
    rw [hpts]
    exact ⟨eHull i, rfl⟩
  have hhull : convexHull ℝ (Set.range v) =
      convexHull ℝ (Set.range pts) := by
    apply Set.Subset.antisymm
    · exact convexHull_min hcontain (convex_convexHull ℝ (Set.range pts))
    · exact convexHull_mono hcycle_subset

  have hfront (i : Fin h) : pts i = w (Fin.castLE hhi i) := by
    rfl
  have hvol : volume (convexHull ℝ (Set.range pts)) =
      ENNReal.ofReal (fanArea w h / 2) :=
    volume_convexHull_eq_frontFanArea7 h w hlo hhi pts hfront hptsCCW
  have hfanpos : 0 < fanArea w h :=
    fanArea_pos_of_hullCCW7 h w hlo hhi hccw
  have hvolume : volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal (fanArea w h / 2) := by
    rw [hhull]
    exact hvol
  have harea : HullBridge.doubledHullArea v = fanArea w h := by
    rw [HullBridge.doubledHullArea, hvolume,
      ENNReal.toReal_ofReal (div_nonneg hfanpos.le (by norm_num))]
    ring
  exact ⟨h, σ, hlo, hhi, hccw, hin, harea⟩

end HeilbronnChallenge.N7Upper
