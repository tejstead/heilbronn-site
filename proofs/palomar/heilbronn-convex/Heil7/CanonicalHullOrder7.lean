import Heil7.CanonicalHullCarrier7
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.RelClasses

/-!
# Ordering an irredundant seven-point hull carrier

Choose one carrier point as anchor.  The remaining carrier points are ordered
by positive orientation around that anchor.  General position makes the
relation total; irredundancy makes it transitive, since the contrary sign
would put a carrier point in the triangle spanned by three other carrier
points.

The output is an equivalence from an initial `Fin` segment to the carrier
subtype, already in strict counter-clockwise order.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

open Function Set

private structure CarrierPoint7 (s : Finset (Fin 7)) where
  val : Fin 7
  property : val ∈ s

private lemma CarrierPoint7.eq_of_val_eq
    {s : Finset (Fin 7)} {x y : CarrierPoint7 s}
    (h : x.val = y.val) : x = y := by
  cases x with
  | mk xv hx =>
      cases y with
      | mk yv hy =>
          simp only at h
          subst yv
          rfl

private def carrierPointEquiv7 (s : Finset (Fin 7)) :
    CarrierPoint7 s ≃ {q : Fin 7 // q ∈ s} where
  toFun q := ⟨q.val, q.property⟩
  invFun q := ⟨q.val, q.property⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

private instance (s : Finset (Fin 7)) : Fintype (CarrierPoint7 s) :=
  Fintype.ofEquiv {q : Fin 7 // q ∈ s} (carrierPointEquiv7 s).symm

private lemma sig_swap_left_order7 (p q r : ℝ × ℝ) :
    sig q p r = -sig p q r := by
  simp only [sig]
  ring

private lemma sig_reverse_order7 (p q r : ℝ × ℝ) :
    sig r q p = -sig p q r := by
  simp only [sig]
  ring

private def carrierOrientationLT7
    (v : Configuration7) (a x y : Fin 7) : Prop :=
  (x = a ∧ y ≠ a) ∨
    (x ≠ a ∧ y ≠ a ∧ 0 < sig (v a) (v x) (v y))

private lemma anchor_orientation_trans7
    {v : Configuration7} (hstrict : AllTripleNonzero7 v)
    {s : Finset (Fin 7)}
    (hirred : ∀ q ∈ s,
      v q ∉ convexHull ℝ (v '' (↑(s.erase q) : Set (Fin 7))))
    {a x y z : Fin 7}
    (has : a ∈ s) (hxs : x ∈ s) (hys : y ∈ s) (hzs : z ∈ s)
    (hxa : x ≠ a) (hya : y ≠ a) (hza : z ≠ a)
    (hxy : 0 < sig (v a) (v x) (v y))
    (hyz : 0 < sig (v a) (v y) (v z)) :
    0 < sig (v a) (v x) (v z) := by
  have hxy_ne : x ≠ y := by
    intro h
    subst y
    simpa [sig] using hxy
  have hyz_ne : y ≠ z := by
    intro h
    subst z
    simpa [sig] using hyz
  have hxz_ne : x ≠ z := by
    intro h
    subst z
    have hswap : sig (v a) (v y) (v x) =
        -sig (v a) (v x) (v y) := by
      simp only [sig]
      ring
    linarith
  have haxz_ne :=
    hstrict a x z (Ne.symm hxa) (Ne.symm hza) hxz_ne
  rcases lt_or_gt_of_ne haxz_ne with haxz | haxz
  · have hxyz : 0 < sig (v x) (v y) (v z) := by
      have hcocycle :
          sig (v x) (v y) (v z) - sig (v a) (v y) (v z) +
              sig (v a) (v x) (v z) - sig (v a) (v x) (v y) = 0 := by
        simpa only [← HeilbronnChallenge.sig_eq] using
          HullBridge.cocycle (v a) (v x) (v y) (v z)
      linarith
    have hin : HullBridge.InTri (v a) (v x) (v y) (v z) := by
      apply HullBridge.inTri_of_sig (v a) (v x) (v y) (v z) hxyz
      · exact hyz.le
      · rw [← HeilbronnChallenge.sig_eq, sig_swap_left_order7]
        linarith
      · have hrot : sig (v x) (v y) (v a) =
            sig (v a) (v x) (v y) := by
          simp only [sig]
          ring
        rw [← HeilbronnChallenge.sig_eq, hrot]
        exact hxy.le
    have htri :
        v a ∈ convexHull ℝ
          ({v x, v y, v z} : Set (ℝ × ℝ)) :=
      hin.mem_convexHull
    have hsubset :
        ({v x, v y, v z} : Set (ℝ × ℝ)) ⊆
          v '' (↑(s.erase a) : Set (Fin 7)) := by
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, ?_, ?_⟩
      · exact ⟨x, Finset.mem_erase.mpr ⟨hxa, hxs⟩, rfl⟩
      · exact ⟨y, Finset.mem_erase.mpr ⟨hya, hys⟩, rfl⟩
      · exact ⟨z, Finset.mem_erase.mpr ⟨hza, hzs⟩, rfl⟩
    exact False.elim
      (hirred a has (convexHull_mono hsubset htri))
  · exact haxz

/-- An irredundant finite carrier in general position admits a strict
counter-clockwise enumeration. -/
theorem exists_strictCCW_order7_of_irredundant
    (v : Configuration7) (hstrict : AllTripleNonzero7 v)
    (s : Finset (Fin 7)) (hcard : 3 ≤ s.card)
    (hirred : ∀ q ∈ s,
      v q ∉ convexHull ℝ (v '' (↑(s.erase q) : Set (Fin 7)))) :
    ∃ e : Fin s.card ≃ {q : Fin 7 // q ∈ s},
      ∀ i j k : Fin s.card, i < j → j < k →
        0 < sig (v (e i)) (v (e j)) (v (e k)) := by
  classical
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  let a : Fin 7 := s.min' hsne
  have has : a ∈ s := Finset.min'_mem s hsne
  let S := CarrierPoint7 s
  let cycleLT : S → S → Prop :=
    fun x y ↦ carrierOrientationLT7 v a x.val y.val

  letI : IsStrictTotalOrder S cycleLT := {
    irrefl := by
      intro x hx
      change carrierOrientationLT7 v a x.val x.val at hx
      rcases hx with hx | hx
      · exact hx.2 hx.1
      · simpa [sig] using hx.2.2
    trans := by
      intro x y z hxy hyz
      change carrierOrientationLT7 v a x.val y.val at hxy
      change carrierOrientationLT7 v a y.val z.val at hyz
      change carrierOrientationLT7 v a x.val z.val
      rcases hxy with hxy | hxy
      · rcases hyz with hyz | hyz
        · exact False.elim (hxy.2 hyz.1)
        · exact Or.inl ⟨hxy.1, hyz.2.1⟩
      · rcases hyz with hyz | hyz
        · exact False.elim (hxy.2.1 hyz.1)
        · refine Or.inr ⟨hxy.1, hyz.2.1, ?_⟩
          exact anchor_orientation_trans7 hstrict hirred
            has x.property y.property z.property hxy.1 hxy.2.1 hyz.2.1
            hxy.2.2 hyz.2.2
    toTrichotomous :=
      Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} ↦ by
        by_cases hxy : x = y
        · exact Or.inr (Or.inl hxy)
        have hxy_val : x.val ≠ y.val := by
          intro h
          exact hxy (CarrierPoint7.eq_of_val_eq h)
        by_cases hxa : x.val = a
        · left
          exact Or.inl ⟨hxa, fun hya ↦ hxy_val (hxa.trans hya.symm)⟩
        · by_cases hya : y.val = a
          · right
            right
            exact Or.inl ⟨hya, fun hxa' ↦ hxy_val (hxa'.trans hya.symm)⟩
          · have hsig_ne :=
              hstrict a x.val y.val (Ne.symm hxa) (Ne.symm hya) hxy_val
            rcases lt_or_gt_of_ne hsig_ne with hneg | hpos
            · right
              right
              refine Or.inr ⟨hya, hxa, ?_⟩
              have hswap : sig (v a) (v y.val) (v x.val) =
                  -sig (v a) (v x.val) (v y.val) := by
                simp only [sig]
                ring
              rw [hswap]
              linarith
            · left
              exact Or.inr ⟨hxa, hya, hpos⟩
  }

  letI : DecidableRel cycleLT := Classical.decRel cycleLT
  letI : LinearOrder S := linearOrderOfSTO cycleLT
  have hS_card : Fintype.card S = s.card := by
    calc
      Fintype.card S = Fintype.card {q : Fin 7 // q ∈ s} :=
        Fintype.card_congr (carrierPointEquiv7 s)
      _ = s.card := Fintype.card_coe s
  let e : Fin s.card ≃o S :=
    monoEquivOfFin S (k := s.card) hS_card
  let c : Fin s.card → Fin 7 := fun i ↦ (e i).val
  have hc_inj : Function.Injective c := by
    intro i j hij
    apply e.injective
    apply CarrierPoint7.eq_of_val_eq
    exact hij
  have hc_mem : ∀ i, c i ∈ s := fun i ↦ (e i).property

  letI : NeZero s.card := ⟨by omega⟩
  let aa : S := ⟨a, has⟩
  have haa_le : ∀ q : S, aa ≤ q := by
    intro q
    change aa = q ∨ cycleLT aa q
    by_cases hqa : q.val = a
    · left
      exact CarrierPoint7.eq_of_val_eq hqa.symm
    · right
      exact Or.inl ⟨rfl, hqa⟩
  have he_zero : e (0 : Fin s.card) = aa := by
    apply le_antisymm
    · rw [← e.apply_symm_apply aa]
      exact e.monotone (Fin.zero_le _)
    · exact haa_le (e 0)
  have hc_zero : c (0 : Fin s.card) = a :=
    congrArg CarrierPoint7.val he_zero

  have hpolar : ∀ i j : Fin s.card,
      (0 : Fin s.card) < i → i < j →
        0 < sig (v a) (v (c i)) (v (c j)) := by
    intro i j hi hij
    have hci_ne : c i ≠ a := by
      intro h
      have : c i = c 0 := h.trans hc_zero.symm
      have := hc_inj this
      omega
    have heij : cycleLT (e i) (e j) := by
      change e i < e j
      exact e.strictMono hij
    rcases heij with heij | heij
    · exact False.elim (hci_ne heij.1)
    · exact heij.2.2

  have hcycle_pos : ∀ i j k : Fin s.card,
      i < j → j < k →
        0 < sig (v (c i)) (v (c j)) (v (c k)) := by
    intro i j k hij hjk
    by_cases hi : i = 0
    · subst i
      rw [hc_zero]
      exact hpolar j k hij hjk
    · have hzero_i : (0 : Fin s.card) < i :=
        Fin.pos_iff_ne_zero.mpr hi
      have hpij := hpolar i j hzero_i hij
      have hpjk := hpolar j k (lt_trans hzero_i hij) hjk
      have hpik := hpolar i k hzero_i (lt_trans hij hjk)
      have hcij : c i ≠ c j := hc_inj.ne hij.ne
      have hcik : c i ≠ c k :=
        hc_inj.ne (ne_of_lt (lt_trans hij hjk))
      have hcjk : c j ≠ c k := hc_inj.ne hjk.ne
      have hsig_ne := hstrict (c i) (c j) (c k) hcij hcik hcjk
      rcases lt_or_gt_of_ne hsig_ne with hneg | hpos
      · have hin : HullBridge.InTri (v (c j)) (v a)
            (v (c i)) (v (c k)) := by
          apply HullBridge.inTri_of_sig (v (c j)) (v a)
            (v (c i)) (v (c k)) hpik
          · rw [← HeilbronnChallenge.sig_eq, sig_swap_left_order7]
            linarith
          · exact hpjk.le
          · exact hpij.le
        have htri :
            v (c j) ∈ convexHull ℝ
              ({v a, v (c i), v (c k)} : Set (ℝ × ℝ)) :=
          hin.mem_convexHull
        have haj : a ≠ c j := by
          intro h
          have : c j = c 0 := h.symm.trans hc_zero.symm
          have := hc_inj this
          omega
        have hsubset :
            ({v a, v (c i), v (c k)} : Set (ℝ × ℝ)) ⊆
              v '' (↑(s.erase (c j)) : Set (Fin 7)) := by
          simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
          refine ⟨?_, ?_, ?_⟩
          · exact ⟨a, Finset.mem_erase.mpr ⟨haj, has⟩, rfl⟩
          · exact ⟨c i, Finset.mem_erase.mpr ⟨hcij, hc_mem i⟩, rfl⟩
          · exact ⟨c k,
              Finset.mem_erase.mpr ⟨Ne.symm hcjk, hc_mem k⟩, rfl⟩
        exact False.elim
          (hirred (c j) (hc_mem j) (convexHull_mono hsubset htri))
      · exact hpos

  let eh : Fin s.card ≃ {q : Fin 7 // q ∈ s} :=
    e.toEquiv.trans (carrierPointEquiv7 s)
  refine ⟨eh, ?_⟩
  intro i j k hij hjk
  simpa [eh, c, carrierPointEquiv7] using
    hcycle_pos i j k hij hjk

end HeilbronnChallenge.N7Upper
