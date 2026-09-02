import Heilbronn8.TriHull.HullFive300CabCensus
import Heilbronn8.TriHull.HullFive300SameSector

/-!
# Geometry adapter for the right-ear CAB census

The sequential hull labels are `A,B,X,C,D = e 0,...,e 4`.  For a CAB
packet this file uses the canonical inner order

`P = e 7` (profile C), `Q = e 5` (profile A), `R = e 6` (profile B).

All three points lie in `BXC`.  The fixed CAB angular signs are kept in the
small `HullFive300CabFanPartition` interface.  From those signs and the
three `BXC` memberships, the determinant identities in this file prove all
seven hypotheses of the propositional census.  Thus the interface needs
only one genuinely fan-combinatorial operation: turn a same-sector bit
clause into an actual same-sector witness.

The final theorem calls the public same-sector central bound and adds the
two hull-triangle floors.  The unique type-717 cell is an explicit callback;
no generated table or certificate is used here.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

/-- A repeated `BXC` fan sector, with an arbitrary inner anchor and an
arbitrary cyclic rotation of the base triangle.  `base_area` records that
the selected base still has oriented area `[BXC]`. -/
inductive HullFive300CabSameSectorWitness
    (v : Configuration) (e : Equiv.Perm (Fin 8)) : Prop where
  | mk
      (f : Fin 6 → Fin 8)
      (injective : Function.Injective f)
      (base_area :
        sig (v (f 0)) (v (f 1)) (v (f 2)) =
          sig (v (e 1)) (v (e 2)) (v (e 3)))
      (anchor_in_base :
        InTriStrict (v (f 3)) (v (f 0)) (v (f 1)) (v (f 2)))
      (first_in_sector :
        InTriStrict (v (f 4)) (v (f 3)) (v (f 1)) (v (f 2)))
      (second_in_sector :
        InTriStrict (v (f 5)) (v (f 3)) (v (f 1)) (v (f 2)))

/-- The small fan-partition interface used by the CAB geometry adapter.

The five implications are exactly the five disjuncts of
`CabSameSectorBits`, in the order `PXC`, `PCB`, `QCB`, `QBX`, `RCB`; the
three omitted `X` rows have their fixed CAB signs in the first three fields.
A caller proves these implications directly from its fan-cell predicates,
independently of the metric argument in this file. -/
structure HullFive300CabFanPartition
    (v : Configuration) (e : Equiv.Perm (Fin 8)) : Prop where
  xpq_neg : sig (v (e 2)) (v (e 7)) (v (e 5)) < 0
  xpr_neg : sig (v (e 2)) (v (e 7)) (v (e 6)) < 0
  xqr_pos : 0 < sig (v (e 2)) (v (e 5)) (v (e 6))
  pxc_of_bits :
    (0 < sig (v (e 3)) (v (e 7)) (v (e 5)) ∧
      0 < sig (v (e 3)) (v (e 7)) (v (e 6))) →
    InTriStrict (v (e 5)) (v (e 7)) (v (e 2)) (v (e 3)) ∧
      InTriStrict (v (e 6)) (v (e 7)) (v (e 2)) (v (e 3))
  pcb_of_bits :
    (¬ 0 < sig (v (e 3)) (v (e 7)) (v (e 5)) ∧
      0 < sig (v (e 1)) (v (e 7)) (v (e 5)) ∧
      ¬ 0 < sig (v (e 3)) (v (e 7)) (v (e 6)) ∧
      0 < sig (v (e 1)) (v (e 7)) (v (e 6))) →
    InTriStrict (v (e 5)) (v (e 7)) (v (e 3)) (v (e 1)) ∧
      InTriStrict (v (e 6)) (v (e 7)) (v (e 3)) (v (e 1))
  qcb_of_bits :
    (0 < sig (v (e 3)) (v (e 7)) (v (e 5)) ∧
      ¬ 0 < sig (v (e 1)) (v (e 7)) (v (e 5)) ∧
      ¬ 0 < sig (v (e 3)) (v (e 5)) (v (e 6)) ∧
      0 < sig (v (e 1)) (v (e 5)) (v (e 6))) →
    InTriStrict (v (e 7)) (v (e 5)) (v (e 3)) (v (e 1)) ∧
      InTriStrict (v (e 6)) (v (e 5)) (v (e 3)) (v (e 1))
  qbx_of_bits :
    (0 < sig (v (e 1)) (v (e 7)) (v (e 5)) ∧
      ¬ 0 < sig (v (e 1)) (v (e 5)) (v (e 6))) →
    InTriStrict (v (e 7)) (v (e 5)) (v (e 1)) (v (e 2)) ∧
      InTriStrict (v (e 6)) (v (e 5)) (v (e 1)) (v (e 2))
  rcb_of_bits :
    (0 < sig (v (e 3)) (v (e 7)) (v (e 6)) ∧
      ¬ 0 < sig (v (e 1)) (v (e 7)) (v (e 6)) ∧
      0 < sig (v (e 3)) (v (e 5)) (v (e 6)) ∧
      ¬ 0 < sig (v (e 1)) (v (e 5)) (v (e 6))) →
    InTriStrict (v (e 7)) (v (e 6)) (v (e 3)) (v (e 1)) ∧
      InTriStrict (v (e 5)) (v (e 6)) (v (e 3)) (v (e 1))

/-- The complete canonical sign description of the exceptional CAB cell,
including the `PQR` sign forced by a Pluecker identity. -/
structure HullFive300Cab717Signs
    (v : Configuration) (e : Equiv.Perm (Fin 8)) : Prop where
  bpq_pos : 0 < sig (v (e 1)) (v (e 7)) (v (e 5))
  xpq_neg : sig (v (e 2)) (v (e 7)) (v (e 5)) < 0
  cpq_pos : 0 < sig (v (e 3)) (v (e 7)) (v (e 5))
  bpr_pos : 0 < sig (v (e 1)) (v (e 7)) (v (e 6))
  xpr_neg : sig (v (e 2)) (v (e 7)) (v (e 6)) < 0
  cpr_neg : sig (v (e 3)) (v (e 7)) (v (e 6)) < 0
  bqr_pos : 0 < sig (v (e 1)) (v (e 5)) (v (e 6))
  xqr_pos : 0 < sig (v (e 2)) (v (e 5)) (v (e 6))
  cqr_neg : sig (v (e 3)) (v (e 5)) (v (e 6)) < 0
  pqr_pos : 0 < sig (v (e 7)) (v (e 5)) (v (e 6))

private lemma sig_ne_zero_of_minTri_pos_cab
    (v : Configuration) (hm : 0 < minTri v)
    {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    sig (v i) (v j) (v k) ≠ 0 := by
  intro hzero
  have hmin := minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
  rw [hzero, abs_zero] at hmin
  linarith

private lemma inTriStrict_rotate_cab {P A B C : ℝ × ℝ}
    (h : InTriStrict P A B C) : InTriStrict P B C A := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, rfl⟩ := h
  exact ⟨y, z, x, hy, hz, hx, by linarith, by module⟩

private lemma cabSameSectorWitness_of_bits
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hP : InTriStrict (v (e 7)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hQ : InTriStrict (v (e 5)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hR : InTriStrict (v (e 6)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hfan : HullFive300CabFanPartition v e)
    (hbits : CabSameSectorBits
      (0 < sig (v (e 1)) (v (e 7)) (v (e 5)))
      (0 < sig (v (e 3)) (v (e 7)) (v (e 5)))
      (0 < sig (v (e 1)) (v (e 7)) (v (e 6)))
      (0 < sig (v (e 3)) (v (e 7)) (v (e 6)))
      (0 < sig (v (e 1)) (v (e 5)) (v (e 6)))
      (0 < sig (v (e 3)) (v (e 5)) (v (e 6)))) :
    HullFive300CabSameSectorWitness v e := by
  simp only [CabSameSectorBits] at hbits
  rcases hbits with hpxc | hpcb | hqcb | hqbx | hrcb
  · obtain ⟨hQsector, hRsector⟩ := hfan.pxc_of_bits hpxc
    let s : Fin 6 → Fin 8 := ![1, 2, 3, 7, 5, 6]
    let f : Fin 6 → Fin 8 := fun i ↦ e (s i)
    have hs : Function.Injective s := by decide
    refine .mk f (e.injective.comp hs) ?_ ?_ ?_ ?_
    · rfl
    · simpa [f, s] using hP
    · simpa [f, s] using hQsector
    · simpa [f, s] using hRsector
  · obtain ⟨hQsector, hRsector⟩ := hfan.pcb_of_bits hpcb
    let s : Fin 6 → Fin 8 := ![2, 3, 1, 7, 5, 6]
    let f : Fin 6 → Fin 8 := fun i ↦ e (s i)
    have hs : Function.Injective s := by decide
    have hProt := inTriStrict_rotate_cab hP
    refine .mk f (e.injective.comp hs) ?_ ?_ ?_ ?_
    · change sig (v (e 2)) (v (e 3)) (v (e 1)) =
        sig (v (e 1)) (v (e 2)) (v (e 3))
      rw [sig_rotate (v (e 2)) (v (e 3)) (v (e 1)),
        sig_rotate (v (e 3)) (v (e 1)) (v (e 2))]
    · simpa [f, s] using hProt
    · simpa [f, s] using hQsector
    · simpa [f, s] using hRsector
  · obtain ⟨hPsector, hRsector⟩ := hfan.qcb_of_bits hqcb
    let s : Fin 6 → Fin 8 := ![2, 3, 1, 5, 7, 6]
    let f : Fin 6 → Fin 8 := fun i ↦ e (s i)
    have hs : Function.Injective s := by decide
    have hQrot := inTriStrict_rotate_cab hQ
    refine .mk f (e.injective.comp hs) ?_ ?_ ?_ ?_
    · change sig (v (e 2)) (v (e 3)) (v (e 1)) =
        sig (v (e 1)) (v (e 2)) (v (e 3))
      rw [sig_rotate (v (e 2)) (v (e 3)) (v (e 1)),
        sig_rotate (v (e 3)) (v (e 1)) (v (e 2))]
    · simpa [f, s] using hQrot
    · simpa [f, s] using hPsector
    · simpa [f, s] using hRsector
  · obtain ⟨hPsector, hRsector⟩ := hfan.qbx_of_bits hqbx
    let s : Fin 6 → Fin 8 := ![3, 1, 2, 5, 7, 6]
    let f : Fin 6 → Fin 8 := fun i ↦ e (s i)
    have hs : Function.Injective s := by decide
    have hQrot := inTriStrict_rotate_cab (inTriStrict_rotate_cab hQ)
    refine .mk f (e.injective.comp hs) ?_ ?_ ?_ ?_
    · change sig (v (e 3)) (v (e 1)) (v (e 2)) =
        sig (v (e 1)) (v (e 2)) (v (e 3))
      rw [sig_rotate (v (e 3)) (v (e 1)) (v (e 2))]
    · simpa [f, s] using hQrot
    · simpa [f, s] using hPsector
    · simpa [f, s] using hRsector
  · obtain ⟨hPsector, hQsector⟩ := hfan.rcb_of_bits hrcb
    let s : Fin 6 → Fin 8 := ![2, 3, 1, 6, 7, 5]
    let f : Fin 6 → Fin 8 := fun i ↦ e (s i)
    have hs : Function.Injective s := by decide
    have hRrot := inTriStrict_rotate_cab hR
    refine .mk f (e.injective.comp hs) ?_ ?_ ?_ ?_
    · change sig (v (e 2)) (v (e 3)) (v (e 1)) =
        sig (v (e 1)) (v (e 2)) (v (e 3))
      rw [sig_rotate (v (e 2)) (v (e 3)) (v (e 1)),
        sig_rotate (v (e 3)) (v (e 1)) (v (e 2))]
    · simpa [f, s] using hRrot
    · simpa [f, s] using hPsector
    · simpa [f, s] using hQsector

/-- The geometry-level CAB census.  The three common `BXC` memberships are
exactly the `.bxc` fields of profiles C, A, and B in canonical CAB order.
The conclusion is either an actual repeated-sector witness or all ten
strict signs of the exceptional type 717. -/
theorem hullFive300_cab_sameSector_or_717
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hm : 0 < minTri v)
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hP : InTriStrict (v (e 7)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hQ : InTriStrict (v (e 5)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hR : InTriStrict (v (e 6)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hfan : HullFive300CabFanPartition v e) :
    HullFive300CabSameSectorWitness v e ∨
      HullFive300Cab717Signs v e := by
  obtain ⟨hPXC, hPCB, hPBX⟩ := inTriStrict_fan_pos hBXC hP
  obtain ⟨hQXC, hQCB, hQBX⟩ := inTriStrict_fan_pos hBXC hQ
  obtain ⟨hRXC, hRCB, hRBX⟩ := inTriStrict_fan_pos hBXC hR

  have hpairPQ :
      sig (v (e 7)) (v (e 2)) (v (e 3)) *
          sig (v (e 1)) (v (e 7)) (v (e 5)) +
        sig (v (e 7)) (v (e 3)) (v (e 1)) *
          sig (v (e 2)) (v (e 7)) (v (e 5)) +
        sig (v (e 7)) (v (e 1)) (v (e 2)) *
          sig (v (e 3)) (v (e 7)) (v (e 5)) = 0 := by
    simp only [sig]
    ring
  have hpairPR :
      sig (v (e 7)) (v (e 2)) (v (e 3)) *
          sig (v (e 1)) (v (e 7)) (v (e 6)) +
        sig (v (e 7)) (v (e 3)) (v (e 1)) *
          sig (v (e 2)) (v (e 7)) (v (e 6)) +
        sig (v (e 7)) (v (e 1)) (v (e 2)) *
          sig (v (e 3)) (v (e 7)) (v (e 6)) = 0 := by
    simp only [sig]
    ring
  have hpairQR :
      sig (v (e 5)) (v (e 2)) (v (e 3)) *
          sig (v (e 1)) (v (e 5)) (v (e 6)) +
        sig (v (e 5)) (v (e 3)) (v (e 1)) *
          sig (v (e 2)) (v (e 5)) (v (e 6)) +
        sig (v (e 5)) (v (e 1)) (v (e 2)) *
          sig (v (e 3)) (v (e 5)) (v (e 6)) = 0 := by
    simp only [sig]
    ring

  have hpq :
      0 < sig (v (e 1)) (v (e 7)) (v (e 5)) ∨
        0 < sig (v (e 3)) (v (e 7)) (v (e 5)) := by
    by_cases hbpq : 0 < sig (v (e 1)) (v (e 7)) (v (e 5))
    · exact Or.inl hbpq
    · right
      by_contra hcpq
      have h0 := mul_nonpos_of_nonneg_of_nonpos hPXC.le
        (le_of_not_gt hbpq)
      have h1 := mul_neg_of_pos_of_neg hPCB hfan.xpq_neg
      have h2 := mul_nonpos_of_nonneg_of_nonpos hPBX.le
        (le_of_not_gt hcpq)
      nlinarith [hpairPQ]
  have hpr :
      0 < sig (v (e 1)) (v (e 7)) (v (e 6)) ∨
        0 < sig (v (e 3)) (v (e 7)) (v (e 6)) := by
    by_cases hbpr : 0 < sig (v (e 1)) (v (e 7)) (v (e 6))
    · exact Or.inl hbpr
    · right
      by_contra hcpr
      have h0 := mul_nonpos_of_nonneg_of_nonpos hPXC.le
        (le_of_not_gt hbpr)
      have h1 := mul_neg_of_pos_of_neg hPCB hfan.xpr_neg
      have h2 := mul_nonpos_of_nonneg_of_nonpos hPBX.le
        (le_of_not_gt hcpr)
      nlinarith [hpairPR]
  have hqr :
      ¬ (0 < sig (v (e 1)) (v (e 5)) (v (e 6)) ∧
        0 < sig (v (e 3)) (v (e 5)) (v (e 6))) := by
    rintro ⟨hbqr, hcqr⟩
    have h0 := mul_pos hQXC hbqr
    have h1 := mul_pos hQCB hfan.xqr_pos
    have h2 := mul_pos hQBX hcqr
    nlinarith [hpairQR]

  have hBidentity :
      sig (v (e 7)) (v (e 3)) (v (e 1)) *
          sig (v (e 1)) (v (e 5)) (v (e 6)) -
        sig (v (e 5)) (v (e 3)) (v (e 1)) *
          sig (v (e 1)) (v (e 7)) (v (e 6)) +
        sig (v (e 6)) (v (e 3)) (v (e 1)) *
          sig (v (e 1)) (v (e 7)) (v (e 5)) = 0 := by
    simp only [sig]
    ring
  have hCidentity :
      sig (v (e 7)) (v (e 2)) (v (e 3)) *
          sig (v (e 3)) (v (e 5)) (v (e 6)) -
        sig (v (e 5)) (v (e 2)) (v (e 3)) *
          sig (v (e 3)) (v (e 7)) (v (e 6)) +
        sig (v (e 6)) (v (e 2)) (v (e 3)) *
          sig (v (e 3)) (v (e 7)) (v (e 5)) = 0 := by
    simp only [sig]
    ring

  have hBcycle₁ : ¬
      (0 < sig (v (e 1)) (v (e 7)) (v (e 5)) ∧
        ¬ 0 < sig (v (e 1)) (v (e 7)) (v (e 6)) ∧
        0 < sig (v (e 1)) (v (e 5)) (v (e 6))) := by
    rintro ⟨hbpq, hbpr, hbqr⟩
    have h0 := mul_pos hPCB hbqr
    have h1 := mul_nonpos_of_nonneg_of_nonpos hQCB.le
      (le_of_not_gt hbpr)
    have h2 := mul_pos hRCB hbpq
    nlinarith [hBidentity]
  have hBcycle₂ : ¬
      (¬ 0 < sig (v (e 1)) (v (e 7)) (v (e 5)) ∧
        0 < sig (v (e 1)) (v (e 7)) (v (e 6)) ∧
        ¬ 0 < sig (v (e 1)) (v (e 5)) (v (e 6))) := by
    rintro ⟨hbpq, hbpr, hbqr⟩
    have h0 := mul_nonpos_of_nonneg_of_nonpos hPCB.le
      (le_of_not_gt hbqr)
    have h1 := mul_pos hQCB hbpr
    have h2 := mul_nonpos_of_nonneg_of_nonpos hRCB.le
      (le_of_not_gt hbpq)
    nlinarith [hBidentity]
  have hCcycle₁ : ¬
      (0 < sig (v (e 3)) (v (e 7)) (v (e 5)) ∧
        ¬ 0 < sig (v (e 3)) (v (e 7)) (v (e 6)) ∧
        0 < sig (v (e 3)) (v (e 5)) (v (e 6))) := by
    rintro ⟨hcpq, hcpr, hcqr⟩
    have h0 := mul_pos hPXC hcqr
    have h1 := mul_nonpos_of_nonneg_of_nonpos hQXC.le
      (le_of_not_gt hcpr)
    have h2 := mul_pos hRXC hcpq
    nlinarith [hCidentity]
  have hCcycle₂ : ¬
      (¬ 0 < sig (v (e 3)) (v (e 7)) (v (e 5)) ∧
        0 < sig (v (e 3)) (v (e 7)) (v (e 6)) ∧
        ¬ 0 < sig (v (e 3)) (v (e 5)) (v (e 6))) := by
    rintro ⟨hcpq, hcpr, hcqr⟩
    have h0 := mul_nonpos_of_nonneg_of_nonpos hPXC.le
      (le_of_not_gt hcqr)
    have h1 := mul_pos hQXC hcpr
    have h2 := mul_nonpos_of_nonneg_of_nonpos hRXC.le
      (le_of_not_gt hcpq)
    nlinarith [hCidentity]

  rcases cab_sameSector_or_717_bits hpq hpr hqr
      hBcycle₁ hBcycle₂ hCcycle₁ hCcycle₂ with hsame | h717
  · exact Or.inl
      (cabSameSectorWitness_of_bits v e hP hQ hR hfan hsame)
  · right
    rcases h717 with ⟨hbpq, hcpq, hbpr, hcpr, hbqr, hcqr⟩
    have hcpr_ne : sig (v (e 3)) (v (e 7)) (v (e 6)) ≠ 0 :=
      sig_ne_zero_of_minTri_pos_cab v hm
        (e.injective.ne (by decide)) (e.injective.ne (by decide))
        (e.injective.ne (by decide))
    have hcqr_ne : sig (v (e 3)) (v (e 5)) (v (e 6)) ≠ 0 :=
      sig_ne_zero_of_minTri_pos_cab v hm
        (e.injective.ne (by decide)) (e.injective.ne (by decide))
        (e.injective.ne (by decide))
    have hcpr_neg : sig (v (e 3)) (v (e 7)) (v (e 6)) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hcpr) hcpr_ne
    have hcqr_neg : sig (v (e 3)) (v (e 5)) (v (e 6)) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hcqr) hcqr_ne
    have hPQRidentity :
        sig (v (e 7)) (v (e 2)) (v (e 3)) *
            sig (v (e 7)) (v (e 5)) (v (e 6)) =
          sig (v (e 3)) (v (e 7)) (v (e 5)) *
              (-sig (v (e 2)) (v (e 7)) (v (e 6))) -
            (-sig (v (e 2)) (v (e 7)) (v (e 5))) *
              sig (v (e 3)) (v (e 7)) (v (e 6)) := by
      simp only [sig]
      ring
    have hfirst :
        0 < sig (v (e 3)) (v (e 7)) (v (e 5)) *
          (-sig (v (e 2)) (v (e 7)) (v (e 6))) :=
      mul_pos hcpq (neg_pos.mpr hfan.xpr_neg)
    have hsecond :
        (-sig (v (e 2)) (v (e 7)) (v (e 5))) *
          sig (v (e 3)) (v (e 7)) (v (e 6)) < 0 :=
      mul_neg_of_pos_of_neg (neg_pos.mpr hfan.xpq_neg) hcpr_neg
    have hPQRmul :
        0 < sig (v (e 7)) (v (e 2)) (v (e 3)) *
          sig (v (e 7)) (v (e 5)) (v (e 6)) := by
      rw [hPQRidentity]
      exact sub_pos.mpr (hsecond.trans hfirst)
    have hpqr : 0 < sig (v (e 7)) (v (e 5)) (v (e 6)) :=
      pos_of_mul_pos_right hPQRmul hPXC.le
    exact {
      bpq_pos := hbpq
      xpq_neg := hfan.xpq_neg
      cpq_pos := hcpq
      bpr_pos := hbpr
      xpr_neg := hfan.xpr_neg
      cpr_neg := hcpr_neg
      bqr_pos := hbqr
      xqr_pos := hfan.xqr_pos
      cqr_neg := hcqr_neg
      pqr_pos := hpqr }

/-- Close the canonical CAB packet from a callback for the unique type-717
sign cell.  In the other branch the public same-sector theorem gives the
normalized central bound `21`; the `ABC` and `ACD` min-triangle floors add
the remaining four normalized units. -/
theorem hullFive300_cab_bound_of_717
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hm : 0 < minTri v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hACD : 0 < sig (v (e 0)) (v (e 3)) (v (e 4)))
    (hP : InTriStrict (v (e 7)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hQ : InTriStrict (v (e 5)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hR : InTriStrict (v (e 6)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hfan : HullFive300CabFanPartition v e)
    (h717 : HullFive300Cab717Signs v e →
      minTri v * 25 ≤ 2 *
        (sig (v (e 0)) (v (e 1)) (v (e 2)) +
          sig (v (e 0)) (v (e 2)) (v (e 3)) +
          sig (v (e 0)) (v (e 3)) (v (e 4)))) :
    minTri v * 25 ≤ 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) +
        sig (v (e 0)) (v (e 3)) (v (e 4))) := by
  rcases hullFive300_cab_sameSector_or_717 v e hm hBXC hP hQ hR hfan with
      hsame | hexceptional
  · rcases hsame with ⟨f, hf, hbase, hanchor, hfirst, hsecond⟩
    have hbase_pos : 0 < sig (v (f 0)) (v (f 1)) (v (f 2)) := by
      rw [hbase]
      exact hBXC
    have hcentral := hullFive300_sameSector_central_bound v f hf hm
      hbase_pos hanchor hfirst hsecond
    have hcentralE :
        21 ≤ (2 / minTri v) *
          sig (v (e 1)) (v (e 2)) (v (e 3)) := by
      rw [← hbase]
      exact hcentral
    have hEbound :
        minTri v * 21 ≤
          2 * sig (v (e 1)) (v (e 2)) (v (e 3)) := by
      calc
        minTri v * 21 ≤ minTri v *
            ((2 / minTri v) *
              sig (v (e 1)) (v (e 2)) (v (e 3))) :=
          mul_le_mul_of_nonneg_left hcentralE hm.le
        _ = 2 * sig (v (e 1)) (v (e 2)) (v (e 3)) := by
          field_simp [ne_of_gt hm]
    have hABCfloor :
        minTri v ≤ sig (v (e 0)) (v (e 1)) (v (e 3)) := by
      have hfloor := minTri_le_abs_sig_of_pairwise_ne v
        (a := e 0) (b := e 1) (c := e 3)
        (e.injective.ne (by decide)) (e.injective.ne (by decide))
        (e.injective.ne (by decide))
      simpa [abs_of_pos hABC] using hfloor
    have hACDfloor :
        minTri v ≤ sig (v (e 0)) (v (e 3)) (v (e 4)) := by
      have hfloor := minTri_le_abs_sig_of_pairwise_ne v
        (a := e 0) (b := e 3) (c := e 4)
        (e.injective.ne (by decide)) (e.injective.ne (by decide))
        (e.injective.ne (by decide))
      simpa [abs_of_pos hACD] using hfloor
    have hfanIdentity :
        sig (v (e 0)) (v (e 1)) (v (e 2)) +
            sig (v (e 0)) (v (e 2)) (v (e 3)) =
          sig (v (e 0)) (v (e 1)) (v (e 3)) +
            sig (v (e 1)) (v (e 2)) (v (e 3)) := by
      simp only [sig]
      ring
    nlinarith [hEbound, hABCfloor, hACDfloor, hfanIdentity]
  · exact h717 hexceptional

end Heilbronn8.TriHull
