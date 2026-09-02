import Heilbronn8.TriHull.HullFive300CabGeometry
import Heilbronn8.TriHull.HullFive300RightProfileReduction
import Heilbronn8.CoverGeometry

/-!
# Full profiles supply the CAB fan partition

The exact right-ear profiles place the canonical inner points

`P = C@7`, `Q = A@5`, `R = B@6`

in three disjoint angular bands at `X`.  Barycentric expansion in the two
relevant hull triangles gives `XPQ < 0`, `XPR < 0`, and `XQR > 0`.
Inside the common triangle `BXC`, each of the five remaining sign clauses is
then exactly the three positive subareas characterizing a strict fan sector.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8.TriHull

private lemma cabProfile_inTriStrict_of_fan_pos
    {p a b c : Point}
    (hD : 0 < sig a b c)
    (h1 : 0 < sig p b c)
    (h2 : 0 < sig a p c)
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
          sig p b c * a.1 + sig a p c * b.1 +
            sig a b p * c.1 := by
      simp only [sig]
      ring
    have hx2 :
        p.2 * sig a b c =
          sig p b c * a.2 + sig a p c * b.2 +
            sig a b p * c.2 := by
      simp only [sig]
      ring
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      linarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      linarith

private lemma cabProfile_rotate_pos {a b c : Point}
    (h : 0 < sig a b c) : 0 < sig b c a := by
  have heq : sig b c a = sig a b c := by
    simp only [sig]
    ring
  rw [heq]
  exact h

private lemma cabProfile_rotate2_pos {a b c : Point}
    (h : 0 < sig a b c) : 0 < sig c a b :=
  cabProfile_rotate_pos (cabProfile_rotate_pos h)

private lemma cabProfile_swap12_pos_of_neg {a b c : Point}
    (h : sig a b c < 0) : 0 < sig b a c := by
  have heq : sig b a c = -sig a b c := by
    simp only [sig]
    ring
  rw [heq]
  exact neg_pos.mpr h

private lemma cabProfile_swap13_pos_of_neg {a b c : Point}
    (h : sig a b c < 0) : 0 < sig c b a := by
  have heq : sig c b a = -sig a b c := by
    simp only [sig]
    ring
  rw [heq]
  exact neg_pos.mpr h

private lemma cabProfile_cycle_pos
    (v : Configuration) (e : Fin 8 → Fin 8)
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (i j k : Fin 5) (hij : i < j) (hjk : j < k) :
    0 < sig (v (e (hullFiveSequentialCycleSlot i)))
      (v (e (hullFiveSequentialCycleSlot j)))
      (v (e (hullFiveSequentialCycleSlot k))) := by
  exact hcyc.pos i j k hij hjk

private lemma cabProfile_sig_ne
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hm : 0 < minTri v) {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    sig (v (e i)) (v (e j)) (v (e k)) ≠ 0 := by
  intro hzero
  have hfloor := minTri_le_abs_sig_of_pairwise_ne v
    (a := e i) (b := e j) (c := e k)
    (fun h ↦ hij (e.injective h))
    (fun h ↦ hik (e.injective h))
    (fun h ↦ hjk (e.injective h))
  rw [hzero, abs_zero] at hfloor
  linarith

private lemma cabProfile_neg_of_not_pos
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hm : 0 < minTri v) {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hnot : ¬ 0 < sig (v (e i)) (v (e j)) (v (e k))) :
    sig (v (e i)) (v (e j)) (v (e k)) < 0 :=
  lt_of_le_of_ne (le_of_not_gt hnot)
    (cabProfile_sig_ne v e hm hij hik hjk)

private lemma cabProfile_xpq_neg
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (p : HullFiveEndRightProfileC v e 7)
    (q : HullFiveEndRightProfileA v e 5) :
    sig (v (e 2)) (v (e 7)) (v (e 5)) < 0 := by
  obtain ⟨pa, pb, px, hpa, hpb, _hpx, hsumP, hp⟩ := p.abx
  obtain ⟨qx, qc, qd, _hqx, hqc, hqd, hsumQ, hq⟩ := q.xcd
  have hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 0 2 3 (by decide) (by decide))
  have hAXD : 0 < sig (v (e 0)) (v (e 2)) (v (e 4)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 0 2 4 (by decide) (by decide))
  have hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 1 2 3 (by decide) (by decide))
  have hBXD : 0 < sig (v (e 1)) (v (e 2)) (v (e 4)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 1 2 4 (by decide) (by decide))
  have hXAC : sig (v (e 2)) (v (e 0)) (v (e 3)) < 0 := by
    have heq : sig (v (e 2)) (v (e 0)) (v (e 3)) =
        -sig (v (e 0)) (v (e 2)) (v (e 3)) := by
      simp only [sig]
      ring
    nlinarith
  have hXAD : sig (v (e 2)) (v (e 0)) (v (e 4)) < 0 := by
    have heq : sig (v (e 2)) (v (e 0)) (v (e 4)) =
        -sig (v (e 0)) (v (e 2)) (v (e 4)) := by
      simp only [sig]
      ring
    nlinarith
  have hXBC : sig (v (e 2)) (v (e 1)) (v (e 3)) < 0 := by
    have heq : sig (v (e 2)) (v (e 1)) (v (e 3)) =
        -sig (v (e 1)) (v (e 2)) (v (e 3)) := by
      simp only [sig]
      ring
    nlinarith
  have hXBD : sig (v (e 2)) (v (e 1)) (v (e 4)) < 0 := by
    have heq : sig (v (e 2)) (v (e 1)) (v (e 4)) =
        -sig (v (e 1)) (v (e 2)) (v (e 4)) := by
      simp only [sig]
      ring
    nlinarith
  have hidentity :
      sig (v (e 2)) (v (e 7)) (v (e 5)) =
        pa * qc * sig (v (e 2)) (v (e 0)) (v (e 3)) +
        pa * qd * sig (v (e 2)) (v (e 0)) (v (e 4)) +
        pb * qc * sig (v (e 2)) (v (e 1)) (v (e 3)) +
        pb * qd * sig (v (e 2)) (v (e 1)) (v (e 4)) := by
    have hpxCoeff : px = 1 - pa - pb := by linarith [hsumP]
    have hqxCoeff : qx = 1 - qc - qd := by linarith [hsumQ]
    rw [hp, hq, hpxCoeff, hqxCoeff]
    simp only [sig, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have h0 := mul_neg_of_pos_of_neg (mul_pos hpa hqc) hXAC
  have h1 := mul_neg_of_pos_of_neg (mul_pos hpa hqd) hXAD
  have h2 := mul_neg_of_pos_of_neg (mul_pos hpb hqc) hXBC
  have h3 := mul_neg_of_pos_of_neg (mul_pos hpb hqd) hXBD
  rw [hidentity]
  exact add_neg (add_neg (add_neg h0 h1) h2) h3

private lemma cabProfile_xpr_neg
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (p : HullFiveEndRightProfileC v e 7)
    (r : HullFiveEndRightProfileB v e 6) :
    sig (v (e 2)) (v (e 7)) (v (e 6)) < 0 := by
  obtain ⟨pa, pb, px, hpa, hpb, _hpx, hsumP, hp⟩ := p.abx
  obtain ⟨rx, rd, ra, _hrx, hrd, hra, hsumR, hr⟩ := r.xda
  have hAXD : 0 < sig (v (e 0)) (v (e 2)) (v (e 4)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 0 2 4 (by decide) (by decide))
  have hBXD : 0 < sig (v (e 1)) (v (e 2)) (v (e 4)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 1 2 4 (by decide) (by decide))
  have hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 0 1 2 (by decide) (by decide))
  have hXAD : sig (v (e 2)) (v (e 0)) (v (e 4)) < 0 := by
    have heq : sig (v (e 2)) (v (e 0)) (v (e 4)) =
        -sig (v (e 0)) (v (e 2)) (v (e 4)) := by
      simp only [sig]
      ring
    nlinarith
  have hXBD : sig (v (e 2)) (v (e 1)) (v (e 4)) < 0 := by
    have heq : sig (v (e 2)) (v (e 1)) (v (e 4)) =
        -sig (v (e 1)) (v (e 2)) (v (e 4)) := by
      simp only [sig]
      ring
    nlinarith
  have hXBA : sig (v (e 2)) (v (e 1)) (v (e 0)) < 0 := by
    have heq : sig (v (e 2)) (v (e 1)) (v (e 0)) =
        -sig (v (e 0)) (v (e 1)) (v (e 2)) := by
      simp only [sig]
      ring
    nlinarith
  have hidentity :
      sig (v (e 2)) (v (e 7)) (v (e 6)) =
        pa * rd * sig (v (e 2)) (v (e 0)) (v (e 4)) +
        pb * rd * sig (v (e 2)) (v (e 1)) (v (e 4)) +
        pb * ra * sig (v (e 2)) (v (e 1)) (v (e 0)) := by
    have hpxCoeff : px = 1 - pa - pb := by linarith [hsumP]
    have hrxCoeff : rx = 1 - rd - ra := by linarith [hsumR]
    rw [hp, hr, hpxCoeff, hrxCoeff]
    simp only [sig, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have h0 := mul_neg_of_pos_of_neg (mul_pos hpa hrd) hXAD
  have h1 := mul_neg_of_pos_of_neg (mul_pos hpb hrd) hXBD
  have h2 := mul_neg_of_pos_of_neg (mul_pos hpb hra) hXBA
  rw [hidentity]
  exact add_neg (add_neg h0 h1) h2

private lemma cabProfile_xqr_pos
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (q : HullFiveEndRightProfileA v e 5)
    (r : HullFiveEndRightProfileB v e 6) :
    0 < sig (v (e 2)) (v (e 5)) (v (e 6)) := by
  obtain ⟨qx, qc, qd, _hqx, hqc, hqd, hsumQ, hq⟩ := q.xcd
  obtain ⟨rx, rd, ra, _hrx, hrd, hra, hsumR, hr⟩ := r.xda
  have hXCD : 0 < sig (v (e 2)) (v (e 3)) (v (e 4)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 2 3 4 (by decide) (by decide))
  have hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 0 2 3 (by decide) (by decide))
  have hAXD : 0 < sig (v (e 0)) (v (e 2)) (v (e 4)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 0 2 4 (by decide) (by decide))
  have hXCA := cabProfile_rotate_pos hAXC
  have hXDA := cabProfile_rotate_pos hAXD
  have hidentity :
      sig (v (e 2)) (v (e 5)) (v (e 6)) =
        qc * rd * sig (v (e 2)) (v (e 3)) (v (e 4)) +
        qc * ra * sig (v (e 2)) (v (e 3)) (v (e 0)) +
        qd * ra * sig (v (e 2)) (v (e 4)) (v (e 0)) := by
    have hqxCoeff : qx = 1 - qc - qd := by linarith [hsumQ]
    have hrxCoeff : rx = 1 - rd - ra := by linarith [hsumR]
    rw [hq, hr, hqxCoeff, hrxCoeff]
    simp only [sig, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have h0 := mul_pos (mul_pos hqc hrd) hXCD
  have h1 := mul_pos (mul_pos hqc hra) hXCA
  have h2 := mul_pos (mul_pos hqd hra) hXDA
  rw [hidentity]
  exact add_pos (add_pos h0 h1) h2

/-- Exact full right-ear profiles supply the small CAB fan-partition packet. -/
theorem hullFive300CabFanPartition_of_profiles
    (v : Configuration) (e : Equiv.Perm (Fin 8))
    (hm : 0 < minTri v)
    (hcyc : StrictCyclicPos hullFiveSequentialCycleSlot
      (fun i ↦ v (e i)))
    (q : HullFiveEndRightProfileA v e 5)
    (r : HullFiveEndRightProfileB v e 6)
    (p : HullFiveEndRightProfileC v e 7) :
    HullFive300CabFanPartition v e := by
  have hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 1 2 3 (by decide) (by decide))
  have hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 0 1 2 (by decide) (by decide))
  have hBXD : 0 < sig (v (e 1)) (v (e 2)) (v (e 4)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 1 2 4 (by decide) (by decide))
  have hDBX : 0 < sig (v (e 4)) (v (e 1)) (v (e 2)) :=
    cabProfile_rotate2_pos hBXD
  obtain ⟨hPXC, hPCB, _hPBX⟩ := inTriStrict_fan_pos hBXC p.bxc
  obtain ⟨hQXC, hQCB, hQBX⟩ := inTriStrict_fan_pos hBXC q.bxc
  obtain ⟨hRXC, hRCB, _hRBX⟩ := inTriStrict_fan_pos hBXC r.bxc
  obtain ⟨hPBX, _, _⟩ := inTriStrict_fan_pos hABX p.abx
  obtain ⟨hRBX, _, _⟩ := inTriStrict_fan_pos hDBX r.dbx
  have hxpq := cabProfile_xpq_neg v e hcyc p q
  have hxpr := cabProfile_xpr_neg v e hcyc p r
  have hxqr := cabProfile_xqr_pos v e hcyc q r
  refine {
    xpq_neg := hxpq
    xpr_neg := hxpr
    xqr_pos := hxqr
    pxc_of_bits := ?_
    pcb_of_bits := ?_
    qcb_of_bits := ?_
    qbx_of_bits := ?_
    rcb_of_bits := ?_ }
  · rintro ⟨hcpq, hcpr⟩
    have hPQC := cabProfile_rotate_pos hcpq
    have hPRC := cabProfile_rotate_pos hcpr
    have hPXQ := cabProfile_swap12_pos_of_neg hxpq
    have hPXR := cabProfile_swap12_pos_of_neg hxpr
    exact ⟨
      cabProfile_inTriStrict_of_fan_pos hPXC hQXC hPQC hPXQ,
      cabProfile_inTriStrict_of_fan_pos hPXC hRXC hPRC hPXR⟩
  · rintro ⟨hncpq, hbpq, hncpr, hbpr⟩
    have hcpq_neg := cabProfile_neg_of_not_pos v e hm
      (i := 3) (j := 7) (k := 5)
      (by decide) (by decide) (by decide) hncpq
    have hcpr_neg := cabProfile_neg_of_not_pos v e hm
      (i := 3) (j := 7) (k := 6)
      (by decide) (by decide) (by decide) hncpr
    have hPQB := cabProfile_rotate_pos hbpq
    have hPRB := cabProfile_rotate_pos hbpr
    have hPCQ := cabProfile_swap12_pos_of_neg hcpq_neg
    have hPCR := cabProfile_swap12_pos_of_neg hcpr_neg
    exact ⟨
      cabProfile_inTriStrict_of_fan_pos hPCB hQCB hPQB hPCQ,
      cabProfile_inTriStrict_of_fan_pos hPCB hRCB hPRB hPCR⟩
  · rintro ⟨hcpq, hnbpq, hncqr, hbqr⟩
    have hbpq_neg := cabProfile_neg_of_not_pos v e hm
      (i := 1) (j := 7) (k := 5)
      (by decide) (by decide) (by decide) hnbpq
    have hcqr_neg := cabProfile_neg_of_not_pos v e hm
      (i := 3) (j := 5) (k := 6)
      (by decide) (by decide) (by decide) hncqr
    have hQPB := cabProfile_swap13_pos_of_neg hbpq_neg
    have hQCP := cabProfile_rotate2_pos hcpq
    have hQRB := cabProfile_rotate_pos hbqr
    have hQCR := cabProfile_swap12_pos_of_neg hcqr_neg
    exact ⟨
      cabProfile_inTriStrict_of_fan_pos hQCB hPCB hQPB hQCP,
      cabProfile_inTriStrict_of_fan_pos hQCB hRCB hQRB hQCR⟩
  · rintro ⟨hbpq, hnbqr⟩
    have hbqr_neg := cabProfile_neg_of_not_pos v e hm
      (i := 1) (j := 5) (k := 6)
      (by decide) (by decide) (by decide) hnbqr
    have hQPX := cabProfile_swap13_pos_of_neg hxpq
    have hQBP := cabProfile_rotate2_pos hbpq
    have hQRX := cabProfile_rotate_pos hxqr
    have hQBR := cabProfile_swap12_pos_of_neg hbqr_neg
    exact ⟨
      cabProfile_inTriStrict_of_fan_pos hQBX hPBX hQPX hQBP,
      cabProfile_inTriStrict_of_fan_pos hQBX hRBX hQRX hQBR⟩
  · rintro ⟨hcpr, hnbpr, hcqr, hnbqr⟩
    have hbpr_neg := cabProfile_neg_of_not_pos v e hm
      (i := 1) (j := 7) (k := 6)
      (by decide) (by decide) (by decide) hnbpr
    have hbqr_neg := cabProfile_neg_of_not_pos v e hm
      (i := 1) (j := 5) (k := 6)
      (by decide) (by decide) (by decide) hnbqr
    have hRPB := cabProfile_swap13_pos_of_neg hbpr_neg
    have hRCP := cabProfile_rotate2_pos hcpr
    have hRQB := cabProfile_swap13_pos_of_neg hbqr_neg
    have hRCQ := cabProfile_rotate2_pos hcqr
    exact ⟨
      cabProfile_inTriStrict_of_fan_pos hRCB hPCB hRPB hRCP,
      cabProfile_inTriStrict_of_fan_pos hRCB hQCB hRQB hRCQ⟩

/-- A callback for the unique CAB type-717 sign cell supplies the complete
canonical CAB endpoint. -/
theorem hullFive300CABUniversalBound_of_717
    (h717 : ∀ (v : Configuration) (e : Equiv.Perm (Fin 8)),
      0 < minTri v →
      StrictCyclicPos hullFiveSequentialCycleSlot (fun i ↦ v (e i)) →
      HullFiveEndRightProfileA v e 5 →
      HullFiveEndRightProfileB v e 6 →
      HullFiveEndRightProfileC v e 7 →
      HullFive300Cab717Signs v e →
      minTri v * 25 ≤ 2 *
        (sig (v (e 0)) (v (e 1)) (v (e 2)) +
          sig (v (e 0)) (v (e 2)) (v (e 3)) +
          sig (v (e 0)) (v (e 3)) (v (e 4)))) :
    HullFive300CABUniversalBound := by
  intro v e hm hcyc q r p
  have hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 0 1 3 (by decide) (by decide))
  have hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 1 2 3 (by decide) (by decide))
  have hACD : 0 < sig (v (e 0)) (v (e 3)) (v (e 4)) := by
    simpa [hullFiveSequentialCycleSlot] using
      (cabProfile_cycle_pos v e hcyc 0 3 4 (by decide) (by decide))
  apply hullFive300_cab_bound_of_717 v e hm hABC hBXC hACD
    p.bxc q.bxc r.bxc
    (hullFive300CabFanPartition_of_profiles v e hm hcyc q r p)
  exact h717 v e hm hcyc q r p

#print axioms hullFive300CabFanPartition_of_profiles
#print axioms hullFive300CABUniversalBound_of_717

end Heilbronn8.TriHull
