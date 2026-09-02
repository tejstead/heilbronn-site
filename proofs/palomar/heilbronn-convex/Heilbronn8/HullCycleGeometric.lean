import Heilbronn8.HullCycleOrder
import Heilbronn8.HullDispatchGeometry

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-!
# Geometric hull cycles as strict sign certificates

`FanCovers` records ordinary barycentric containment, whereas
`HullCycleOf` asks for containment derived from the canonical strict sign
oracle.  In general position these interfaces agree: a contained labelled
point which is not one of the triangle vertices cannot lie on an edge, so
all three subtriangle determinants are strictly positive.
-/

/-- Barycentric containment in a positively oriented triangle makes the
three subtriangle determinants nonnegative. -/
lemma inTri_oriented_signs_nonneg
    {p a b c : ℝ × ℝ} (hp : InTri p a b c)
    (habc : 0 ≤ sig a b c) :
    0 ≤ sig p b c ∧ 0 ≤ sig a p c ∧ 0 ≤ sig a b p := by
  obtain ⟨x, y, z, hx, hy, hz, hxyz, rfl⟩ := hp
  constructor
  · rw [sig_affine_fst a b c b c x y z hxyz]
    simpa [sig] using mul_nonneg hx habc
  constructor
  · rw [sig_rotate a (x • a + y • b + z • c) c,
      sig_affine_fst a b c c a x y z hxyz,
      ← sig_rotate a b c]
    simpa [sig] using mul_nonneg hy habc
  · rw [sig_rotate a b (x • a + y • b + z • c),
      sig_rotate b (x • a + y • b + z • c) a,
      sig_affine_fst a b c a b x y z hxyz,
      sig_rotate c a b]
    simpa [sig] using mul_nonneg hz habc

/-- In a strict configuration, ordinary containment of an off-cycle point
in a positively oriented cycle triangle is already a direct sign
certificate. -/
lemma directInTriSigns_of_inTri_of_strict
    {v : Configuration} (hstrict : AllTripleSignsStrict v)
    {p a b c : Fin 8}
    (hpab : p ≠ a) (hpac : p ≠ b) (hpad : p ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habc : 0 < sig (v a) (v b) (v c))
    (hp : InTri (v p) (v a) (v b) (v c)) :
    DirectInTriSigns
      (StrictSignData.ofAllTripleSignsStrict v hstrict) p a b c := by
  obtain ⟨hpbc, hapc, habp⟩ :=
    inTri_oriented_signs_nonneg hp habc.le
  have hpbcNe : sig (v p) (v b) (v c) ≠ 0 :=
    hstrict.sig_ne_of_pairwise_ne hpac hpad hbc
  have hapcNe : sig (v a) (v p) (v c) ≠ 0 :=
    hstrict.sig_ne_of_pairwise_ne hpab.symm hac hpad
  have habpNe : sig (v a) (v b) (v p) ≠ 0 :=
    hstrict.sig_ne_of_pairwise_ne hab hpab.symm hpac.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      (StrictSignData.ofAllTripleSignsStrict_ccw v hstrict a b c).2 habc
  · exact
      (StrictSignData.ofAllTripleSignsStrict_ccw v hstrict p b c).2
        (lt_of_le_of_ne hpbc (Ne.symm hpbcNe))
  · exact
      (StrictSignData.ofAllTripleSignsStrict_ccw v hstrict a p c).2
        (lt_of_le_of_ne hapc (Ne.symm hapcNe))
  · exact
      (StrictSignData.ofAllTripleSignsStrict_ccw v hstrict a b p).2
        (lt_of_le_of_ne habp (Ne.symm habpNe))

/-- A geometric strict cycle with a semantic fan cover determines the
canonical `HullCycleOf` certificate. -/
theorem HullCycleOf.ofGeometric
    {v : Configuration} (hstrict : AllTripleSignsStrict v)
    (d : HullCycleData)
    (hdInjective : Function.Injective d.get)
    (hcyc : StrictCyclicPos d.get v)
    (hfan : FanCovers v d.get) :
    HullCycleOf (StrictSignData.ofAllTripleSignsStrict v hstrict) d := by
  refine ⟨List.nodup_iff_injective_get.mpr hdInjective, ?_, ?_⟩
  · intro i j k hij hjk
    exact
      (StrictSignData.ofAllTripleSignsStrict_ccw v hstrict
        (d.get i) (d.get j) (d.get k)).2
        (hcyc.pos i j k hij hjk)
  · intro p hpOutside
    obtain ⟨i, j, hi, hij, hp⟩ := hfan p hpOutside
    have h0i : d.get 0 ≠ d.get i := by
      intro h
      exact (ne_of_lt hi) (hdInjective h)
    have h0j : d.get 0 ≠ d.get j := by
      intro h
      exact (ne_of_lt (lt_trans hi hij)) (hdInjective h)
    have hijLabels : d.get i ≠ d.get j := by
      intro h
      exact (ne_of_lt hij) (hdInjective h)
    have hp0 : p ≠ d.get 0 := by
      intro h
      exact hpOutside ⟨0, h.symm⟩
    have hpi : p ≠ d.get i := by
      intro h
      exact hpOutside ⟨i, h.symm⟩
    have hpj : p ≠ d.get j := by
      intro h
      exact hpOutside ⟨j, h.symm⟩
    refine ⟨i, j, hi, hij, InTriBySigns.direct ?_⟩
    exact directInTriSigns_of_inTri_of_strict hstrict
      hp0 hpi hpj h0i h0j hijLabels
      (hcyc.pos 0 i j hi hij) hp

end Heilbronn8
