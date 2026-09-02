import Heilbronn8.QuadHull.Occupancy
import Heilbronn8.QuadHull.OrbitIISemanticPrimitive

/-!
# Geometric realization of the four diagonal sectors

This is the geometric half of `SectorCensus.classifyFourSectors`.  A point
strictly inside one of the two `AC` fan triangles and not on `BD` belongs to
one of the four open sectors.  The theorem below returns the actual strict
triangle memberships, not merely an abstract sector number.

It does not yet select the four off-hull labels or dispatch the resulting
census to a hull-bound producer.
-/

namespace Heilbronn8.QuadHull

/-- The four open sectors `ABO`, `BCO`, `CDO`, `DAO`, expressed without
naming the diagonal intersection `O`. -/
def StrictQuadSector (X A B C D : Point) : Fin 4 → Prop :=
  fun i ↦
    match i.val with
    | 0 =>
        TriHull.InTriStrict X A B C ∧
          TriHull.InTriStrict X D A B
    | 1 =>
        TriHull.InTriStrict X A B C ∧
          TriHull.InTriStrict X B C D
    | 2 =>
        TriHull.InTriStrict X B C D ∧
          TriHull.InTriStrict X A C D
    | _ =>
        TriHull.InTriStrict X A C D ∧
          TriHull.InTriStrict X D A B

/-- Cyclically rotate a strict triangle membership. -/
theorem inTriStrict_rotate {X A B C : Point}
    (h : TriHull.InTriStrict X A B C) :
    TriHull.InTriStrict X B C A := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hX⟩ := h
  refine ⟨y, z, x, hy, hz, hx, by linarith, ?_⟩
  rw [hX]
  module

/-- Rotate a strict triangle membership twice. -/
theorem inTriStrict_rotateTwo {X A B C : Point}
    (h : TriHull.InTriStrict X A B C) :
    TriHull.InTriStrict X C A B :=
  inTriStrict_rotate (inTriStrict_rotate h)

/-- A strict point in the `AC` hull fan, together with non-incidence on
`BD`, lies in an actual open diagonal sector. -/
theorem strictQuadSector_exists
    {X A B C D : Point}
    (hccw : CCWQuad A B C D)
    (hinside : TriHull.InTriStrict X A B C ∨
      TriHull.InTriStrict X A C D)
    (hBDXne : sig B D X ≠ 0) :
    ∃ i : Fin 4, StrictQuadSector X A B C D i := by
  have hABD : 0 < sig A B D := by
    calc
      0 < sig D A B := hccw.2.2.2
      _ = sig A B D := sig_rotate _ _ _
  have hACD : 0 < sig A C D := by
    calc
      0 < sig C D A := hccw.2.2.1
      _ = sig D A C := sig_rotate _ _ _
      _ = sig A C D := sig_rotate _ _ _
  rcases hinside with hABCinside | hACDinside
  · obtain ⟨hXBC, _hXCA, hXAB⟩ :=
      TriHull.inTriStrict_fan_pos hccw.1 hABCinside
    have hABCcoordinates := hABCinside
    obtain ⟨x, y, z, hx, hy, hz, hsum, hX⟩ := hABCcoordinates
    have hXDA : 0 < sig X D A := by
      rw [hX, sig_affine_fst A B C D A x y z hsum]
      simp only [sig_eq13, mul_zero, zero_add]
      exact add_pos (mul_pos hy (by
        calc
          0 < sig D A B := hccw.2.2.2
          _ = sig A B D := sig_rotate _ _ _
          _ = sig B D A := sig_rotate _ _ _))
        (mul_pos hz hccw.2.2.1)
    have hAXD : 0 < sig A X D := by
      calc
        0 < sig X D A := hXDA
        _ = sig D A X := sig_rotate _ _ _
        _ = sig A X D := sig_rotate _ _ _
    have hABX : 0 < sig A B X := by
      calc
        0 < sig X A B := hXAB
        _ = sig A B X := sig_rotate _ _ _
    have hXCD : 0 < sig X C D := by
      rw [hX, sig_affine_fst A B C C D x y z hsum]
      simp only [sig_eq12, mul_zero, add_zero]
      exact add_pos (mul_pos hx hACD) (mul_pos hy hccw.2.1)
    by_cases hBDX : 0 < sig B D X
    · have hXBD : 0 < sig X B D := by
        calc
          0 < sig B D X := hBDX
          _ = sig D X B := sig_rotate _ _ _
          _ = sig X B D := sig_rotate _ _ _
      have hABDinside : TriHull.InTriStrict X A B D :=
        OrbitIIInternal.inTriStrict_of_fan_pos
          hABD hXBD hAXD hABX
      refine ⟨0, ?_⟩
      exact ⟨hABCinside, inTriStrict_rotateTwo hABDinside⟩
    · have hBDXneg : sig B D X < 0 :=
        lt_of_le_of_ne (le_of_not_gt hBDX) hBDXne
      have hBXD : 0 < sig B X D := by
        rw [sig_swap]
        linarith
      have hBCX : 0 < sig B C X := by
        calc
          0 < sig X B C := hXBC
          _ = sig B C X := sig_rotate _ _ _
      have hBCDinside : TriHull.InTriStrict X B C D :=
        OrbitIIInternal.inTriStrict_of_fan_pos
          hccw.2.1 hXCD hBXD hBCX
      refine ⟨1, ?_⟩
      exact ⟨hABCinside, hBCDinside⟩
  · obtain ⟨hXCD, hXDA, _hXAC⟩ :=
      TriHull.inTriStrict_fan_pos hACD hACDinside
    have hACDcoordinates := hACDinside
    obtain ⟨x, y, z, hx, hy, hz, hsum, hX⟩ := hACDcoordinates
    have hXAB : 0 < sig X A B := by
      rw [hX, sig_affine_fst A C D A B x y z hsum]
      simp only [sig_eq12, mul_zero, zero_add]
      have hCAB : 0 < sig C A B := by
        calc
          0 < sig A B C := hccw.1
          _ = sig B C A := sig_rotate _ _ _
          _ = sig C A B := sig_rotate _ _ _
      exact add_pos (mul_pos hy hCAB) (mul_pos hz hccw.2.2.2)
    have hABX : 0 < sig A B X := by
      calc
        0 < sig X A B := hXAB
        _ = sig A B X := sig_rotate _ _ _
    have hAXD : 0 < sig A X D := by
      calc
        0 < sig X D A := hXDA
        _ = sig D A X := sig_rotate _ _ _
        _ = sig A X D := sig_rotate _ _ _
    have hXBC : 0 < sig X B C := by
      rw [hX, sig_affine_fst A C D B C x y z hsum]
      simp only [sig_eq13, mul_zero, add_zero]
      have hDBC : 0 < sig D B C := by
        calc
          0 < sig B C D := hccw.2.1
          _ = sig C D B := sig_rotate _ _ _
          _ = sig D B C := sig_rotate _ _ _
      exact add_pos (mul_pos hx hccw.1) (mul_pos hz hDBC)
    have hBCX : 0 < sig B C X := by
      calc
        0 < sig X B C := hXBC
        _ = sig B C X := sig_rotate _ _ _
    by_cases hBDX : 0 < sig B D X
    · have hXBD : 0 < sig X B D := by
        calc
          0 < sig B D X := hBDX
          _ = sig D X B := sig_rotate _ _ _
          _ = sig X B D := sig_rotate _ _ _
      have hABDinside : TriHull.InTriStrict X A B D :=
        OrbitIIInternal.inTriStrict_of_fan_pos
          hABD hXBD hAXD hABX
      refine ⟨3, ?_⟩
      exact ⟨hACDinside, inTriStrict_rotateTwo hABDinside⟩
    · have hBDXneg : sig B D X < 0 :=
        lt_of_le_of_ne (le_of_not_gt hBDX) hBDXne
      have hBXD : 0 < sig B X D := by
        rw [sig_swap]
        linarith
      have hBCDinside : TriHull.InTriStrict X B C D :=
        OrbitIIInternal.inTriStrict_of_fan_pos
          hccw.2.1 hXCD hBXD hBCX
      refine ⟨2, ?_⟩
      exact ⟨hBCDinside, hACDinside⟩

/-- Proof-relevant geometric realization of an abstract four-sector
assignment.  Keeping the witnesses attached prevents a later finite census
dispatcher from forgetting which strict triangle memberships justified its
sector numbers. -/
structure StrictQuadSectorAssignment
    (inner : Fin 4 → Point) (A B C D : Point) where
  assignment : SectorCensus.Assignment
  realizes : ∀ x : Fin 4,
    StrictQuadSector (inner x) A B C D (assignment x)

/-- Package the pointwise sector choices into one witness-rich assignment. -/
theorem strictQuadSectorAssignment_exists
    {inner : Fin 4 → Point} {A B C D : Point}
    (hccw : CCWQuad A B C D)
    (hinside : ∀ x : Fin 4,
      TriHull.InTriStrict (inner x) A B C ∨
        TriHull.InTriStrict (inner x) A C D)
    (hBDne : ∀ x : Fin 4, sig B D (inner x) ≠ 0) :
    Nonempty (StrictQuadSectorAssignment inner A B C D) := by
  classical
  have hsector : ∀ x : Fin 4,
      ∃ s : Fin 4, StrictQuadSector (inner x) A B C D s :=
    fun x ↦ strictQuadSector_exists hccw (hinside x) (hBDne x)
  choose assignment realizes using hsector
  exact ⟨⟨assignment, realizes⟩⟩

/-- The abstract finite census applies to every geometric assignment, while
the `realizes` field retains the strict memberships needed by the branch
producers. -/
theorem StrictQuadSectorAssignment.classified
    {inner : Fin 4 → Point} {A B C D : Point}
    (h : StrictQuadSectorAssignment inner A B C D) :
    SectorCensus.Classified (SectorCensus.census h.assignment) :=
  SectorCensus.classifyFourSectors h.assignment

end Heilbronn8.QuadHull
