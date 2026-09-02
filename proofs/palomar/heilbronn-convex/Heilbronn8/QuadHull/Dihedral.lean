import Heilbronn8.QuadHull.Main

/-!
# Dihedral transport for quadrilateral certificates

`SectorCensus.classifyFourSectors` classifies occupancies up to the full
dihedral group, while `CCWQuad` and the record-level joins keep a fixed
counterclockwise orientation.  This module supplies the missing sound
transport layer.  A cyclic relabelling leaves the normalized hull area
unchanged.  A reflection of the plane, together with reversal of the four
hull labels, also leaves both `minTri` and the positive quadrilateral area
unchanged.

No occupancy classification is asserted here.
-/

namespace Heilbronn8.QuadHull

/-- A fixed orientation-reversing linear isometry of the plane. -/
@[simp] def mirrorPoint (p : Point) : Point := (-p.1, p.2)

/-- Apply `mirrorPoint` pointwise to an eight-point configuration. -/
@[simp] def mirrorConfiguration (v : Fin 8 → Point) : Fin 8 → Point :=
  fun i ↦ mirrorPoint (v i)

@[simp] theorem mirrorPoint_involutive (p : Point) :
    mirrorPoint (mirrorPoint p) = p := by
  cases p
  simp [mirrorPoint]

@[simp] theorem sig_mirrorPoint (P Q R : Point) :
    sig (mirrorPoint P) (mirrorPoint Q) (mirrorPoint R) =
      -sig P Q R := by
  simp [mirrorPoint, sig]
  ring

/-- Strict barycentric membership is preserved by the reflection. -/
theorem inTriStrict_mirrorPoint {P A B C : Point}
    (h : TriHull.InTriStrict P A B C) :
    TriHull.InTriStrict (mirrorPoint P)
      (mirrorPoint A) (mirrorPoint B) (mirrorPoint C) := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hP⟩ := h
  refine ⟨x, y, z, hx, hy, hz, hsum, ?_⟩
  rw [hP]
  apply Prod.ext <;>
    simp [mirrorPoint, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_add, Prod.snd_add, smul_eq_mul] <;>
    ring

/-- Strict barycentric membership is insensitive to reversing two triangle
vertices.  Together with cyclic rotation, this supplies all six vertex
permutations needed when a reflected sector chart is put back into canonical
counterclockwise order. -/
theorem inTriStrict_swap {P A B C : Point}
    (h : TriHull.InTriStrict P A B C) :
    TriHull.InTriStrict P A C B := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, hP⟩ := h
  refine ⟨x, z, y, hx, hz, hy, by linarith, ?_⟩
  rw [hP]
  module

/-- Reflection followed by an odd triangle relabelling preserves strict
membership.  This is the primitive used by reflected hull-sector charts. -/
theorem inTriStrict_mirrorSwap {P A B C : Point}
    (h : TriHull.InTriStrict P A B C) :
    TriHull.InTriStrict (mirrorPoint P)
      (mirrorPoint A) (mirrorPoint C) (mirrorPoint B) :=
  inTriStrict_swap (inTriStrict_mirrorPoint h)

/-- Reversing the hull labels compensates for the orientation reversal. -/
theorem ccwQuad_mirrorReverse {A B C D : Point}
    (h : CCWQuad A B C D) :
    CCWQuad (mirrorPoint A) (mirrorPoint D)
      (mirrorPoint C) (mirrorPoint B) := by
  have hACD : 0 < sig A C D := by
    calc
      0 < sig C D A := h.2.2.1
      _ = sig D A C := sig_rotate _ _ _
      _ = sig A C D := sig_rotate _ _ _
  have hDBC : 0 < sig D B C := by
    calc
      0 < sig B C D := h.2.1
      _ = sig C D B := sig_rotate _ _ _
      _ = sig D B C := sig_rotate _ _ _
  have hCAB : 0 < sig C A B := by
    calc
      0 < sig A B C := h.1
      _ = sig B C A := sig_rotate _ _ _
      _ = sig C A B := sig_rotate _ _ _
  have hBDA : 0 < sig B D A := by
    calc
      0 < sig D A B := h.2.2.2
      _ = sig A B D := sig_rotate _ _ _
      _ = sig B D A := sig_rotate _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      0 < sig A C D := hACD
      _ = sig (mirrorPoint A) (mirrorPoint D) (mirrorPoint C) := by
        simp only [sig_mirrorPoint]
        simp only [sig]
        ring
  · calc
      0 < sig D B C := hDBC
      _ = sig (mirrorPoint D) (mirrorPoint C) (mirrorPoint B) := by
        simp only [sig_mirrorPoint]
        simp only [sig]
        ring
  · calc
      0 < sig C A B := hCAB
      _ = sig (mirrorPoint C) (mirrorPoint B) (mirrorPoint A) := by
        simp only [sig_mirrorPoint]
        simp only [sig]
        ring
  · calc
      0 < sig B D A := hBDA
      _ = sig (mirrorPoint B) (mirrorPoint A) (mirrorPoint D) := by
        simp only [sig_mirrorPoint]
        simp only [sig]
        ring

/-- Reflection preserves every absolute triple determinant and hence its
finite minimum. -/
theorem minTri_mirrorConfiguration (v : Fin 8 → Point) :
    minTri (mirrorConfiguration v) = minTri v := by
  apply le_antisymm
  · apply le_minTri
    intro i j k hij hjk
    simpa only [mirrorConfiguration, sig_mirrorPoint, abs_neg] using
      (minTri_le (mirrorConfiguration v) hij hjk)
  · apply le_minTri
    intro i j k hij hjk
    have hmin := minTri_le v hij hjk
    simpa only [mirrorConfiguration, sig_mirrorPoint, abs_neg] using hmin

/-- One cyclic step does not change the oriented quadrilateral area. -/
theorem quadHullArea_rotate (A B C D : Point) :
    quadHullArea B C D A = quadHullArea A B C D := by
  simp only [quadHullArea, oarea, sig]
  ring

/-- Reflection plus reversal does not change the positive quadrilateral
area. -/
theorem quadHullArea_mirrorReverse (A B C D : Point) :
    quadHullArea (mirrorPoint A) (mirrorPoint D)
        (mirrorPoint C) (mirrorPoint B) =
      quadHullArea A B C D := by
  simp only [quadHullArea, oarea, sig_mirrorPoint]
  simp only [sig]
  ring

/-- Transport a certificate back across one cyclic relabelling. -/
theorem OrbitCertificate.rotateBack
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitCertificate v B C D A) :
    OrbitCertificate v A B C D := by
  rcases h with hzero | ⟨H, hscale, hcase⟩
  · exact Or.inl hzero
  · refine Or.inr ⟨H, ?_, hcase⟩
    rw [quadHullArea_rotate] at hscale
    exact hscale

/-- Transport a certificate on the mirrored, reversed hull back to the
original counterclockwise hull. -/
theorem OrbitCertificate.mirrorReverseBack
    {v : Fin 8 → Point} {A B C D : Fin 8}
    (h : OrbitCertificate (mirrorConfiguration v) A D C B) :
    OrbitCertificate v A B C D := by
  rcases h with hzero | ⟨H, hscale, hcase⟩
  · apply Or.inl
    rw [minTri_mirrorConfiguration] at hzero
    exact hzero
  · refine Or.inr ⟨H, ?_, hcase⟩
    rw [minTri_mirrorConfiguration] at hscale
    change quadHullArea (mirrorPoint (v A)) (mirrorPoint (v D))
        (mirrorPoint (v C)) (mirrorPoint (v B)) =
      minTri v / 2 * H at hscale
    rw [quadHullArea_mirrorReverse] at hscale
    exact hscale

end Heilbronn8.QuadHull
