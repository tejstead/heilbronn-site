import Heilbronn8.Survivors.Join.HullSixTwoFourGeometryCore
import Heilbronn8.Survivors.Join.HullSixTwoFourWideGeometryIdentities

/-!
# Geometric adapter for nonadjacent wide `2 + 4` products

The wide-product scalar theorem needs a selected lower face and the two hull
faces left by retriangulating the lower pentagon.  There are only three
nonadjacent lower chords: `L0-L2`, `L1-L3`, and `L0-L3`.  This file performs
that finite geometric seam once and leaves chamber recognition to a small
Ferrers-table wrapper.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8

/-- The three nonadjacent lower chords in a four-vertex lower block. -/
inductive HullSixTwoFourWideChord
  | lower02
  | lower13
  | lower03
  deriving DecidableEq, Repr

instance : Fintype HullSixTwoFourWideChord where
  elems := {.lower02, .lower13, .lower03}
  complete x := by cases x <;> simp

def HullSixTwoFourWideChord.left : HullSixTwoFourWideChord → Fin 4
  | .lower02 => 0
  | .lower13 => 1
  | .lower03 => 0

def HullSixTwoFourWideChord.right : HullSixTwoFourWideChord → Fin 4
  | .lower02 => 2
  | .lower13 => 3
  | .lower03 => 3

/-- Selected lower face. -/
noncomputable def HullSixTwoFourWideChord.face
    (W : HullSixTwoFourWideChord) (P : ℝ × ℝ)
    (L : Fin 4 → ℝ × ℝ) : ℝ :=
  sig P (L W.left) (L W.right)

/-- First remaining lower face after retriangulation. -/
noncomputable def HullSixTwoFourWideChord.remainder0
    (W : HullSixTwoFourWideChord) (P : ℝ × ℝ)
    (L : Fin 4 → ℝ × ℝ) : ℝ :=
  match W with
  | .lower02 => sig (L 0) (L 1) (L 2)
  | .lower13 => sig P (L 0) (L 1)
  | .lower03 => sig (L 0) (L 1) (L 2)

/-- Second remaining lower face after retriangulation. -/
noncomputable def HullSixTwoFourWideChord.remainder1
    (W : HullSixTwoFourWideChord) (P : ℝ × ℝ)
    (L : Fin 4 → ℝ × ℝ) : ℝ :=
  match W with
  | .lower02 => sig P (L 2) (L 3)
  | .lower13 => sig (L 1) (L 2) (L 3)
  | .lower03 => sig (L 0) (L 2) (L 3)

/-- The three selected lower chords really give the required lower-pentagon
retriangulations. -/
theorem hullSixTwoFourWideChord_retriangulation
    (W : HullSixTwoFourWideChord) (P : ℝ × ℝ)
    (L : Fin 4 → ℝ × ℝ) :
    sig P (L 0) (L 1) + sig P (L 1) (L 2) + sig P (L 2) (L 3) =
      W.face P L + W.remainder0 P L + W.remainder1 P L := by
  cases W with
  | lower02 =>
      simpa [HullSixTwoFourWideChord.face,
        HullSixTwoFourWideChord.left, HullSixTwoFourWideChord.right,
        HullSixTwoFourWideChord.remainder0,
        HullSixTwoFourWideChord.remainder1] using
          hullSixTwoFour_lower_retriangulation_02 P (L 0) (L 1) (L 2) (L 3)
  | lower13 =>
      simpa [HullSixTwoFourWideChord.face,
        HullSixTwoFourWideChord.left, HullSixTwoFourWideChord.right,
        HullSixTwoFourWideChord.remainder0,
        HullSixTwoFourWideChord.remainder1] using
          hullSixTwoFour_lower_retriangulation_13 P (L 0) (L 1) (L 2) (L 3)
  | lower03 =>
      simpa [HullSixTwoFourWideChord.face,
        HullSixTwoFourWideChord.left, HullSixTwoFourWideChord.right,
        HullSixTwoFourWideChord.remainder0,
        HullSixTwoFourWideChord.remainder1] using
          hullSixTwoFour_lower_retriangulation_03 P (L 0) (L 1) (L 2) (L 3)

namespace HullSixCompactCrossChordResidual

/-- A nonadjacent wide local product contradicts a beating compact residual.

`hC` is the ordinary `P`-cross-cap floor, `hcapV` is the invariant far
`Q`-cap floor, and `hD` records positivity of the selected same-side lower
face.  The Ferrers wrapper supplies these together with the local product
pattern. -/
theorem twoFourWideAt_false_of_pattern
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 2,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset i))))
    (hlower : ∀ j : Fin 4,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))) < 0)
    (W : HullSixTwoFourWideChord)
    (hD : minTri cfg ≤ W.face (cfg P) (fun j ↦
      cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
    (hC : minTri cfg ≤ sig (cfg P)
      (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1)))
      (cfg (cycle (rotation + hullSixTwoFourLowerOffset 0))))
    (hcapV : minTri cfg ≤ sig (cfg Q)
      (cfg (cycle (rotation + hullSixTwoFourLowerOffset 3)))
      (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0))))
    (hpattern : HullSixLocalProductTwelvePattern
      (minTri cfg)
      (sig (cfg P)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0)))
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1))))
      (W.face (cfg P) (fun j ↦
        cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
      (sig (cfg P)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.left))))
      (sig (cfg P)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.right))))
      (sig (cfg P)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.left))))
      (sig (cfg P)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.right))))
      (sig (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.left))))
      (sig (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.right))))
      (sig (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.left))))
      (sig (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.right))))) :
    False := by
  let m := minTri cfg
  let U : Fin 2 → ℝ × ℝ := fun i ↦
    cfg (cycle (rotation + hullSixTwoFourUpperOffset i))
  let L : Fin 4 → ℝ × ℝ := fun j ↦
    cfg (cycle (rotation + hullSixTwoFourLowerOffset j))
  let A := sig (cfg P) (U 0) (U 1)
  let D := W.face (cfg P) L
  let C := sig (cfg P) (U 1) (L 0)
  let E0 := sig (cfg P) (L 0) (L 1)
  let E1 := sig (cfg P) (L 1) (L 2)
  let E2 := sig (cfg P) (L 2) (L 3)
  let S0 := W.remainder0 (cfg P) L
  let S1 := W.remainder1 (cfg P) L
  let capU := sig (cfg P) (L 3) (cfg Q)
  let capV := sig (cfg Q) (L 3) (U 0)
  let capQ := sig (cfg P) (cfg Q) (U 0)

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hA : m ≤ A := by
    simpa [m, A, U, hullSixTwoFourUpperOffset] using
      R.twoFour_P_boundary_floor V rotation 0
  have hDRaw : m ≤ D := by simpa [m, D, L] using hD
  have hCRaw : m ≤ C := by simpa [m, C, U, L] using hC

  have hE0 : m ≤ E0 := by
    simpa [m, E0, L, hullSixTwoFourLowerOffset] using
      R.twoFour_P_boundary_floor V rotation 2
  have hE2 : m ≤ E2 := by
    simpa [m, E2, L, hullSixTwoFourLowerOffset] using
      R.twoFour_P_boundary_floor V rotation 4
  have hEar0 : m ≤ sig (L 0) (L 1) (L 2) := by
    simpa [m, L, hullSixTwoFourLowerOffset, add_assoc] using
      R.twoFour_hullEar_floor rotation 2
  have hEar1 : m ≤ sig (L 1) (L 2) (L 3) := by
    simpa [m, L, hullSixTwoFourLowerOffset, add_assoc] using
      R.twoFour_hullEar_floor rotation 3
  have hLong : m ≤ sig (L 0) (L 2) (L 3) := by
    simpa [m, L] using hullSixTwoFour_shiftedLower023_floor R rotation
  have hS0 : m ≤ S0 := by
    cases W <;>
      simp [S0, HullSixTwoFourWideChord.remainder0] <;>
      assumption
  have hS1 : m ≤ S1 := by
    cases W <;>
      simp [S1, HullSixTwoFourWideChord.remainder1] <;>
      assumption

  have hUpperLevel : m ≤ sig (cfg P) (cfg Q) (U 0) := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourUpperOffset 0)
    rw [abs_of_pos (hupper 0)] at h
    simpa [m, U] using h
  have hLowerLevel : m ≤ -sig (cfg P) (cfg Q) (L 3) := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 3)
    rw [abs_of_neg (hlower 3)] at h
    simpa [m, L] using h
  have hcapUIdentity :
      capU = -sig (cfg P) (cfg Q) (L 3) := by
    dsimp [capU]
    simp only [sig]
    ring
  have hcapURaw : m ≤ capU := by
    rw [hcapUIdentity]
    exact hLowerLevel
  have hcapVRaw : m ≤ capV := by
    simpa [m, capV, U, L] using hcapV
  have hcapQRaw : m ≤ capQ := by
    simpa [m, capQ, U] using hUpperLevel

  have hFan : doubledHullArea cfg = A + C + E0 + E1 + E2 +
      sig (cfg P) (L 3) (U 0) := by
    simpa [A, C, E0, E1, E2, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using
        R.twoFour_P_fan_sum V rotation
  have hCapSplit :
      sig (cfg P) (L 3) (U 0) = capU + capV + capQ := by
    simpa [capU, capV, capQ] using
      hullSixTwoFour_crossCap_split (cfg P) (cfg Q) (U 0) (L 3)
  have hFan' : doubledHullArea cfg =
      A + C + E0 + E1 + E2 + capU + capV + capQ := by
    linarith
  have hLower : E0 + E1 + E2 = D + S0 + S1 := by
    simpa [E0, E1, E2, D, S0, S1, L] using
      hullSixTwoFourWideChord_retriangulation W (cfg P) L
  have hPattern' : HullSixLocalProductTwelvePattern m A D
      (sig (cfg P) (U 0) (L W.left))
      (sig (cfg P) (U 0) (L W.right))
      (sig (cfg P) (U 1) (L W.left))
      (sig (cfg P) (U 1) (L W.right))
      (sig (cfg Q) (U 0) (L W.left))
      (sig (cfg Q) (U 0) (L W.right))
      (sig (cfg Q) (U 1) (L W.left))
      (sig (cfg Q) (U 1) (L W.right)) := by
    simpa [m, A, D, U, L] using hpattern
  have hwide : 25 * m < 2 * doubledHullArea cfg :=
    hullSixTwoFour_finish_of_wideLocalProduct_and_lowerRetriangulation
      hm hA hDRaw hCRaw hS0 hS1 hcapURaw hcapVRaw hcapQRaw
      hFan' hLower hPattern'
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hwide, hcut]

/-- The `Q`-fan mirror of `twoFourWideAt_false_of_pattern`.

Here the selected wide lower face and the upper face both use base `Q`.
The cross cap `Q-U1-L0` is split at `P`; its three pieces are the upper
line-level face, the ordinary boundary cell `P-U1-L0`, and the lower
line-level face.  Thus this theorem consumes the `LR / LL` Plucker pattern
directly, without transporting the whole configuration by a complement
symmetry. -/
theorem twoFourWideQAt_false_of_pattern
    {cfg : Configuration} {cycle : Fin 6 → Fin 8} {p q P Q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q)
    (V : HullSixOrientedView cfg cycle P Q)
    (rotation : Fin 6)
    (hupper : ∀ i : Fin 2,
      0 < sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset i))))
    (hlower : ∀ j : Fin 4,
      sig (cfg P) (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))) < 0)
    (W : HullSixTwoFourWideChord)
    (hD : minTri cfg ≤ W.face (cfg Q) (fun j ↦
      cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
    (hwrap : minTri cfg ≤ sig (cfg Q)
      (cfg (cycle (rotation + hullSixTwoFourLowerOffset 3)))
      (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0))))
    (hcross : minTri cfg ≤ sig (cfg P)
      (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1)))
      (cfg (cycle (rotation + hullSixTwoFourLowerOffset 0))))
    (hpattern : HullSixLocalProductTwelvePattern
      (minTri cfg)
      (sig (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0)))
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1))))
      (W.face (cfg Q) (fun j ↦
        cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
      (sig (cfg P)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.left))))
      (sig (cfg P)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.right))))
      (sig (cfg P)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.left))))
      (sig (cfg P)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.right))))
      (sig (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.left))))
      (sig (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 0)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.right))))
      (sig (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.left))))
      (sig (cfg Q)
        (cfg (cycle (rotation + hullSixTwoFourUpperOffset 1)))
        (cfg (cycle (rotation + hullSixTwoFourLowerOffset W.right))))) :
    False := by
  let m := minTri cfg
  let U : Fin 2 → ℝ × ℝ := fun i ↦
    cfg (cycle (rotation + hullSixTwoFourUpperOffset i))
  let L : Fin 4 → ℝ × ℝ := fun j ↦
    cfg (cycle (rotation + hullSixTwoFourLowerOffset j))
  let A := sig (cfg Q) (U 0) (U 1)
  let D := W.face (cfg Q) L
  let E0 := sig (cfg Q) (L 0) (L 1)
  let E1 := sig (cfg Q) (L 1) (L 2)
  let E2 := sig (cfg Q) (L 2) (L 3)
  let S0 := W.remainder0 (cfg Q) L
  let S1 := W.remainder1 (cfg Q) L
  let wrap := sig (cfg Q) (L 3) (U 0)
  let capU := sig (cfg Q) (U 1) (cfg P)
  let capV := sig (cfg P) (U 1) (L 0)
  let capL := sig (cfg Q) (cfg P) (L 0)

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hA : m ≤ A := by
    simpa [m, A, U, hullSixTwoFourUpperOffset] using
      R.twoFour_Q_boundary_floor V rotation 0
  have hDRaw : m ≤ D := by simpa [m, D, L] using hD
  have hWrapRaw : m ≤ wrap := by
    simpa [m, wrap, U, L] using hwrap

  have hE0 : m ≤ E0 := by
    simpa [m, E0, L, hullSixTwoFourLowerOffset] using
      R.twoFour_Q_boundary_floor V rotation 2
  have hE2 : m ≤ E2 := by
    simpa [m, E2, L, hullSixTwoFourLowerOffset] using
      R.twoFour_Q_boundary_floor V rotation 4
  have hEar0 : m ≤ sig (L 0) (L 1) (L 2) := by
    simpa [m, L, hullSixTwoFourLowerOffset, add_assoc] using
      R.twoFour_hullEar_floor rotation 2
  have hEar1 : m ≤ sig (L 1) (L 2) (L 3) := by
    simpa [m, L, hullSixTwoFourLowerOffset, add_assoc] using
      R.twoFour_hullEar_floor rotation 3
  have hLong : m ≤ sig (L 0) (L 2) (L 3) := by
    simpa [m, L] using hullSixTwoFour_shiftedLower023_floor R rotation
  have hS0 : m ≤ S0 := by
    cases W <;>
      simp [S0, HullSixTwoFourWideChord.remainder0] <;>
      assumption
  have hS1 : m ≤ S1 := by
    cases W <;>
      simp [S1, HullSixTwoFourWideChord.remainder1] <;>
      assumption

  have hUpperLevel : m ≤ sig (cfg P) (cfg Q) (U 1) := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourUpperOffset 1)
    rw [abs_of_pos (hupper 1)] at h
    simpa [m, U] using h
  have hLowerLevel : m ≤ -sig (cfg P) (cfg Q) (L 0) := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset 0)
    rw [abs_of_neg (hlower 0)] at h
    simpa [m, L] using h
  have hcapUIdentity : capU = sig (cfg P) (cfg Q) (U 1) := by
    dsimp [capU]
    simp only [sig]
    ring
  have hcapURaw : m ≤ capU := by
    rw [hcapUIdentity]
    exact hUpperLevel
  have hcapVRaw : m ≤ capV := by
    simpa [m, capV, U, L] using hcross
  have hcapLIdentity : capL = -sig (cfg P) (cfg Q) (L 0) := by
    dsimp [capL]
    simp only [sig]
    ring
  have hcapLRaw : m ≤ capL := by
    rw [hcapLIdentity]
    exact hLowerLevel

  have hFan : doubledHullArea cfg = A +
      sig (cfg Q) (U 1) (L 0) + E0 + E1 + E2 + wrap := by
    simpa [A, E0, E1, E2, wrap, U, L,
      hullSixTwoFourUpperOffset, hullSixTwoFourLowerOffset] using
        R.twoFour_Q_fan_sum V rotation
  have hCapSplit :
      sig (cfg Q) (U 1) (L 0) = capU + capV + capL := by
    simpa [capU, capV, capL] using
      hullSixTwoFour_crossCap_split (cfg Q) (cfg P) (L 0) (U 1)
  have hFan' : doubledHullArea cfg =
      A + wrap + E0 + E1 + E2 + capU + capV + capL := by
    linarith
  have hLower : E0 + E1 + E2 = D + S0 + S1 := by
    simpa [E0, E1, E2, D, S0, S1, L] using
      hullSixTwoFourWideChord_retriangulation W (cfg Q) L
  have hPattern' : HullSixLocalProductTwelvePattern m A D
      (sig (cfg P) (U 0) (L W.left))
      (sig (cfg P) (U 0) (L W.right))
      (sig (cfg P) (U 1) (L W.left))
      (sig (cfg P) (U 1) (L W.right))
      (sig (cfg Q) (U 0) (L W.left))
      (sig (cfg Q) (U 0) (L W.right))
      (sig (cfg Q) (U 1) (L W.left))
      (sig (cfg Q) (U 1) (L W.right)) := by
    simpa [m, A, D, U, L] using hpattern
  have hwide : 25 * m < 2 * doubledHullArea cfg :=
    hullSixTwoFour_finish_of_wideLocalProduct_and_lowerRetriangulation
      hm hA hDRaw hWrapRaw hS0 hS1 hcapURaw hcapVRaw hcapLRaw
      hFan' hLower hPattern'
  have hcut : (2 / 25 : ℝ) * doubledHullArea cfg < m := by
    change (2 / 25 : ℝ) * doubledHullArea cfg < minTri cfg
    exact R.cut_margin
  nlinarith only [hwide, hcut]

end HullSixCompactCrossChordResidual

end Heilbronn8
