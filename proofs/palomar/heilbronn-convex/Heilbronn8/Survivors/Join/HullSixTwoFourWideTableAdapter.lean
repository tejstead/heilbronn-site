import Heilbronn8.Survivors.Join.HullSixTwoFourWideGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindCases

/-!
# Ferrers recognition for both nonadjacent wide families

This is the table-facing half of the wide geometry adapter.  It turns a
selected `RR / LR` lower chord into the strengthened local product pattern,
derives positivity of the selected lower face from that product, and invokes
the geometric retriangulation theorem.

The complementary `LR / LL` family is closed directly in the `Q` fan.  This
keeps the geometry adapter independent of a global complement-transport
theorem.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Heilbronn8

namespace HullSixTwoFourCuts

/-- Every genuinely new wide table has an orientation with a nonadjacent
`RR / LR` witness.  Adjacent witnesses and the designated hard table were
already part of `CurrentlyCovered`; the eight new labels are exactly the
cases consumed by the geometric theorem below. -/
theorem newlyWide_orients_to_nonadjacent_RRLR :
    ∀ T : HullSixTwoFourCuts,
      T.Legal → T.HasWideProductTwelve → ¬T.CurrentlyCovered →
        ∃ g : Symmetry, ∃ W : HullSixTwoFourWideChord,
          (act g T).table 0 W.left = HullSixChamberLabel.R ∧
          (act g T).table 0 W.right = HullSixChamberLabel.R ∧
          (act g T).table 1 W.left = HullSixChamberLabel.L ∧
          (act g T).table 1 W.right = HullSixChamberLabel.R := by
  letI : DecidablePred fun T : HullSixTwoFourCuts =>
      T.Legal → T.HasWideProductTwelve → ¬T.CurrentlyCovered →
        ∃ g : Symmetry, ∃ W : HullSixTwoFourWideChord,
          (act g T).table 0 W.left = HullSixChamberLabel.R ∧
          (act g T).table 0 W.right = HullSixChamberLabel.R ∧
          (act g T).table 1 W.left = HullSixChamberLabel.L ∧
          (act g T).table 1 W.right = HullSixChamberLabel.R := fun T => by
    letI : DecidablePred fun g : Symmetry =>
        ∃ W : HullSixTwoFourWideChord,
          (act g T).table 0 W.left = HullSixChamberLabel.R ∧
          (act g T).table 0 W.right = HullSixChamberLabel.R ∧
          (act g T).table 1 W.left = HullSixChamberLabel.L ∧
          (act g T).table 1 W.right = HullSixChamberLabel.R := fun g => by
      letI : DecidablePred fun W : HullSixTwoFourWideChord =>
          (act g T).table 0 W.left = HullSixChamberLabel.R ∧
          (act g T).table 0 W.right = HullSixChamberLabel.R ∧
          (act g T).table 1 W.left = HullSixChamberLabel.L ∧
          (act g T).table 1 W.right = HullSixChamberLabel.R :=
        fun _ => inferInstance
      exact inferInstance
    letI : Decidable T.Legal := inferInstance
    letI : Decidable T.HasWideProductTwelve := inferInstance
    letI : Decidable T.CurrentlyCovered := inferInstance
    exact inferInstance
  decide

/-- Without changing orientation, every genuinely new wide table contains
either a nonadjacent `RR / LR` witness or a nonadjacent `LR / LL` witness. -/
theorem newlyWide_has_nonadjacent_pattern :
    ∀ T : HullSixTwoFourCuts,
      T.Legal → T.HasWideProductTwelve → ¬T.CurrentlyCovered →
        ∃ W : HullSixTwoFourWideChord,
          ((T.table 0 W.left = HullSixChamberLabel.R ∧
              T.table 0 W.right = HullSixChamberLabel.R ∧
              T.table 1 W.left = HullSixChamberLabel.L ∧
              T.table 1 W.right = HullSixChamberLabel.R) ∨
            (T.table 0 W.left = HullSixChamberLabel.L ∧
              T.table 0 W.right = HullSixChamberLabel.R ∧
              T.table 1 W.left = HullSixChamberLabel.L ∧
              T.table 1 W.right = HullSixChamberLabel.L)) := by
  letI : DecidablePred fun T : HullSixTwoFourCuts =>
      T.Legal → T.HasWideProductTwelve → ¬T.CurrentlyCovered →
        ∃ W : HullSixTwoFourWideChord,
          ((T.table 0 W.left = HullSixChamberLabel.R ∧
              T.table 0 W.right = HullSixChamberLabel.R ∧
              T.table 1 W.left = HullSixChamberLabel.L ∧
              T.table 1 W.right = HullSixChamberLabel.R) ∨
            (T.table 0 W.left = HullSixChamberLabel.L ∧
              T.table 0 W.right = HullSixChamberLabel.R ∧
              T.table 1 W.left = HullSixChamberLabel.L ∧
              T.table 1 W.right = HullSixChamberLabel.L)) := fun T => by
    letI : DecidablePred fun W : HullSixTwoFourWideChord =>
        ((T.table 0 W.left = HullSixChamberLabel.R ∧
            T.table 0 W.right = HullSixChamberLabel.R ∧
            T.table 1 W.left = HullSixChamberLabel.L ∧
            T.table 1 W.right = HullSixChamberLabel.R) ∨
          (T.table 0 W.left = HullSixChamberLabel.L ∧
            T.table 0 W.right = HullSixChamberLabel.R ∧
            T.table 1 W.left = HullSixChamberLabel.L ∧
            T.table 1 W.right = HullSixChamberLabel.L)) :=
      fun _ => inferInstance
    letI : Decidable T.Legal := inferInstance
    letI : Decidable T.HasWideProductTwelve := inferInstance
    letI : Decidable T.CurrentlyCovered := inferInstance
    exact inferInstance
  decide

end HullSixTwoFourCuts

namespace HullSixCompactCrossChordResidual

/-- A selected nonadjacent `RR / LR` block is impossible in a beating
oriented `2 + 4` residual. -/
theorem twoFourWideRRLRAt_false
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
    (T : HullSixTwoFourCuts) (hLegal : T.Legal)
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j)))))
    (W : HullSixTwoFourWideChord)
    (h00 : T.table 0 W.left = HullSixChamberLabel.R)
    (h01 : T.table 0 W.right = HullSixChamberLabel.R)
    (h10 : T.table 1 W.left = HullSixChamberLabel.L)
    (h11 : T.table 1 W.right = HullSixChamberLabel.R) :
    False := by
  let m := minTri cfg
  let U : Fin 2 → ℝ × ℝ := fun i ↦
    cfg (cycle (rotation + hullSixTwoFourUpperOffset i))
  let L : Fin 4 → ℝ × ℝ := fun j ↦
    cfg (cycle (rotation + hullSixTwoFourLowerOffset j))
  let u : Fin 2 → ℝ := fun i ↦ sig (cfg P) (cfg Q) (U i)
  let v : Fin 4 → ℝ := fun j ↦ -sig (cfg P) (cfg Q) (L j)
  let x : Fin 2 → Fin 4 → ℝ := fun i j ↦ sig (cfg P) (U i) (L j)
  let y : Fin 2 → Fin 4 → ℝ := fun i j ↦ sig (cfg Q) (U i) (L j)
  let A := sig (cfg P) (U 0) (U 1)
  let D := W.face (cfg P) L

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hu (i : Fin 2) : m ≤ u i := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourUpperOffset i)
    rw [abs_of_pos (hupper i)] at h
    simpa [m, u, U] using h
  have hv (j : Fin 4) : m ≤ v j := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset j)
    rw [abs_of_neg (hlower j)] at h
    simpa [m, v, L] using h
  have hbase (i : Fin 2) (j : Fin 4) :
      y i j = x i j + u i + v j := by
    have h := sig_crossChord_base_change (cfg P) (cfg Q) (U i) (L j)
    dsimp [x, y, u, v]
    linarith only [h]

  have hplucker :
      A * D = x 0 W.left * x 1 W.right -
        x 0 W.right * x 1 W.left := by
    have h := sig_crossChord_plucker
      (cfg P) (U 0) (U 1) (L W.left) (L W.right)
    simpa [A, D, x, HullSixTwoFourWideChord.face] using h.symm

  have hPattern : HullSixLocalProductTwelvePattern m A D
      (x 0 W.left) (x 0 W.right) (x 1 W.left) (x 1 W.right)
      (y 0 W.left) (y 0 W.right) (y 1 W.left) (y 1 W.right) := by
    apply hullSixLocalProductTwelvePattern_of_RR_LR
      (hu 0) (hu 1) (hv W.left) (hv W.right)
      (hbase 0 W.left) (hbase 0 W.right)
      (hbase 1 W.left) (hbase 1 W.right)
    · simpa [h00] using hTable 0 W.left
    · simpa [h01] using hTable 0 W.right
    · simpa [h10] using hTable 1 W.left
    · simpa [h11] using hTable 1 W.right
    · exact hplucker

  have hA : m ≤ A := by
    simpa [m, A, U, hullSixTwoFourUpperOffset] using
      R.twoFour_P_boundary_floor V rotation 0
  have hproduct : 12 * m ^ 2 ≤ A * D :=
    hullSixLocalProductTwelvePattern_product (le_of_lt hm) hPattern
  have hproductPos : 0 < A * D := by
    have hmSq : 0 < m ^ 2 := sq_pos_of_pos hm
    nlinarith
  have hDPos : 0 < D :=
    pos_of_mul_pos_right hproductPos (by linarith)
  have hLeftRight :
      rotation + hullSixTwoFourLowerOffset W.left ≠
        rotation + hullSixTwoFourLowerOffset W.right := by
    cases W <;> fin_cases rotation <;> decide
  have hPLeft :
      P ≠ cycle (rotation + hullSixTwoFourLowerOffset W.left) := by
    intro h
    exact V.P_outside ⟨_, h.symm⟩
  have hPRight :
      P ≠ cycle (rotation + hullSixTwoFourLowerOffset W.right) := by
    intro h
    exact V.P_outside ⟨_, h.symm⟩
  have hDFloorAbs : m ≤ |D| := by
    have h := minTri_le_abs_sig_of_pairwise_ne cfg hPLeft hPRight
      (R.cycle_injective.ne hLeftRight)
    simpa [m, D, L, HullSixTwoFourWideChord.face] using h
  have hDFloor : m ≤ D := by
    rwa [abs_of_pos hDPos] at hDFloorAbs

  obtain ⟨hBoundaryC, hBoundaryCap⟩ :=
    HullSixTwoFourCuts.boundary_cells T hLegal
  have hCFloor : m ≤ x 1 0 := by
    simpa [m, x, U, L, hBoundaryC,
      HullSixChamberLabel.Holds] using hTable 1 0
  have hFarQ : y 0 3 ≤ -m := by
    simpa [m, y, U, L, hBoundaryCap,
      HullSixChamberLabel.Holds] using hTable 0 3
  have hcapVIdentity : sig (cfg Q) (L 3) (U 0) = -y 0 3 := by
    dsimp [y]
    simp only [sig]
    ring
  have hcapV : m ≤ sig (cfg Q) (L 3) (U 0) := by
    rw [hcapVIdentity]
    linarith

  apply R.twoFourWideAt_false_of_pattern V rotation hupper hlower W
  · simpa [m, D, L] using hDFloor
  · simpa [m, x, U, L] using hCFloor
  · simpa [m, U, L] using hcapV
  · simpa [m, A, D, U, L, x, y] using hPattern

/-- A selected nonadjacent `LR / LL` block is impossible in a beating
oriented `2 + 4` residual.  This is the direct `Q`-fan mirror of
`twoFourWideRRLRAt_false`. -/
theorem twoFourWideLRLLAt_false
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
    (T : HullSixTwoFourCuts) (hLegal : T.Legal)
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j)))))
    (W : HullSixTwoFourWideChord)
    (h00 : T.table 0 W.left = HullSixChamberLabel.L)
    (h01 : T.table 0 W.right = HullSixChamberLabel.R)
    (h10 : T.table 1 W.left = HullSixChamberLabel.L)
    (h11 : T.table 1 W.right = HullSixChamberLabel.L) :
    False := by
  let m := minTri cfg
  let U : Fin 2 → ℝ × ℝ := fun i ↦
    cfg (cycle (rotation + hullSixTwoFourUpperOffset i))
  let L : Fin 4 → ℝ × ℝ := fun j ↦
    cfg (cycle (rotation + hullSixTwoFourLowerOffset j))
  let u : Fin 2 → ℝ := fun i ↦ sig (cfg P) (cfg Q) (U i)
  let v : Fin 4 → ℝ := fun j ↦ -sig (cfg P) (cfg Q) (L j)
  let x : Fin 2 → Fin 4 → ℝ := fun i j ↦ sig (cfg P) (U i) (L j)
  let y : Fin 2 → Fin 4 → ℝ := fun i j ↦ sig (cfg Q) (U i) (L j)
  let A := sig (cfg Q) (U 0) (U 1)
  let D := W.face (cfg Q) L

  have hm : 0 < m := by simpa [m] using R.minTri_pos
  have hu (i : Fin 2) : m ≤ u i := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourUpperOffset i)
    rw [abs_of_pos (hupper i)] at h
    simpa [m, u, U] using h
  have hv (j : Fin 4) : m ≤ v j := by
    have h := V.lineLevel_floor
      (rotation + hullSixTwoFourLowerOffset j)
    rw [abs_of_neg (hlower j)] at h
    simpa [m, v, L] using h
  have hbase (i : Fin 2) (j : Fin 4) :
      y i j = x i j + u i + v j := by
    have h := sig_crossChord_base_change (cfg P) (cfg Q) (U i) (L j)
    dsimp [x, y, u, v]
    linarith only [h]

  have hplucker :
      A * D = y 0 W.left * y 1 W.right -
        y 0 W.right * y 1 W.left := by
    have h := sig_crossChord_plucker
      (cfg Q) (U 0) (U 1) (L W.left) (L W.right)
    simpa [A, D, y, HullSixTwoFourWideChord.face] using h.symm

  have hPattern : HullSixLocalProductTwelvePattern m A D
      (x 0 W.left) (x 0 W.right) (x 1 W.left) (x 1 W.right)
      (y 0 W.left) (y 0 W.right) (y 1 W.left) (y 1 W.right) := by
    apply hullSixLocalProductTwelvePattern_of_LR_LL
      (hu 0) (hu 1) (hv W.left) (hv W.right)
      (hbase 0 W.left) (hbase 0 W.right)
      (hbase 1 W.left) (hbase 1 W.right)
    · simpa [h00] using hTable 0 W.left
    · simpa [h01] using hTable 0 W.right
    · simpa [h10] using hTable 1 W.left
    · simpa [h11] using hTable 1 W.right
    · exact hplucker

  have hA : m ≤ A := by
    simpa [m, A, U, hullSixTwoFourUpperOffset] using
      R.twoFour_Q_boundary_floor V rotation 0
  have hproduct : 12 * m ^ 2 ≤ A * D :=
    hullSixLocalProductTwelvePattern_product (le_of_lt hm) hPattern
  have hproductPos : 0 < A * D := by
    have hmSq : 0 < m ^ 2 := sq_pos_of_pos hm
    nlinarith
  have hDPos : 0 < D :=
    pos_of_mul_pos_right hproductPos (by linarith)
  have hLeftRight :
      rotation + hullSixTwoFourLowerOffset W.left ≠
        rotation + hullSixTwoFourLowerOffset W.right := by
    cases W <;> fin_cases rotation <;> decide
  have hQLeft :
      Q ≠ cycle (rotation + hullSixTwoFourLowerOffset W.left) := by
    intro h
    exact V.Q_outside ⟨_, h.symm⟩
  have hQRight :
      Q ≠ cycle (rotation + hullSixTwoFourLowerOffset W.right) := by
    intro h
    exact V.Q_outside ⟨_, h.symm⟩
  have hDFloorAbs : m ≤ |D| := by
    have h := minTri_le_abs_sig_of_pairwise_ne cfg hQLeft hQRight
      (R.cycle_injective.ne hLeftRight)
    simpa [m, D, L, HullSixTwoFourWideChord.face] using h
  have hDFloor : m ≤ D := by
    rwa [abs_of_pos hDPos] at hDFloorAbs

  obtain ⟨hBoundaryCross, hBoundaryWrap⟩ :=
    HullSixTwoFourCuts.boundary_cells T hLegal
  have hCross : m ≤ x 1 0 := by
    simpa [m, x, U, L, hBoundaryCross,
      HullSixChamberLabel.Holds] using hTable 1 0
  have hFarQ : y 0 3 ≤ -m := by
    simpa [m, y, U, L, hBoundaryWrap,
      HullSixChamberLabel.Holds] using hTable 0 3
  have hWrapIdentity : sig (cfg Q) (L 3) (U 0) = -y 0 3 := by
    dsimp [y]
    simp only [sig]
    ring
  have hWrap : m ≤ sig (cfg Q) (L 3) (U 0) := by
    rw [hWrapIdentity]
    linarith

  apply R.twoFourWideQAt_false_of_pattern V rotation hupper hlower W
  · simpa [m, D, L] using hDFloor
  · simpa [m, U, L] using hWrap
  · simpa [m, x, U, L] using hCross
  · simpa [m, A, D, U, L, x, y] using hPattern

/-- Direct wide dispatch for the eight tables newly covered by a
nonadjacent product.  No configuration symmetry is needed: the two chamber
alternatives are consumed in their native `P` and `Q` fans. -/
theorem twoFourNewlyWideAt_false
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
    (T : HullSixTwoFourCuts) (hLegal : T.Legal)
    (hWide : T.HasWideProductTwelve) (hNew : ¬T.CurrentlyCovered)
    (hTable : ∀ i j,
      HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
        (sig (cfg P)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))
        (sig (cfg Q)
          (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
          (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))))) :
    False := by
  obtain ⟨W, hRRLR | hLRLL⟩ :=
    HullSixTwoFourCuts.newlyWide_has_nonadjacent_pattern
      T hLegal hWide hNew
  · rcases hRRLR with ⟨h00, h01, h10, h11⟩
    exact R.twoFourWideRRLRAt_false V rotation hupper hlower T hLegal
      hTable W h00 h01 h10 h11
  · rcases hLRLL with ⟨h00, h01, h10, h11⟩
    exact R.twoFourWideLRLLAt_false V rotation hupper hlower T hLegal
      hTable W h00 h01 h10 h11

end HullSixCompactCrossChordResidual
end Heilbronn8
