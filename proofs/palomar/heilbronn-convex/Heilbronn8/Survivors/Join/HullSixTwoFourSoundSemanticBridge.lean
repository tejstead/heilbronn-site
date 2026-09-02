import Heilbronn8.Survivors.Join.HullSixFerrersNormalization
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindAdjacentGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourQBlindEndOpenGeometry
import Heilbronn8.Survivors.Join.HullSixTwoFourWideTableAdapter

/-!
# Sound semantic bridge for hull-six `2 + 4` packets

This module replaces the circular symmetry-and-weakening provider by three
separate notions with direct geometric meanings.

* An exact packet is closed only in the frame in which its complete table is
  realized.
* A q-weakening is used only for `HullSixQBlindFrontierHolds`, whose retained
  `X` inequalities are genuinely monotone when the second cuts increase.
* A finite table symmetry may be used only when a new geometric frame and an
  exact table-transport theorem are supplied explicitly.

No same-shape geometric custody for the `2 x 4` complement-rotation is
asserted here.  Swapping the exterior points naturally exchanges the `2 + 4`
and `4 + 2` blocks, so such custody is a real premise rather than a finite
table identity.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-! ## Geometry custody -/

/-- The complete geometric data of one normalized, fixed-orientation
`2 + 4` frame, before selecting its exact Ferrers table. -/
structure HullSixTwoFourGeometricFrame
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q) where
  P : Fin 8
  Q : Fin 8
  pair : HullSixIsOrientedPair p q P Q
  view : HullSixOrientedView cfg cycle P Q
  rotation : Fin 6
  upper_pos : ∀ i : Fin 2,
    0 < sig (cfg P) (cfg Q)
      (cfg (cycle (rotation + hullSixTwoFourUpperOffset i)))
  lower_neg : ∀ j : Fin 4,
    sig (cfg P) (cfg Q)
      (cfg (cycle (rotation + hullSixTwoFourLowerOffset j))) < 0

namespace HullSixTwoFourGeometricFrame

/-- The `P`-based cross-chord determinant in a fixed frame. -/
def X
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R) (i : Fin 2) (j : Fin 4) : ℝ :=
  sig (cfg F.P)
    (cfg (cycle (F.rotation + hullSixTwoFourUpperOffset i)))
    (cfg (cycle (F.rotation + hullSixTwoFourLowerOffset j)))

/-- Exact chamber realization of a cut record in this particular frame. -/
def TableHolds
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R)
    (T : HullSixTwoFourCuts) : Prop :=
  ∀ i j,
    HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
      (sig (cfg F.P)
        (cfg (cycle (F.rotation + hullSixTwoFourUpperOffset i)))
        (cfg (cycle (F.rotation + hullSixTwoFourLowerOffset j))))
      (sig (cfg F.Q)
        (cfg (cycle (F.rotation + hullSixTwoFourUpperOffset i)))
        (cfg (cycle (F.rotation + hullSixTwoFourLowerOffset j))))

/-- The q-blind partial information attached to a cut record.  Unlike exact
table realization, this predicate is monotone when only the second cuts are
increased. -/
def XFrontierHolds
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R)
    (T : HullSixTwoFourCuts) : Prop :=
  HullSixQBlindFrontierHolds T.p T.q (minTri cfg) F.X

/-- A scalar theorem that contradicts only the retained q-blind `X`
frontier, not a hypothetical exact chamber table. -/
def XFrontierClosed
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R)
    (T : HullSixTwoFourCuts) : Prop :=
  F.XFrontierHolds T -> False

/-- A geometry-sound implementation of a finite table symmetry.  The target
frame is explicit, and exact realization is transported rather than assumed.
No nonidentity instance is supplied in this module. -/
structure SymmetryCustody
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F F' : HullSixTwoFourGeometricFrame R)
    (g : HullSixTwoFourCuts.Symmetry) : Prop where
  tableHolds : ∀ T, T.Legal -> F.TableHolds T ->
    F'.TableHolds (HullSixTwoFourCuts.act g T)

/-- Identity symmetry has identity geometric custody. -/
theorem identityCustody
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R) :
    SymmetryCustody F F .identity := by
  refine ⟨?_⟩
  intro T hLegal hTable
  simpa [HullSixTwoFourCuts.act] using hTable

/-- The exact additional premise that would justify using the finite
complement-rotation as a geometry symmetry.  It is intentionally not proved:
the evident point swap produces a `4 + 2` frame, not another frame of this
same `2 + 4` type. -/
def RotateComplementCustody : Prop :=
  ∀ {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R),
    ∃ F' : HullSixTwoFourGeometricFrame R,
      SymmetryCustody F F' .rotateComplement

/-! ## The genuinely monotone weakening seam -/

/-- Increasing a q-frontier preserves the retained partial `X` data. -/
theorem xFrontierHolds_mono
    {r s : ℕ} {p p' q q' : Fin r -> ℕ}
    {m : ℝ} {X : Fin r -> Fin s -> ℝ}
    (hp : ∀ i, p i = p' i) (hq : ∀ i, q i ≤ q' i)
    (h : HullSixQBlindFrontierHolds p q m X) :
    HullSixQBlindFrontierHolds p' q' m X := by
  rcases h with ⟨hleft, hnegative, hstrong⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj
    apply hleft i j
    simpa [hp i] using hj
  · intro i j hj
    apply hnegative i j
    simpa [hp i] using hj
  · intro i j hj
    exact hstrong i j (le_trans (hq i) hj)

/-- Exact realization of `T`, followed by a genuine q-weakening `T <= U`,
supplies the partial `X` frontier of `U`. -/
theorem xFrontierHolds_of_table_weak
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R)
    {T U : HullSixTwoFourCuts} (hLegal : T.Legal)
    (hWeak : HullSixTwoFourCuts.Weak T U)
    (hTable : F.TableHolds T) : F.XFrontierHolds U := by
  let upper : Fin 2 -> ℝ × ℝ := fun i =>
    cfg (cycle (F.rotation + hullSixTwoFourUpperOffset i))
  let lower : Fin 4 -> ℝ × ℝ := fun j =>
    cfg (cycle (F.rotation + hullSixTwoFourLowerOffset j))
  let u : Fin 2 -> ℝ := fun i => sig (cfg F.P) (cfg F.Q) (upper i)
  let v : Fin 4 -> ℝ := fun j => -sig (cfg F.P) (cfg F.Q) (lower j)
  let Y : Fin 2 -> Fin 4 -> ℝ := fun i j =>
    sig (cfg F.Q) (upper i) (lower j)

  have hpq : ∀ i, T.p i ≤ T.q i := by
    intro i
    fin_cases i
    · simpa [HullSixTwoFourCuts.p, HullSixTwoFourCuts.q] using hLegal.1
    · simpa [HullSixTwoFourCuts.p, HullSixTwoFourCuts.q] using hLegal.2.1
  have hp : ∀ i, T.p i = U.p i := by
    intro i
    fin_cases i
    · simpa [HullSixTwoFourCuts.p, hWeak.1]
    · simpa [HullSixTwoFourCuts.p, hWeak.2.1]
  have hq : ∀ i, T.q i ≤ U.q i := by
    intro i
    fin_cases i
    · simpa [HullSixTwoFourCuts.q] using hWeak.2.2.1
    · simpa [HullSixTwoFourCuts.q] using hWeak.2.2.2
  have hu : ∀ i, minTri cfg ≤ u i := by
    intro i
    have h := F.view.lineLevel_floor
      (F.rotation + hullSixTwoFourUpperOffset i)
    rw [abs_of_pos (F.upper_pos i)] at h
    simpa [u, upper] using h
  have hv : ∀ j, minTri cfg ≤ v j := by
    intro j
    have h := F.view.lineLevel_floor
      (F.rotation + hullSixTwoFourLowerOffset j)
    rw [abs_of_neg (F.lower_neg j)] at h
    simpa [v, lower] using h
  have hbase : ∀ i j, Y i j = F.X i j + u i + v j := by
    intro i j
    have h := sig_crossChord_base_change
      (cfg F.P) (cfg F.Q) (upper i) (lower j)
    dsimp [Y, X, u, v, upper, lower]
    linarith only [h]
  have hholds : ∀ i j,
      HullSixChamberLabel.Holds
        (hullSixFerrersLabel T.p T.q i j) (minTri cfg)
        (F.X i j) (Y i j) := by
    simpa [TableHolds, HullSixTwoFourCuts.table, X, Y, upper, lower] using
      hTable
  have hfront : HullSixQBlindFrontierHolds
      T.p U.q (minTri cfg) F.X :=
    qBlindFrontierHolds_of_ferrers
      (le_of_lt R.minTri_pos) hpq hq hu hv hbase hholds
  exact xFrontierHolds_mono hp (fun _ => le_rfl) hfront

/-- `XFrontierClosed` is contravariant under q-weakening for the correct
reason: the retained partial frontier itself is monotone. -/
theorem xFrontierClosed_of_weak
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R)
    {T U : HullSixTwoFourCuts}
    (hWeak : HullSixTwoFourCuts.Weak T U)
    (hClosed : F.XFrontierClosed U) : F.XFrontierClosed T := by
  intro hT
  apply hClosed
  apply xFrontierHolds_mono
    (p := T.p) (p' := U.p) (q := T.q) (q' := U.q)
  · intro i
    fin_cases i
    · simpa [HullSixTwoFourCuts.p, hWeak.1]
    · simpa [HullSixTwoFourCuts.p, hWeak.2.1]
  · intro i
    fin_cases i
    · simpa [HullSixTwoFourCuts.q] using hWeak.2.2.1
    · simpa [HullSixTwoFourCuts.q] using hWeak.2.2.2
  · exact hT

/-! ## Exact packet and fixed-frontier contracts -/

/-- Exact-table callback for one finite packet family in one fixed frame. -/
def ExactPacketClosed
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R)
    (Packet : HullSixTwoFourCuts -> Prop) : Prop :=
  ∀ T, T.Legal -> Packet T -> F.TableHolds T -> False

/-- A packet closed after an explicitly custodied symmetry remains closed in
the source frame. -/
theorem false_of_custodied_exactPacket
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    {F F' : HullSixTwoFourGeometricFrame R}
    {g : HullSixTwoFourCuts.Symmetry}
    (C : SymmetryCustody F F' g)
    {Packet : HullSixTwoFourCuts -> Prop}
    (hClosed : F'.ExactPacketClosed Packet)
    {T : HullSixTwoFourCuts} (hLegal : T.Legal)
    (hPacket : Packet (HullSixTwoFourCuts.act g T))
    (hTable : F.TableHolds T) : False := by
  apply hClosed (HullSixTwoFourCuts.act g T)
  · exact HullSixTwoFourCuts.legal_act g T hLegal
  · exact hPacket
  · exact C.tableHolds T hLegal hTable

/-- The two q-blind `p = (0,1)` packet families whose exact scalar adapters
are currently total. -/
def IsClosedP01Packet (T : HullSixTwoFourCuts) : Prop :=
  T.IsAdjacentStaggerPacket ∨ T.IsEndOpenTransitionPacket

/-- The exact wide family for which the current wide dispatcher is total. -/
def IsNewlyWidePacket (T : HullSixTwoFourCuts) : Prop :=
  T.HasWideProductTwelve ∧ ¬T.CurrentlyCovered

/-- All exact native-orientation packets currently closed by total adapters. -/
def IsClosedNativePacket (T : HullSixTwoFourCuts) : Prop :=
  IsClosedP01Packet T ∨ IsNewlyWidePacket T

/-- Existing exact adjacent and end-open umbrellas close the corresponding
native `p = (0,1)` packet family, with no weakening or table symmetry. -/
theorem closedP01Packet_exact
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R) :
    F.ExactPacketClosed IsClosedP01Packet := by
  intro T hLegal hPacket hTable
  rcases hPacket with hAdjacent | hEndOpen
  · exact R.twoFourQBlindAdjacentAt_false F.view F.rotation
      F.upper_pos F.lower_neg T hAdjacent hTable
  · exact R.twoFourQBlindEndOpenAt_false F.view F.rotation
      F.upper_pos F.lower_neg T hEndOpen hTable

/-- The total part of the existing wide dispatcher is also an exact native
packet callback. -/
theorem newlyWidePacket_exact
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R) :
    F.ExactPacketClosed IsNewlyWidePacket := by
  intro T hLegal hPacket hTable
  exact R.twoFourNewlyWideAt_false F.view F.rotation
    F.upper_pos F.lower_neg T hLegal hPacket.1 hPacket.2 hTable

/-- Current exact packet callbacks assembled without weakening or symmetry. -/
theorem closedNativePacket_exact
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R) :
    F.ExactPacketClosed IsClosedNativePacket := by
  intro T hLegal hPacket hTable
  rcases hPacket with hP01 | hWide
  · exact F.closedP01Packet_exact T hLegal hP01 hTable
  · exact F.newlyWidePacket_exact T hLegal hWide hTable

end HullSixTwoFourGeometricFrame

/-! ## Sound fixed-orientation endpoint -/

/-- A scalar provider for an exact packet family in every normalized frame. -/
def HullSixTwoFourExactPacketProvider
    (Packet : HullSixTwoFourCuts -> Prop) : Prop :=
  ∀ {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R),
    F.ExactPacketClosed Packet

/-- The existing adjacent and end-open exact umbrellas, assembled as a
global fixed-frame packet provider. -/
theorem hullSixTwoFourClosedP01PacketProvider :
    HullSixTwoFourExactPacketProvider
      HullSixTwoFourGeometricFrame.IsClosedP01Packet := by
  intro cfg cycle p q R F
  exact F.closedP01Packet_exact

/-- All currently total native exact callbacks as one global provider. -/
theorem hullSixTwoFourClosedNativePacketProvider :
    HullSixTwoFourExactPacketProvider
      HullSixTwoFourGeometricFrame.IsClosedNativePacket := by
  intro cfg cycle p q R F
  exact F.closedNativePacket_exact

/-- A scalar provider for genuinely partial q-blind frontiers. -/
def HullSixTwoFourXFrontierProvider
    (Top : HullSixTwoFourCuts -> Prop) : Prop :=
  ∀ {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixTwoFourGeometricFrame R) (U : HullSixTwoFourCuts),
    U.Legal -> Top U -> F.XFrontierClosed U

/-- Pure finite cover used by the sound bridge.  It never alternates an
abstract table symmetry with weakening: an exact table is either consumed in
place, or weakens within its fixed orientation to a partial frontier. -/
def HullSixTwoFourFixedOrientationCover
    (Packet Top : HullSixTwoFourCuts -> Prop) : Prop :=
  ∀ T : HullSixTwoFourCuts, T.Legal ->
    Packet T ∨
      ∃ U : HullSixTwoFourCuts,
        HullSixTwoFourCuts.Weak T U ∧ U.Legal ∧ Top U

/-- A maximal second-cut frontier.  There are thirteen such legal records,
one for each possible first-cut pair; no table symmetry is used. -/
def HullSixTwoFourIsMaximalQFrontier (T : HullSixTwoFourCuts) : Prop :=
  T.q0 = 3 ∧ T.q1 = 4

/-- Every legal table outside the already closed exact p01 packets weakens,
in its original geometric orientation, to the maximal frontier with the same
first cuts. -/
theorem hullSixTwoFour_closedP01_or_maximalQ_cover :
    HullSixTwoFourFixedOrientationCover
      HullSixTwoFourGeometricFrame.IsClosedP01Packet
      HullSixTwoFourIsMaximalQFrontier := by
  intro T hLegal
  by_cases hPacket :
      HullSixTwoFourGeometricFrame.IsClosedP01Packet T
  · exact Or.inl hPacket
  · right
    let U : HullSixTwoFourCuts :=
      ⟨T.p0, T.p1, 3, 4⟩
    refine ⟨U, ?_, ?_, ?_⟩
    · rcases hLegal with ⟨hp0q0, hp1q1, hp, hq, hbound⟩
      rcases hbound with ⟨hp1, hq0⟩
      dsimp [HullSixTwoFourCuts.Weak, U]
      constructor
      · rfl
      constructor
      · rfl
      constructor <;> omega
    · rcases hLegal with ⟨hp0q0, hp1q1, hp, hq, hbound⟩
      rcases hbound with ⟨hp1, hq0⟩
      dsimp [HullSixTwoFourCuts.Legal, HullSixTwoFourCuts.Boundaries, U]
      omega
    · simp [HullSixTwoFourIsMaximalQFrontier, U]

/-- Stronger current cover, also consuming the total newly-wide exact
dispatcher before falling back to a partial maximal-q frontier. -/
theorem hullSixTwoFour_closedNative_or_maximalQ_cover :
    HullSixTwoFourFixedOrientationCover
      HullSixTwoFourGeometricFrame.IsClosedNativePacket
      HullSixTwoFourIsMaximalQFrontier := by
  intro T hLegal
  by_cases hPacket :
      HullSixTwoFourGeometricFrame.IsClosedNativePacket T
  · exact Or.inl hPacket
  · right
    have hNotP01 :
        ¬HullSixTwoFourGeometricFrame.IsClosedP01Packet T := by
      intro h
      exact hPacket (Or.inl h)
    rcases hullSixTwoFour_closedP01_or_maximalQ_cover T hLegal with
      hP01 | hFrontier
    · exact False.elim (hNotP01 hP01)
    · exact hFrontier

/-- Sound closure of every normalized `2 + 4` input from exact packet
callbacks and genuinely monotone fixed-orientation frontier callbacks. -/
theorem hullSixTwoFourFerrersClosed_of_fixedOrientationCover
    {Packet Top : HullSixTwoFourCuts -> Prop}
    (hCover : HullSixTwoFourFixedOrientationCover Packet Top)
    (hExact : HullSixTwoFourExactPacketProvider Packet)
    (hFrontier : HullSixTwoFourXFrontierProvider Top) :
    HullSixTwoFourFerrersClosed := by
  intro cfg cycle p q R hInput
  rcases hInput with
    ⟨P, Q, hpair, V, rotation, T, hupper, hlower, hLegal, hTable⟩
  let F : HullSixTwoFourGeometricFrame R :=
    ⟨P, Q, hpair, V, rotation, hupper, hlower⟩
  have hExactTable : F.TableHolds T := by
    simpa [F, HullSixTwoFourGeometricFrame.TableHolds] using hTable
  rcases hCover T hLegal with hPacket | ⟨U, hWeak, hULegal, hTop⟩
  · exact hExact F T hLegal hPacket hExactTable
  · have hPartial : F.XFrontierHolds U :=
      F.xFrontierHolds_of_table_weak hLegal hWeak hExactTable
    exact hFrontier F U hULegal hTop hPartial

/-- Direct hull-six endpoint from the sound fixed-orientation `2 + 4`
bridge and any independently closed `3 + 3` provider. -/
theorem geometricHullSixExclusion_of_fixedTwoFourSemanticCover
    {Packet Top : HullSixTwoFourCuts -> Prop}
    (hCover : HullSixTwoFourFixedOrientationCover Packet Top)
    (hExact : HullSixTwoFourExactPacketProvider Packet)
    (hFrontier : HullSixTwoFourXFrontierProvider Top)
    (hThreeThree : HullSixThreeThreeFerrersClosed) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_ferrersClosed
    (hullSixTwoFourFerrersClosed_of_fixedOrientationCover
      hCover hExact hFrontier)
    hThreeThree

/-- Specialized direct endpoint.  The exact adjacent/end-open p01 packets
and newly-wide packets are already discharged.  The remaining explicit
`2 + 4` premise is the thirteen fixed-orientation maximal-q partial
frontiers.  A later cover may narrow that frontier predicate when complete
exact coverage removes an entire first-cut fibre. -/
theorem geometricHullSixExclusion_of_maximalQFrontiers
    (hFrontier :
      HullSixTwoFourXFrontierProvider HullSixTwoFourIsMaximalQFrontier)
    (hThreeThree : HullSixThreeThreeFerrersClosed) :
    GeometricHullSizeExclusion 6 StrictXOrder :=
  geometricHullSixExclusion_of_fixedTwoFourSemanticCover
    hullSixTwoFour_closedNative_or_maximalQ_cover
    hullSixTwoFourClosedNativePacketProvider hFrontier hThreeThree

end Heilbronn8
