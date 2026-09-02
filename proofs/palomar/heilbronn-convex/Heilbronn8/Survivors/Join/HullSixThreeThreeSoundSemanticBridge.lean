import Heilbronn8.Survivors.Join.HullSixFerrersNormalization
import Heilbronn8.Survivors.Join.HullSixThreeThreeBroadTableAdapter
import Heilbronn8.Survivors.Join.HullSixThreeThreeQBlindTableAdapter

/-!
# Sound semantic bridge for hull-six `3 + 3` packets

The finite `3 x 3` bridge is an abstract theorem about a predicate which is
invariant under four table symmetries and contravariant under q-weakening.
Negation of exact table realizability does not have the latter property: an
increased second cut changes `R` cells into `M` cells.  Nor does a finite
table identity, by itself, transport the surrounding geometric frame.

This module keeps the two valid uses separate.

* The broad table and every exact `p = 011` table are contradicted in the
  geometric frame in which they occur.
* All other exact tables may increase only their second cuts, in the same
  frame, to the partial `X`-frontier with `q = 233`.  This partial predicate
  is genuinely monotone and makes no claim about the changed `Y` signs.

Consequently the remaining explicit premise is a scalar closure theorem for
the seventeen maximal-q `X`-frontiers whose first cut is not `011`.  No
nonidentity table symmetry or geometric symmetry custody is asserted here.
-/

set_option relaxedAutoImplicit false

namespace Heilbronn8

/-! ## Fixed-orientation geometry custody -/

/-- The complete data of one normalized `3 + 3` frame, before selecting its
exact Ferrers table. -/
structure HullSixThreeThreeGeometricFrame
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    (R : HullSixCompactCrossChordResidual cfg cycle p q) where
  P : Fin 8
  Q : Fin 8
  pair : HullSixIsOrientedPair p q P Q
  view : HullSixOrientedView cfg cycle P Q
  rotation : Fin 6
  upper_pos : ∀ i : Fin 3,
    0 < sig (cfg P) (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeUpperOffset i)))
  lower_neg : ∀ j : Fin 3,
    sig (cfg P) (cfg Q)
      (cfg (cycle (rotation + hullSixThreeThreeLowerOffset j))) < 0

namespace HullSixThreeThreeGeometricFrame

/-- The `P`-based cross-chord determinant in this fixed frame. -/
def X
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) (i j : Fin 3) : ℝ :=
  sig (cfg F.P)
    (cfg (cycle (F.rotation + hullSixThreeThreeUpperOffset i)))
    (cfg (cycle (F.rotation + hullSixThreeThreeLowerOffset j)))

/-- Exact chamber realization of a cut record in this particular frame. -/
def TableHolds
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (T : HullSixThreeThreeCuts) : Prop :=
  ∀ i j,
    HullSixChamberLabel.Holds (T.table i j) (minTri cfg)
      (sig (cfg F.P)
        (cfg (cycle (F.rotation + hullSixThreeThreeUpperOffset i)))
        (cfg (cycle (F.rotation + hullSixThreeThreeLowerOffset j))))
      (sig (cfg F.Q)
        (cfg (cycle (F.rotation + hullSixThreeThreeUpperOffset i)))
        (cfg (cycle (F.rotation + hullSixThreeThreeLowerOffset j))))

/-- The q-blind partial information attached to a cut record.  It retains
only the `X` signs fixed by the first cuts and the stronger `X` bounds beyond
the selected second-cut frontier. -/
def XFrontierHolds
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (T : HullSixThreeThreeCuts) : Prop :=
  HullSixQBlindFrontierHolds T.p T.q (minTri cfg) F.X

/-- A scalar theorem contradicting only the retained q-blind `X` frontier. -/
def XFrontierClosed
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (T : HullSixThreeThreeCuts) : Prop :=
  F.XFrontierHolds T -> False

/-- Increasing a q-frontier preserves the retained partial `X` data. -/
theorem threeThree_xFrontierHolds_mono
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
supplies the partial `X` frontier of `U`.  No exact realization of `U` is
claimed. -/
theorem xFrontierHolds_of_table_weak
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    {T U : HullSixThreeThreeCuts} (hLegal : T.Legal)
    (hWeak : HullSixThreeThreeCuts.Weak T U)
    (hTable : F.TableHolds T) : F.XFrontierHolds U := by
  let upper : Fin 3 -> ℝ × ℝ := fun i =>
    cfg (cycle (F.rotation + hullSixThreeThreeUpperOffset i))
  let lower : Fin 3 -> ℝ × ℝ := fun j =>
    cfg (cycle (F.rotation + hullSixThreeThreeLowerOffset j))
  let u : Fin 3 -> ℝ := fun i => sig (cfg F.P) (cfg F.Q) (upper i)
  let v : Fin 3 -> ℝ := fun j => -sig (cfg F.P) (cfg F.Q) (lower j)
  let Y : Fin 3 -> Fin 3 -> ℝ := fun i j =>
    sig (cfg F.Q) (upper i) (lower j)

  rcases hLegal with
    ⟨hp01, hp12, hq01, hq12, hpq0, hpq1, hpq2, hp2, hq0⟩
  rcases hWeak with ⟨hp0, hp1, hp2eq, hq0le, hq1le, hq2le⟩
  have hpq : ∀ i, T.p i ≤ T.q i := by
    intro i
    fin_cases i
    · simpa [HullSixThreeThreeCuts.p, HullSixThreeThreeCuts.q] using hpq0
    · simpa [HullSixThreeThreeCuts.p, HullSixThreeThreeCuts.q] using hpq1
    · simpa [HullSixThreeThreeCuts.p, HullSixThreeThreeCuts.q] using hpq2
  have hp : ∀ i, T.p i = U.p i := by
    intro i
    fin_cases i
    · simpa [HullSixThreeThreeCuts.p] using congrArg Fin.val hp0
    · simpa [HullSixThreeThreeCuts.p] using congrArg Fin.val hp1
    · simpa [HullSixThreeThreeCuts.p] using congrArg Fin.val hp2eq
  have hq : ∀ i, T.q i ≤ U.q i := by
    intro i
    fin_cases i
    · simpa [HullSixThreeThreeCuts.q] using hq0le
    · simpa [HullSixThreeThreeCuts.q] using hq1le
    · simpa [HullSixThreeThreeCuts.q] using hq2le
  have hu : ∀ i, minTri cfg ≤ u i := by
    intro i
    have h := F.view.lineLevel_floor
      (F.rotation + hullSixThreeThreeUpperOffset i)
    rw [abs_of_pos (F.upper_pos i)] at h
    simpa [u, upper] using h
  have hv : ∀ j, minTri cfg ≤ v j := by
    intro j
    have h := F.view.lineLevel_floor
      (F.rotation + hullSixThreeThreeLowerOffset j)
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
    simpa [TableHolds, HullSixThreeThreeCuts.table, X, Y, upper, lower] using
      hTable
  have hfront : HullSixQBlindFrontierHolds
      T.p U.q (minTri cfg) F.X :=
    qBlindFrontierHolds_of_ferrers
      (le_of_lt R.minTri_pos) hpq hq hu hv hbase hholds
  exact threeThree_xFrontierHolds_mono hp (fun _ => le_rfl) hfront

/-- `XFrontierClosed` is contravariant under q-weakening because the partial
frontier itself is monotone. -/
theorem xFrontierClosed_of_weak
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    {T U : HullSixThreeThreeCuts}
    (hWeak : HullSixThreeThreeCuts.Weak T U)
    (hClosed : F.XFrontierClosed U) : F.XFrontierClosed T := by
  rcases hWeak with ⟨hp0, hp1, hp2, hq0, hq1, hq2⟩
  intro hT
  apply hClosed
  apply threeThree_xFrontierHolds_mono
    (p := T.p) (p' := U.p) (q := T.q) (q' := U.q)
  · intro i
    fin_cases i
    · simpa [HullSixThreeThreeCuts.p] using congrArg Fin.val hp0
    · simpa [HullSixThreeThreeCuts.p] using congrArg Fin.val hp1
    · simpa [HullSixThreeThreeCuts.p] using congrArg Fin.val hp2
  · intro i
    fin_cases i
    · simpa [HullSixThreeThreeCuts.q] using hq0
    · simpa [HullSixThreeThreeCuts.q] using hq1
    · simpa [HullSixThreeThreeCuts.q] using hq2
  · exact hT

/-! ## Exact native packets -/

/-- Exact-table callback for a packet family in one fixed frame. -/
def ExactPacketClosed
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R)
    (Packet : HullSixThreeThreeCuts -> Prop) : Prop :=
  ∀ T, T.Legal -> Packet T -> F.TableHolds T -> False

/-- The exact `p = 011` family consumed by the existing master adapter. -/
def IsQBlindP011Packet (T : HullSixThreeThreeCuts) : Prop :=
  T.p0 = 0 ∧ T.p1 = 1 ∧ T.p2 = 1

/-- The exact packets currently closed in their native orientation: the
broad table and all fifteen legal tables with `p = 011`. -/
def IsClosedNativePacket (T : HullSixThreeThreeCuts) : Prop :=
  T = HullSixThreeThreeCuts.broad ∨ IsQBlindP011Packet T

/-- The broad and `p = 011` table adapters assemble into one exact packet
callback without weakening or finite-table symmetry. -/
theorem closedNativePacket_exact
    {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) :
    F.ExactPacketClosed IsClosedNativePacket := by
  intro T hLegal hPacket hTable
  rcases hPacket with hBroad | hP011
  · subst T
    exact R.threeThreeBroadAt_false F.pair F.view F.rotation
      F.upper_pos F.lower_neg hTable
  · rcases hP011 with ⟨hp0, hp1, hp2⟩
    exact R.threeThreeQBlindAt_false F.view F.rotation
      F.upper_pos F.lower_neg T hLegal hp0 hp1 hp2 hTable

end HullSixThreeThreeGeometricFrame

/-! ## Sound fixed-orientation endpoint -/

/-- A scalar provider for an exact packet family in every normalized frame. -/
def HullSixThreeThreeExactPacketProvider
    (Packet : HullSixThreeThreeCuts -> Prop) : Prop :=
  ∀ {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R),
    F.ExactPacketClosed Packet

/-- Existing broad and `p = 011` adapters as a global fixed-frame provider. -/
theorem hullSixThreeThreeClosedNativePacketProvider :
    HullSixThreeThreeExactPacketProvider
      HullSixThreeThreeGeometricFrame.IsClosedNativePacket := by
  intro cfg cycle p q R F
  exact F.closedNativePacket_exact

/-- A scalar provider for genuinely partial q-blind `X` frontiers. -/
def HullSixThreeThreeXFrontierProvider
    (Top : HullSixThreeThreeCuts -> Prop) : Prop :=
  ∀ {cfg : Configuration} {cycle : Fin 6 -> Fin 8} {p q : Fin 8}
    {R : HullSixCompactCrossChordResidual cfg cycle p q}
    (F : HullSixThreeThreeGeometricFrame R) (U : HullSixThreeThreeCuts),
    U.Legal -> Top U -> F.XFrontierClosed U

/-- A pure fixed-orientation cover.  An exact table is either consumed in
place or weakened, without changing frame, to a partial frontier. -/
def HullSixThreeThreeFixedOrientationCover
    (Packet Top : HullSixThreeThreeCuts -> Prop) : Prop :=
  ∀ T : HullSixThreeThreeCuts, T.Legal ->
    Packet T ∨
      ∃ U : HullSixThreeThreeCuts,
        HullSixThreeThreeCuts.Weak T U ∧ U.Legal ∧ Top U

/-- The unique maximal second-cut triple allowed by the `3 x 3` boundary
conditions. -/
def HullSixThreeThreeIsMaximalQFrontier
    (T : HullSixThreeThreeCuts) : Prop :=
  T.q0 = 2 ∧ T.q1 = 3 ∧ T.q2 = 3

/-- The seventeen maximal-q frontiers not already closed by the exact
`p = 011` packet family. -/
def HullSixThreeThreeIsRemainingMaximalQFrontier
    (T : HullSixThreeThreeCuts) : Prop :=
  HullSixThreeThreeIsMaximalQFrontier T ∧
    ¬HullSixThreeThreeGeometricFrame.IsQBlindP011Packet T

/-- Every legal table is either a native exact packet or weakens, in its
original frame, to the maximal q-frontier with the same first cuts. -/
theorem hullSixThreeThree_closedNative_or_maximalQ_cover :
    HullSixThreeThreeFixedOrientationCover
      HullSixThreeThreeGeometricFrame.IsClosedNativePacket
      HullSixThreeThreeIsRemainingMaximalQFrontier := by
  intro T hLegal
  by_cases hPacket :
      HullSixThreeThreeGeometricFrame.IsClosedNativePacket T
  · exact Or.inl hPacket
  · right
    have hNotP011 :
        ¬HullSixThreeThreeGeometricFrame.IsQBlindP011Packet T := by
      intro h
      exact hPacket (Or.inr h)
    rcases hLegal with
      ⟨hp01, hp12, hq01, hq12, hpq0, hpq1, hpq2, hp2, hq0⟩
    let U : HullSixThreeThreeCuts :=
      ⟨T.p0, T.p1, T.p2, 2, 3, 3⟩
    refine ⟨U, ?_, ?_, ?_⟩
    · dsimp [HullSixThreeThreeCuts.Weak, U]
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · omega
      constructor <;> omega
    · dsimp [HullSixThreeThreeCuts.Legal, U]
      omega
    · refine ⟨?_, ?_⟩
      · simp [HullSixThreeThreeIsMaximalQFrontier, U]
      · intro hU
        apply hNotP011
        simpa [HullSixThreeThreeGeometricFrame.IsQBlindP011Packet, U] using hU

/-- Sound closure of every normalized `3 + 3` input from exact native packet
callbacks and fixed-orientation partial-frontier callbacks. -/
theorem hullSixThreeThreeFerrersClosed_of_fixedOrientationCover
    {Packet Top : HullSixThreeThreeCuts -> Prop}
    (hCover : HullSixThreeThreeFixedOrientationCover Packet Top)
    (hExact : HullSixThreeThreeExactPacketProvider Packet)
    (hFrontier : HullSixThreeThreeXFrontierProvider Top) :
    HullSixThreeThreeFerrersClosed := by
  intro cfg cycle p q R hInput
  rcases hInput with
    ⟨P, Q, hpair, V, rotation, T, hupper, hlower, hLegal, hTable⟩
  let F : HullSixThreeThreeGeometricFrame R :=
    ⟨P, Q, hpair, V, rotation, hupper, hlower⟩
  have hExactTable : F.TableHolds T := by
    simpa [F, HullSixThreeThreeGeometricFrame.TableHolds] using hTable
  rcases hCover T hLegal with hPacket | ⟨U, hWeak, hULegal, hTop⟩
  · exact hExact F T hLegal hPacket hExactTable
  · have hPartial : F.XFrontierHolds U :=
      F.xFrontierHolds_of_table_weak hLegal hWeak hExactTable
    exact hFrontier F U hULegal hTop hPartial

/-- Specialized honest `3 + 3` closer.  The exact broad and `p = 011`
packets are already discharged; the only remaining premise is closure of
the seventeen fixed-orientation maximal-q partial `X` frontiers. -/
theorem hullSixThreeThreeFerrersClosed_of_remainingMaximalQFrontiers
    (hFrontier : HullSixThreeThreeXFrontierProvider
      HullSixThreeThreeIsRemainingMaximalQFrontier) :
    HullSixThreeThreeFerrersClosed :=
  hullSixThreeThreeFerrersClosed_of_fixedOrientationCover
    hullSixThreeThree_closedNative_or_maximalQ_cover
    hullSixThreeThreeClosedNativePacketProvider hFrontier

end Heilbronn8
