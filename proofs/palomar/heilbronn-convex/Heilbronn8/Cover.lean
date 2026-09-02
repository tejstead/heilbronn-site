import Heilbronn8.CoverGeometry
import Heilbronn8.CertCheckX

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace Heilbronn8

/-! ## Dyadic cover layer -/

structure Box where
  bounds : Fin 5 -> Prod Rat Rat

def Box.Mem (x : Fin 5 -> Real) (B : Box) : Prop :=
  ∀ i,
    (B.bounds i).1 <= x i ∧
      x i <= (B.bounds i).2

/-- An exact dyadic number `numerator / 2^exponent`. -/
structure Dyadic where
  numerator : Int
  exponent : Nat

def Dyadic.value (d : Dyadic) : Rat :=
  d.numerator / (2 : Rat) ^ d.exponent

inductive LeafTag where
  | farkas (ref : Nat)
  | incumbent (ref : Nat)

inductive SplitTree where
  | leaf (tag : LeafTag)
  | node
      (coord : Fin 5) (mid : Dyadic)
      (left right : SplitTree)
  /-- An exact spatial split at an arbitrary rational endpoint. -/
  | rationalNode
      (coord : Fin 5) (mid : Rat)
      (left right : SplitTree)
  | signNode
      (form : CertCheckX.Row)
      (nonpos nonneg : SplitTree)
  /-- A proof-layer semantic gate. If the checker premise is available, the
  tagged leaf is owned; otherwise the configuration is sent to an explicit
  fallback subtree (normally the residual corpus obligation). -/
  | semanticNode
      (premise : (Fin 5 → Real) → (Fin 5 → Real) → Prop)
      (tag : LeafTag) (fallback : SplitTree)

/--
Owned coordinate regions use `< mid` on the left and `mid <=` on the right,
matching the shard partition convention. Sign children compare the underlying
row weakly in opposite directions and may overlap only on its equality set.
-/
inductive ReachesLeaf
    (x y : Fin 5 -> Real) :
    SplitTree -> LeafTag -> Prop where
  | leaf (tag) :
      ReachesLeaf x y (.leaf tag) tag
  | nodeLeft {coord mid left right tag}
      (hside : x coord < (mid.value : Real))
      (hreach : ReachesLeaf x y left tag) :
      ReachesLeaf x y (.node coord mid left right) tag
  | nodeRight {coord mid left right tag}
      (hside : (mid.value : Real) <= x coord)
      (hreach : ReachesLeaf x y right tag) :
      ReachesLeaf x y (.node coord mid left right) tag
  | rationalNodeLeft {coord} {mid : Rat} {left right tag}
      (hside : x coord < (mid : Real))
      (hreach : ReachesLeaf x y left tag) :
      ReachesLeaf x y (.rationalNode coord mid left right) tag
  | rationalNodeRight {coord} {mid : Rat} {left right tag}
      (hside : (mid : Real) <= x coord)
      (hreach : ReachesLeaf x y right tag) :
      ReachesLeaf x y (.rationalNode coord mid left right) tag
  | signNonpos {form nonpos nonneg tag}
      (hside : form.lhs x y <= form.rhsValue x)
      (hreach : ReachesLeaf x y nonpos tag) :
      ReachesLeaf x y (.signNode form nonpos nonneg) tag
  | signNonneg {form nonpos nonneg tag}
      (hside : form.rhsValue x <= form.lhs x y)
      (hreach : ReachesLeaf x y nonneg tag) :
      ReachesLeaf x y (.signNode form nonpos nonneg) tag
  | semanticHit {premise tag fallback}
      (hsemantic : premise x y) :
      ReachesLeaf x y (.semanticNode premise tag fallback) tag
  | semanticMiss {premise owned fallback tag}
      (hsemantic : ¬premise x y)
      (hreach : ReachesLeaf x y fallback tag) :
      ReachesLeaf x y (.semanticNode premise owned fallback) tag

/-- Structural invariant saying that every leaf reachable from a tree
satisfies a tag-indexed semantic proposition. -/
def SplitTree.LeavesSatisfy
    (x y : Fin 5 → Real) (semantic : LeafTag → Prop) : SplitTree → Prop
  | .leaf tag => semantic tag
  | .node _ _ left right =>
      left.LeavesSatisfy x y semantic ∧ right.LeavesSatisfy x y semantic
  | .rationalNode _ _ left right =>
      left.LeavesSatisfy x y semantic ∧ right.LeavesSatisfy x y semantic
  | .signNode _ nonpos nonneg =>
      nonpos.LeavesSatisfy x y semantic ∧ nonneg.LeavesSatisfy x y semantic
  | .semanticNode premise tag fallback =>
      (premise x y → semantic tag) ∧
        fallback.LeavesSatisfy x y semantic

theorem ReachesLeaf.semantic
    {x y : Fin 5 → Real} {T : SplitTree} {tag : LeafTag}
    {semantic : LeafTag → Prop}
    (hvalid : T.LeavesSatisfy x y semantic)
    (hreach : ReachesLeaf x y T tag) : semantic tag := by
  induction hreach with
  | leaf tag => exact hvalid
  | nodeLeft _ _ ih => exact ih hvalid.1
  | nodeRight _ _ ih => exact ih hvalid.2
  | rationalNodeLeft _ _ ih => exact ih hvalid.1
  | rationalNodeRight _ _ ih => exact ih hvalid.2
  | signNonpos _ _ ih => exact ih hvalid.1
  | signNonneg _ _ ih => exact ih hvalid.2
  | semanticHit hsemantic => exact hvalid.1 hsemantic
  | semanticMiss _ _ ih => exact ih hvalid.2

def LeafRegion
    (root : Box) (T : SplitTree)
    (x y : Fin 5 -> Real)
    (tag : LeafTag) : Prop :=
  root.Mem x ∧ ReachesLeaf x y T tag

theorem SplitTree.cover
    (root : Box) (T : SplitTree)
    (x y : Fin 5 -> Real)
    (hx : root.Mem x) :
    ∃ tag, LeafRegion root T x y tag := by
  induction T with
  | leaf tag =>
      exact ⟨tag, hx, ReachesLeaf.leaf tag⟩
  | node coord mid left right ihLeft ihRight =>
      rcases
        lt_or_ge (x coord) (mid.value : Real)
      with hlt | hge
      · obtain ⟨tag, _, hreach⟩ := ihLeft
        exact
          ⟨tag, hx, ReachesLeaf.nodeLeft hlt hreach⟩
      · obtain ⟨tag, _, hreach⟩ := ihRight
        exact
          ⟨tag, hx, ReachesLeaf.nodeRight hge hreach⟩
  | rationalNode coord mid left right ihLeft ihRight =>
      rcases lt_or_ge (x coord) (mid : Real) with hlt | hge
      · obtain ⟨tag, _, hreach⟩ := ihLeft
        exact
          ⟨tag, hx, ReachesLeaf.rationalNodeLeft hlt hreach⟩
      · obtain ⟨tag, _, hreach⟩ := ihRight
        exact
          ⟨tag, hx, ReachesLeaf.rationalNodeRight hge hreach⟩
  | signNode form nonpos nonneg ihNonpos ihNonneg =>
      rcases
        le_total (form.lhs x y) (form.rhsValue x)
      with hle | hge
      · obtain ⟨tag, _, hreach⟩ := ihNonpos
        exact
          ⟨tag, hx,
            ReachesLeaf.signNonpos hle hreach⟩
      · obtain ⟨tag, _, hreach⟩ := ihNonneg
        exact
          ⟨tag, hx,
            ReachesLeaf.signNonneg hge hreach⟩
  | semanticNode premise owned fallback ihFallback =>
      classical
      by_cases hsemantic : premise x y
      · exact ⟨owned, hx, ReachesLeaf.semanticHit hsemantic⟩
      · obtain ⟨tag, _, hreach⟩ := ihFallback
        exact ⟨tag, hx, ReachesLeaf.semanticMiss hsemantic hreach⟩

/-! ## Generated-data interfaces -/

/--
Generated-data slot 1.

For every Farkas-tagged leaf, the generator emits the kernel check and proves
that any normalized beating configuration in the split-tree region has its
five x-coordinates in the certificate box and satisfies every stored row at
its five x- and five y-coordinates. The stored rows already include the
sign-cell and beat inequalities.
-/
def FarkasGeneratedData
    (H : Configuration -> Real) (q : Real)
    (root : Box) (T : SplitTree)
    (certificates : Nat -> CertCheckX.Leaf) : Prop :=
  ∀ (ref : Nat) (v : Configuration),
    GaugeNormalized v ->
    Beats H q v ->
    LeafRegion root T
      (xCoordsOf v) (yCoordsOf v) (.farkas ref) ->
    CertCheckX.CheckLeafX (certificates ref) = true ∧
      (certificates ref).inXbox (xCoordsOf v) ∧
      CertCheckX.satisfiesAll
        (certificates ref) (xCoordsOf v) (yCoordsOf v)

/--
Generated-data slot 2, discharged by the neighborhood-certificate module.
-/
def IncumbentDischarge
    (H : Configuration -> Real) (q : Real)
    (root : Box) (T : SplitTree) : Prop :=
  ∀ (ref : Nat) (v : Configuration),
    GaugeNormalized v ->
    LeafRegion root T
      (xCoordsOf v) (yCoordsOf v)
      (.incumbent ref) ->
    ¬ Beats H q v

/--
Final phase-3 dispatch.

`hRoot` is the hand-written gauge-to-root-box lemma. The last two hypotheses
are the generated/module data slots.
-/
theorem main_bound_skeleton
    (H : Configuration -> Real) (q : Real)
    (root : Box) (T : SplitTree)
    (certificates : Nat -> CertCheckX.Leaf)
    (hRoot : ∀ v : Configuration,
      GaugeNormalized v -> root.Mem (xCoordsOf v))
    (generatedFarkas :
      FarkasGeneratedData H q root T certificates)
    (incumbentNeighborhood :
      IncumbentDischarge H q root T) :
    ∀ v : Configuration,
      GaugeNormalized v -> ¬ Beats H q v := by
  intro v hv hbeat
  have hx : root.Mem (xCoordsOf v) :=
    hRoot v hv
  obtain ⟨tag, hregion⟩ :=
    SplitTree.cover root T
      (xCoordsOf v) (yCoordsOf v) hx
  cases tag with
  | farkas ref =>
      obtain ⟨hcheck, hxbox, hrows⟩ :=
        generatedFarkas ref v hv hbeat hregion
      exact
        CertCheckX.soundness
          (certificates ref) hcheck
          (xCoordsOf v) (yCoordsOf v) hxbox hrows
  | incumbent ref =>
      exact
        incumbentNeighborhood ref v hv hregion hbeat

end Heilbronn8
