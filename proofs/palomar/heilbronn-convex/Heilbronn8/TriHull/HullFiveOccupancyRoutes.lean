import Heilbronn8.TriHull.HullFiveOccupancyCombinatorics

/-!
# Finite canonical routes for hull-five occupancy profiles

This module chooses the cyclic anchor and the permutation of the three
off-cycle points needed by the metric endpoint theorems.  It contains no
geometry.  All searches range over `Fin 5`, the six permutations of
`Fin 3`, and the eleven point regions.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace Heilbronn8.TriHull

/-- The three point-region labels as a finite tuple. -/
def hullFiveRegionTriple
    (P Q R : HullFivePointRegion) : Fin 3 → HullFivePointRegion :=
  ![P, Q, R]

inductive HullFiveEndMajor where
  | first
  | middle
deriving Repr, DecidableEq

instance : Fintype HullFiveEndMajor where
  elems := {.first, .middle}
  complete x := by cases x <;> simp

inductive HullFive111RouteKind where
  | uz
  | vz
deriving Repr, DecidableEq

instance : Fintype HullFive111RouteKind where
  elems := {.uz, .vz}
  complete x := by cases x <;> simp

private def decidableForallHullFiveRegionTriple
    (p : HullFivePointRegion → HullFivePointRegion →
      HullFivePointRegion → Prop)
    (hp : ∀ P Q R, Decidable (p P Q R)) :
    Decidable (∀ P Q R, p P Q R) := by
  let rDec (P Q : HullFivePointRegion) :
      DecidablePred (fun R => p P Q R) :=
    fun R => hp P Q R
  let qDec (P : HullFivePointRegion) :
      DecidablePred (fun Q => ∀ R, p P Q R) :=
    fun Q => by
      letI := rDec P Q
      exact Fintype.decidableForallFintype
  let pDec : DecidablePred (fun P => ∀ Q R, p P Q R) :=
    fun P => by
      letI := qDec P
      exact Fintype.decidableForallFintype
  letI := pDec
  exact Fintype.decidableForallFintype

private def centralExistsDecidable
    (P Q R : HullFivePointRegion) :
    Decidable (∃ anchor : Fin 5,
      (hullFiveRegionCounts P Q R anchor).IsCentral300) := by
  letI : DecidablePred (fun anchor : Fin 5 =>
      (hullFiveRegionCounts P Q R anchor).IsCentral300) :=
    fun _ => by
      unfold HullFiveRegionCounts.IsCentral300
      infer_instance
  exact Fintype.decidableExistsFintype

private def endExistsDecidable
    (P Q R : HullFivePointRegion) :
    Decidable (∃ anchor : Fin 5,
      (hullFiveRegionCounts P Q R anchor).IsEnd210) := by
  letI : DecidablePred (fun anchor : Fin 5 =>
      (hullFiveRegionCounts P Q R anchor).IsEnd210) :=
    fun _ => by
      unfold HullFiveRegionCounts.IsEnd210
      infer_instance
  exact Fintype.decidableExistsFintype

private def middleExistsDecidable
    (P Q R : HullFivePointRegion) :
    Decidable (∃ anchor : Fin 5,
      (hullFiveRegionCounts P Q R anchor).IsMiddle210) := by
  letI : DecidablePred (fun anchor : Fin 5 =>
      (hullFiveRegionCounts P Q R anchor).IsMiddle210) :=
    fun _ => by
      unfold HullFiveRegionCounts.IsMiddle210
      infer_instance
  exact Fintype.decidableExistsFintype

private def all111Decidable
    (P Q R : HullFivePointRegion) :
    Decidable (∀ anchor : Fin 5,
      (hullFiveRegionCounts P Q R anchor).Is111) := by
  letI : DecidablePred (fun anchor : Fin 5 =>
      (hullFiveRegionCounts P Q R anchor).Is111) :=
    fun _ => by
      unfold HullFiveRegionCounts.Is111
      infer_instance
  exact Fintype.decidableForallFintype

/-- Canonical data for the two end-zero homogeneous endpoints. -/
structure HullFiveEndRoute
    (P Q R : HullFivePointRegion) where
  anchor : Fin 5
  inner : Equiv.Perm (Fin 3)
  major : HullFiveEndMajor
  cells :
    let region := hullFiveRegionTriple P Q R
    match major with
    | .first =>
        (region (inner 0)).fanCell anchor = 0 ∧
        (region (inner 1)).fanCell anchor = 0 ∧
        (region (inner 2)).fanCell anchor = 1
    | .middle =>
        (region (inner 0)).fanCell anchor = 1 ∧
        (region (inner 1)).fanCell anchor = 1 ∧
        (region (inner 2)).fanCell anchor = 0

/-- A central route needs only the cyclic anchor: all three points occupy
the standard middle fan triangle there. -/
structure HullFiveCentralRoute
    (P Q R : HullFivePointRegion) where
  anchor : Fin 5
  cells : P.fanCell anchor = 1 ∧
    Q.fanCell anchor = 1 ∧ R.fanCell anchor = 1

theorem hullFiveCentralRoute_of_counts :
    ∀ P Q R : HullFivePointRegion,
      (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsCentral300) →
      ∃ anchor : Fin 5,
        P.fanCell anchor = 1 ∧ Q.fanCell anchor = 1 ∧
          R.fanCell anchor = 1 := by
  let fixedDec (P Q R : HullFivePointRegion) : Decidable
      ((∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsCentral300) →
        ∃ anchor : Fin 5,
          P.fanCell anchor = 1 ∧ Q.fanCell anchor = 1 ∧
            R.fanCell anchor = 1) := by
    letI := centralExistsDecidable P Q R
    letI : DecidablePred (fun anchor : Fin 5 =>
        P.fanCell anchor = 1 ∧ Q.fanCell anchor = 1 ∧
          R.fanCell anchor = 1) :=
      fun _ => inferInstance
    letI : Decidable (∃ anchor : Fin 5,
        P.fanCell anchor = 1 ∧ Q.fanCell anchor = 1 ∧
          R.fanCell anchor = 1) :=
      Fintype.decidableExistsFintype
    infer_instance
  letI := decidableForallHullFiveRegionTriple _ fixedDec
  decide

theorem hullFiveEndRoute_of_counts :
    ∀ P Q R : HullFivePointRegion,
      (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsEnd210) →
      ∃ anchor : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
        ∃ major : HullFiveEndMajor,
          let region := hullFiveRegionTriple P Q R
          match major with
          | .first =>
              (region (inner 0)).fanCell anchor = 0 ∧
              (region (inner 1)).fanCell anchor = 0 ∧
              (region (inner 2)).fanCell anchor = 1
          | .middle =>
              (region (inner 0)).fanCell anchor = 1 ∧
              (region (inner 1)).fanCell anchor = 1 ∧
              (region (inner 2)).fanCell anchor = 0 := by
  let fixedDec (P Q R : HullFivePointRegion) : Decidable
      ((∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsEnd210) →
        ∃ anchor : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
          ∃ major : HullFiveEndMajor,
            let region := hullFiveRegionTriple P Q R
            match major with
            | .first =>
                (region (inner 0)).fanCell anchor = 0 ∧
                (region (inner 1)).fanCell anchor = 0 ∧
                (region (inner 2)).fanCell anchor = 1
            | .middle =>
                (region (inner 0)).fanCell anchor = 1 ∧
                (region (inner 1)).fanCell anchor = 1 ∧
                (region (inner 2)).fanCell anchor = 0) := by
    letI := endExistsDecidable P Q R
    let routeCells (anchor : Fin 5) (inner : Equiv.Perm (Fin 3))
        (major : HullFiveEndMajor) : Prop :=
      let region := hullFiveRegionTriple P Q R
      match major with
      | .first =>
          (region (inner 0)).fanCell anchor = 0 ∧
          (region (inner 1)).fanCell anchor = 0 ∧
          (region (inner 2)).fanCell anchor = 1
      | .middle =>
          (region (inner 0)).fanCell anchor = 1 ∧
          (region (inner 1)).fanCell anchor = 1 ∧
          (region (inner 2)).fanCell anchor = 0
    let majorDec (anchor : Fin 5) (inner : Equiv.Perm (Fin 3)) :
        DecidablePred (routeCells anchor inner) :=
      fun major => by
        cases major <;> dsimp [routeCells] <;> infer_instance
    let innerDec (anchor : Fin 5) : DecidablePred
        (fun inner : Equiv.Perm (Fin 3) =>
          ∃ major : HullFiveEndMajor, routeCells anchor inner major) :=
      fun inner => by
        letI := majorDec anchor inner
        exact Fintype.decidableExistsFintype
    let anchorDec : DecidablePred
        (fun anchor : Fin 5 =>
          ∃ inner : Equiv.Perm (Fin 3),
            ∃ major : HullFiveEndMajor, routeCells anchor inner major) :=
      fun anchor => by
        letI := innerDec anchor
        exact Fintype.decidableExistsFintype
    letI : Decidable
        (∃ anchor : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
          ∃ major : HullFiveEndMajor, routeCells anchor inner major) := by
      letI := anchorDec
      exact Fintype.decidableExistsFintype
    change Decidable
      ((∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsEnd210) →
        ∃ anchor : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
          ∃ major : HullFiveEndMajor, routeCells anchor inner major)
    infer_instance
  letI := decidableForallHullFiveRegionTriple _ fixedDec
  decide

/-- The three cyclic full profiles which can survive when an end-zero
dispatcher returns its all-in-`BXC` right-ear residue. -/
def HullFivePointRegion.IsEndRightAAt
    (region : HullFivePointRegion) (k : Fin 5) : Prop :=
  ∀ j : Fin 5, region.fanCell (k + j) = ![1, 0, 0, 2, 2] j

def HullFivePointRegion.IsEndRightBAt
    (region : HullFivePointRegion) (k : Fin 5) : Prop :=
  ∀ j : Fin 5, region.fanCell (k + j) = ![1, 0, 1, 2, 1] j

def HullFivePointRegion.IsEndRightCAt
    (region : HullFivePointRegion) (k : Fin 5) : Prop :=
  ∀ j : Fin 5, region.fanCell (k + j) = ![0, 0, 2, 2, 1] j

private instance (region : HullFivePointRegion) (k : Fin 5) :
    Decidable (region.IsEndRightAAt k) := by
  unfold HullFivePointRegion.IsEndRightAAt
  letI : DecidablePred (fun j : Fin 5 =>
      region.fanCell (k + j) = ![1, 0, 0, 2, 2] j) :=
    fun _ => inferInstance
  exact Fintype.decidableForallFintype

private instance (region : HullFivePointRegion) (k : Fin 5) :
    Decidable (region.IsEndRightBAt k) := by
  unfold HullFivePointRegion.IsEndRightBAt
  letI : DecidablePred (fun j : Fin 5 =>
      region.fanCell (k + j) = ![1, 0, 1, 2, 1] j) :=
    fun _ => inferInstance
  exact Fintype.decidableForallFintype

private instance (region : HullFivePointRegion) (k : Fin 5) :
    Decidable (region.IsEndRightCAt k) := by
  unfold HullFivePointRegion.IsEndRightCAt
  letI : DecidablePred (fun j : Fin 5 =>
      region.fanCell (k + j) = ![0, 0, 2, 2, 1] j) :=
    fun _ => inferInstance
  exact Fintype.decidableForallFintype

/-- Priority-aware end route with the exact right-ear residue exposed.

If the next anchored fan is not uniformly in cell `0`, an all-in-`BXC`
geometric residue contradicts fan-cell disjointness.  Otherwise the three
full cyclic profiles are, up to the endpoint ordering, exactly `CCA`, `CAA`,
or `CAB` (including the two CAB orders). -/
theorem hullFiveEndRoute_with_rightResidual :
    ∀ P Q R : HullFivePointRegion,
      ¬ (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsCentral300) →
      (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsEnd210) →
      ∃ k : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
        ∃ major : HullFiveEndMajor,
          let region := hullFiveRegionTriple P Q R
          (match major with
          | .first =>
              (region (inner 0)).fanCell k = 0 ∧
              (region (inner 1)).fanCell k = 0 ∧
              (region (inner 2)).fanCell k = 1
          | .middle =>
              (region (inner 0)).fanCell k = 1 ∧
              (region (inner 1)).fanCell k = 1 ∧
              (region (inner 2)).fanCell k = 0) ∧
          ((∃ i : Fin 3,
              (region (inner i)).fanCell (k + 1) ≠ 0) ∨
            match major with
            | .first =>
                (region (inner 0)).IsEndRightCAt k ∧
                (region (inner 1)).IsEndRightCAt k ∧
                (region (inner 2)).IsEndRightAAt k
            | .middle =>
                (region (inner 2)).IsEndRightCAt k ∧
                (((region (inner 0)).IsEndRightAAt k ∧
                    (region (inner 1)).IsEndRightAAt k) ∨
                  ((region (inner 0)).IsEndRightAAt k ∧
                    (region (inner 1)).IsEndRightBAt k) ∨
                  ((region (inner 0)).IsEndRightBAt k ∧
                    (region (inner 1)).IsEndRightAAt k))) := by
  let fixedDec (P Q R : HullFivePointRegion) : Decidable
      (¬ (∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsCentral300) →
        (∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsEnd210) →
        ∃ k : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
          ∃ major : HullFiveEndMajor,
            let region := hullFiveRegionTriple P Q R
            (match major with
            | .first =>
                (region (inner 0)).fanCell k = 0 ∧
                (region (inner 1)).fanCell k = 0 ∧
                (region (inner 2)).fanCell k = 1
            | .middle =>
                (region (inner 0)).fanCell k = 1 ∧
                (region (inner 1)).fanCell k = 1 ∧
                (region (inner 2)).fanCell k = 0) ∧
            ((∃ i : Fin 3,
                (region (inner i)).fanCell (k + 1) ≠ 0) ∨
              match major with
              | .first =>
                  (region (inner 0)).IsEndRightCAt k ∧
                  (region (inner 1)).IsEndRightCAt k ∧
                  (region (inner 2)).IsEndRightAAt k
              | .middle =>
                  (region (inner 2)).IsEndRightCAt k ∧
                  (((region (inner 0)).IsEndRightAAt k ∧
                      (region (inner 1)).IsEndRightAAt k) ∨
                    ((region (inner 0)).IsEndRightAAt k ∧
                      (region (inner 1)).IsEndRightBAt k) ∨
                    ((region (inner 0)).IsEndRightBAt k ∧
                      (region (inner 1)).IsEndRightAAt k)))) := by
    letI := centralExistsDecidable P Q R
    letI := endExistsDecidable P Q R
    let result (k : Fin 5) (inner : Equiv.Perm (Fin 3))
        (major : HullFiveEndMajor) : Prop :=
      let region := hullFiveRegionTriple P Q R
      (match major with
      | .first =>
          (region (inner 0)).fanCell k = 0 ∧
          (region (inner 1)).fanCell k = 0 ∧
          (region (inner 2)).fanCell k = 1
      | .middle =>
          (region (inner 0)).fanCell k = 1 ∧
          (region (inner 1)).fanCell k = 1 ∧
          (region (inner 2)).fanCell k = 0) ∧
      ((∃ i : Fin 3,
          (region (inner i)).fanCell (k + 1) ≠ 0) ∨
        match major with
        | .first =>
            (region (inner 0)).IsEndRightCAt k ∧
            (region (inner 1)).IsEndRightCAt k ∧
            (region (inner 2)).IsEndRightAAt k
        | .middle =>
            (region (inner 2)).IsEndRightCAt k ∧
            (((region (inner 0)).IsEndRightAAt k ∧
                (region (inner 1)).IsEndRightAAt k) ∨
              ((region (inner 0)).IsEndRightAAt k ∧
                (region (inner 1)).IsEndRightBAt k) ∨
              ((region (inner 0)).IsEndRightBAt k ∧
                (region (inner 1)).IsEndRightAAt k)))
    let majorDec (k : Fin 5) (inner : Equiv.Perm (Fin 3)) :
        DecidablePred (result k inner) :=
      fun major => by
        let region := hullFiveRegionTriple P Q R
        letI : DecidablePred (fun i : Fin 3 =>
            (region (inner i)).fanCell (k + 1) ≠ 0) :=
          fun _ => inferInstance
        letI : Decidable (∃ i : Fin 3,
            (region (inner i)).fanCell (k + 1) ≠ 0) :=
          Fintype.decidableExistsFintype
        cases major <;> dsimp [result] <;> infer_instance
    let innerDec (k : Fin 5) : DecidablePred
        (fun inner : Equiv.Perm (Fin 3) =>
          ∃ major : HullFiveEndMajor, result k inner major) :=
      fun inner => by
        letI := majorDec k inner
        exact Fintype.decidableExistsFintype
    let anchorDec : DecidablePred
        (fun k : Fin 5 =>
          ∃ inner : Equiv.Perm (Fin 3),
            ∃ major : HullFiveEndMajor, result k inner major) :=
      fun k => by
        letI := innerDec k
        exact Fintype.decidableExistsFintype
    letI : Decidable
        (∃ k : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
          ∃ major : HullFiveEndMajor, result k inner major) := by
      letI := anchorDec
      exact Fintype.decidableExistsFintype
    change Decidable
      (¬ (∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsCentral300) →
        (∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsEnd210) →
        ∃ k : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
          ∃ major : HullFiveEndMajor, result k inner major)
    infer_instance
  letI := decidableForallHullFiveRegionTriple _ fixedDec
  decide

/-- Every all-anchor `111` triple has a cyclic reanchor and point ordering
which is exactly one of the compact `UZ`/`VZ` membership packets.

The cell rows below are simply the seven packet triangles expressed in the
five standard fans.  For example, relative to anchor `k`, `ABC` is cell `1`
at `k+3`, `ABD` is cell `0` at `k+4`, and `BCD` is cell `1` at `k+1`. -/
theorem hullFive111Route_of_counts :
    ∀ P Q R : HullFivePointRegion,
      (∀ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).Is111) →
      ∃ k : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
        ∃ kind : HullFive111RouteKind,
          let region := hullFiveRegionTriple P Q R
          let p := region (inner 0)
          let q := region (inner 1)
          let r := region (inner 2)
          match kind with
          | .uz =>
              p.fanCell k = 0 ∧
              p.fanCell (k + 1) = 0 ∧
              q.fanCell (k + 3) = 1 ∧
              q.fanCell k = 1 ∧
              q.fanCell (k + 4) = 0 ∧
              r.fanCell (k + 1) = 1 ∧
              r.fanCell k = 2
          | .vz =>
              p.fanCell (k + 3) = 1 ∧
              p.fanCell k = 0 ∧
              p.fanCell (k + 4) = 0 ∧
              q.fanCell k = 1 ∧
              q.fanCell (k + 1) = 0 ∧
              r.fanCell (k + 1) = 1 ∧
              r.fanCell k = 2 := by
  let fixedDec (P Q R : HullFivePointRegion) : Decidable
      ((∀ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).Is111) →
        ∃ k : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
          ∃ kind : HullFive111RouteKind,
            let region := hullFiveRegionTriple P Q R
            let p := region (inner 0)
            let q := region (inner 1)
            let r := region (inner 2)
            match kind with
            | .uz =>
                p.fanCell k = 0 ∧
                p.fanCell (k + 1) = 0 ∧
                q.fanCell (k + 3) = 1 ∧
                q.fanCell k = 1 ∧
                q.fanCell (k + 4) = 0 ∧
                r.fanCell (k + 1) = 1 ∧
                r.fanCell k = 2
            | .vz =>
                p.fanCell (k + 3) = 1 ∧
                p.fanCell k = 0 ∧
                p.fanCell (k + 4) = 0 ∧
                q.fanCell k = 1 ∧
                q.fanCell (k + 1) = 0 ∧
                r.fanCell (k + 1) = 1 ∧
                r.fanCell k = 2) := by
    letI := all111Decidable P Q R
    let packet (k : Fin 5) (inner : Equiv.Perm (Fin 3))
        (kind : HullFive111RouteKind) : Prop :=
      let region := hullFiveRegionTriple P Q R
      let p := region (inner 0)
      let q := region (inner 1)
      let r := region (inner 2)
      match kind with
      | .uz =>
          p.fanCell k = 0 ∧
          p.fanCell (k + 1) = 0 ∧
          q.fanCell (k + 3) = 1 ∧
          q.fanCell k = 1 ∧
          q.fanCell (k + 4) = 0 ∧
          r.fanCell (k + 1) = 1 ∧
          r.fanCell k = 2
      | .vz =>
          p.fanCell (k + 3) = 1 ∧
          p.fanCell k = 0 ∧
          p.fanCell (k + 4) = 0 ∧
          q.fanCell k = 1 ∧
          q.fanCell (k + 1) = 0 ∧
          r.fanCell (k + 1) = 1 ∧
          r.fanCell k = 2
    let kindDec (k : Fin 5) (inner : Equiv.Perm (Fin 3)) :
        DecidablePred (packet k inner) :=
      fun kind => by
        cases kind <;> dsimp [packet] <;> infer_instance
    let innerDec (k : Fin 5) : DecidablePred
        (fun inner : Equiv.Perm (Fin 3) =>
          ∃ kind : HullFive111RouteKind, packet k inner kind) :=
      fun inner => by
        letI := kindDec k inner
        exact Fintype.decidableExistsFintype
    let anchorDec : DecidablePred
        (fun k : Fin 5 =>
          ∃ inner : Equiv.Perm (Fin 3),
            ∃ kind : HullFive111RouteKind, packet k inner kind) :=
      fun k => by
        letI := innerDec k
        exact Fintype.decidableExistsFintype
    letI : Decidable
        (∃ k : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
          ∃ kind : HullFive111RouteKind, packet k inner kind) := by
      letI := anchorDec
      exact Fintype.decidableExistsFintype
    change Decidable
      ((∀ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).Is111) →
        ∃ k : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
          ∃ kind : HullFive111RouteKind, packet k inner kind)
    infer_instance
  letI := decidableForallHullFiveRegionTriple _ fixedDec
  decide

/-- Once central `300` and right-oriented end-zero `210` have been removed,
each of the five residual middle-zero region triples admits the canonical
`VZ`/middle packet. -/
theorem hullFiveMiddleVZRoute_of_residual :
    ∀ P Q R : HullFivePointRegion,
      ¬ (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsCentral300) →
      ¬ (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsEnd210) →
      (∃ anchor : Fin 5,
        (hullFiveRegionCounts P Q R anchor).IsMiddle210) →
      ∃ k : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
        let region := hullFiveRegionTriple P Q R
        let p := region (inner 0)
        let q := region (inner 1)
        let r := region (inner 2)
        p.fanCell (k + 3) = 1 ∧
        p.fanCell k = 0 ∧
        p.fanCell (k + 4) = 0 ∧
        q.fanCell k = 1 ∧
        q.fanCell (k + 1) = 0 ∧
        r.fanCell (k + 1) = 1 ∧
        r.fanCell k = 2 := by
  let fixedDec (P Q R : HullFivePointRegion) : Decidable
      (¬ (∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsCentral300) →
        ¬ (∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsEnd210) →
        (∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsMiddle210) →
        ∃ k : Fin 5, ∃ inner : Equiv.Perm (Fin 3),
          let region := hullFiveRegionTriple P Q R
          let p := region (inner 0)
          let q := region (inner 1)
          let r := region (inner 2)
          p.fanCell (k + 3) = 1 ∧
          p.fanCell k = 0 ∧
          p.fanCell (k + 4) = 0 ∧
          q.fanCell k = 1 ∧
          q.fanCell (k + 1) = 0 ∧
          r.fanCell (k + 1) = 1 ∧
          r.fanCell k = 2) := by
    letI := centralExistsDecidable P Q R
    letI := endExistsDecidable P Q R
    letI := middleExistsDecidable P Q R
    let packet (k : Fin 5) (inner : Equiv.Perm (Fin 3)) : Prop :=
      let region := hullFiveRegionTriple P Q R
      let p := region (inner 0)
      let q := region (inner 1)
      let r := region (inner 2)
      p.fanCell (k + 3) = 1 ∧
      p.fanCell k = 0 ∧
      p.fanCell (k + 4) = 0 ∧
      q.fanCell k = 1 ∧
      q.fanCell (k + 1) = 0 ∧
      r.fanCell (k + 1) = 1 ∧
      r.fanCell k = 2
    let innerDec (k : Fin 5) : DecidablePred (packet k) :=
      fun inner => by
        dsimp [packet]
        infer_instance
    let anchorDec : DecidablePred
        (fun k : Fin 5 =>
          ∃ inner : Equiv.Perm (Fin 3), packet k inner) :=
      fun k => by
        letI := innerDec k
        exact Fintype.decidableExistsFintype
    letI : Decidable
        (∃ k : Fin 5, ∃ inner : Equiv.Perm (Fin 3), packet k inner) := by
      letI := anchorDec
      exact Fintype.decidableExistsFintype
    change Decidable
      (¬ (∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsCentral300) →
        ¬ (∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsEnd210) →
        (∃ anchor : Fin 5,
          (hullFiveRegionCounts P Q R anchor).IsMiddle210) →
        ∃ k : Fin 5, ∃ inner : Equiv.Perm (Fin 3), packet k inner)
    infer_instance
  letI := decidableForallHullFiveRegionTriple _ fixedDec
  decide

#print axioms hullFiveCentralRoute_of_counts
#print axioms hullFiveEndRoute_of_counts
#print axioms hullFiveEndRoute_with_rightResidual
#print axioms hullFive111Route_of_counts
#print axioms hullFiveMiddleVZRoute_of_residual

end Heilbronn8.TriHull
