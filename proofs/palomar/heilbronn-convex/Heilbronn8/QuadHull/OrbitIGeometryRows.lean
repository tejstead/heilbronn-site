import Heilbronn8.QuadHull.Bridge

-- The large cyclic witness constructor performs exact nonlinear normalization
-- across all eighteen rows.  Give elaboration a deterministic local budget.
set_option maxHeartbeats 1000000

namespace Heilbronn8.QuadHull

/-!
# Exact cyclic-row geometry for orbit I

This module is deliberately independent of the generated stratum corpus and
is not imported by a shared aggregate.  It is a source-only draft: the
identities below have been checked algebraically, but the file has not yet
been elaborated by Lean.

Once `minTri v` is nonzero, the fan sums, primed-row transport, pair gaps,
central determinant, and `CD` rows are polynomial identities.  A finite
sign-word dispatcher therefore only needs to establish the relevant strict
signs and subtriangle memberships.  It should not emit rational equality
certificates for any identity in this file.
-/

/-- A doubled signed area normalized by the doubled minimum triangle area. -/
noncomputable def normalizedSig
    (v : Fin 8 → Point) (i j k : Fin 8) : ℝ :=
  sig (v i) (v j) (v k) / minTri v

/-- A positive semantic determinant with distinct labels has normalized size
at least one. -/
lemma one_le_normalizedSig_of_pos
    (v : Fin 8 → Point) (i j k : Fin 8)
    (hm : 0 < minTri v)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpos : 0 < sig (v i) (v j) (v k)) :
    1 ≤ normalizedSig v i j k := by
  have hmin := minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
  rw [abs_of_pos hpos] at hmin
  rw [normalizedSig, le_div_iff₀ hm]
  simpa using hmin

/-- The two three-cell fans cut by `PX`, sharing the cell `PXA`. -/
structure OrbitIRow where
  x : ℝ
  j : ℝ
  y : ℝ
  x' : ℝ
  y' : ℝ

/--
The unprimed row is the fan of `PCA`; the primed row is the fan of `PDA`.
-/
noncomputable def orbitIRow
    (v : Fin 8 → Point) (P C A D X : Fin 8) : OrbitIRow where
  x := normalizedSig v P C X
  j := normalizedSig v P X A
  y := normalizedSig v X C A
  x' := normalizedSig v P D X
  y' := normalizedSig v X D A

/-! ## Minimal finite data for a cyclic leaf -/

/-- Compact lookup for a containing triangle and its one interior witness.
The explicit match keeps the finite label proof independent of vector
notation. -/
@[simp] def orbitIOnePointLabels
    (i j k q : Fin 8) : Fin 4 → Fin 8 :=
  fun n ↦
    match n.val with
    | 0 => i
    | 1 => j
    | 2 => k
    | _ => q

/--
A single geometric witness for a normalized triangle to be at least `3`.
The target triangle's positive orientation is supplied by the common orbit-I
placement; injectivity and strict containment are the only finite data needed
by the one-point triangle theorem.
-/
structure OrbitIOnePointWitness
    (v : Fin 8 → Point) (i j k : Fin 8) where
  q : Fin 8
  labels_injective : Function.Injective (orbitIOnePointLabels i j k q)
  q_in_triangle : TriHull.InTriStrict (v q) (v i) (v j) (v k)

lemma OrbitIOnePointWitness.three_le
    {v : Fin 8 → Point} {i j k : Fin 8}
    (h : OrbitIOnePointWitness v i j k)
    (hm : 0 < minTri v)
    (hpos : 0 < sig (v i) (v j) (v k)) :
    3 ≤ normalizedSig v i j k := by
  obtain ⟨h1, h2, h3⟩ :=
    TriHull.inTriStrict_fan_pos hpos h.q_in_triangle
  have hne : ∀ {a b : Fin 4}, a ≠ b →
      orbitIOnePointLabels i j k h.q a ≠
        orbitIOnePointLabels i j k h.q b := by
    intro a b hab heq
    exact hab (h.labels_injective heq)
  have hu1 : 1 ≤ normalizedSig v h.q j k :=
    one_le_normalizedSig_of_pos v h.q j k hm
      (by simpa using hne (show (3 : Fin 4) ≠ 1 by decide))
      (by simpa using hne (show (3 : Fin 4) ≠ 2 by decide))
      (by simpa using hne (show (1 : Fin 4) ≠ 2 by decide)) h1
  have hu2 : 1 ≤ normalizedSig v h.q k i :=
    one_le_normalizedSig_of_pos v h.q k i hm
      (by simpa using hne (show (3 : Fin 4) ≠ 2 by decide))
      (by simpa using hne (show (3 : Fin 4) ≠ 0 by decide))
      (by simpa using hne (show (2 : Fin 4) ≠ 0 by decide)) h2
  have hu3 : 1 ≤ normalizedSig v h.q i j :=
    one_le_normalizedSig_of_pos v h.q i j hm
      (by simpa using hne (show (3 : Fin 4) ≠ 0 by decide))
      (by simpa using hne (show (3 : Fin 4) ≠ 1 by decide))
      (by simpa using hne (show (0 : Fin 4) ≠ 1 by decide)) h3
  have hfan :
      normalizedSig v h.q j k + normalizedSig v h.q k i +
          normalizedSig v h.q i j = normalizedSig v i j k := by
    dsimp [normalizedSig]
    field_simp [hm.ne']
    simp only [sig]
    ring
  linarith

/--
Exactly the ten one-point witnesses needed for the `3`-lower fields of
`CyclicLeaf`.  Its remaining five row fields only need the universal unit
bound and hence no containment witness.
-/
structure OrbitICyclicLowerWitnesses
    (v : Fin 8 → Point) (P C A D S T R : Fin 8) where
  Sx : OrbitIOnePointWitness v P C S
  Sy : OrbitIOnePointWitness v S C A
  Sx' : OrbitIOnePointWitness v P D S
  Sy' : OrbitIOnePointWitness v S D A
  Tj : OrbitIOnePointWitness v P T A
  Ty : OrbitIOnePointWitness v T C A
  Ty' : OrbitIOnePointWitness v T D A
  Rx : OrbitIOnePointWitness v P C R
  Rj : OrbitIOnePointWitness v P R A
  Rx' : OrbitIOnePointWitness v P D R

/--
The nine strict orientations not supplied by the row identities.  The first
eight yield all twelve pair gaps, with the `A` and `P` signs reused by both
fans.  The last yields the central determinant.  The three `CDX` signs are
not stored: they follow barycentrically from `X ∈ DAB` and a CCW hull.
-/
structure OrbitICyclicOrientationWitnesses
    (v : Fin 8 → Point) (P C A D S T R : Fin 8) : Prop where
  CST_pos : 0 < sig (v C) (v S) (v T)
  AST_pos : 0 < sig (v A) (v S) (v T)
  DST_pos : 0 < sig (v D) (v S) (v T)
  CRS_pos : 0 < sig (v C) (v R) (v S)
  PRS_pos : 0 < sig (v P) (v R) (v S)
  DRS_pos : 0 < sig (v D) (v R) (v S)
  ATR_pos : 0 < sig (v A) (v T) (v R)
  PTR_pos : 0 < sig (v P) (v T) (v R)
  STR_pos : 0 < sig (v S) (v T) (v R)

/-- Compact label lookup for the seven labels used by a cyclic row.  The
explicit match avoids the large dependent terms produced by vector notation. -/
@[simp] def orbitICyclicLabels
    (P C A D S T R : Fin 8) : Fin 7 → Fin 8 :=
  fun i ↦
    match i.val with
    | 0 => P
    | 1 => C
    | 2 => A
    | 3 => D
    | 4 => S
    | 5 => T
    | _ => R

/-- Slots of the common eight-label orbit-I packet used by
`orbitICyclicLabels`: `P,C,A,D,S,T,R`. -/
@[simp] def orbitICyclicSlots : Fin 7 → Fin 8 :=
  fun i ↦
    match i.val with
    | 0 => 4
    | 1 => 2
    | 2 => 0
    | 3 => 3
    | 4 => 5
    | 5 => 6
    | _ => 7

lemma orbitICyclicSlots_injective : Function.Injective orbitICyclicSlots := by
  decide

/-- `CDX` is positive for every point strictly inside the CCW triangle
`DAB`; the cyclic leaf therefore need not store three separate `CD` signs. -/
lemma orbitI_CD_pos_of_in_DAB
    {v : Fin 8 → Point} {A B C D X : Fin 8}
    (hccw : CCWQuad (v A) (v B) (v C) (v D))
    (hX : TriHull.InTriStrict (v X) (v D) (v A) (v B)) :
    0 < sig (v C) (v D) (v X) := by
  obtain ⟨dx, ax, bx, hdx, hax, hbx, hsum, hXeq⟩ := hX
  have hACD : 0 < sig (v A) (v C) (v D) := by
    calc
      0 < sig (v C) (v D) (v A) := hccw.2.2.1
      _ = sig (v A) (v C) (v D) := by
        simp only [sig]
        ring
  have hXCD : 0 < sig (v X) (v C) (v D) := by
    rw [hXeq,
      sig_affine_fst (v D) (v A) (v B) (v C) (v D)
        dx ax bx hsum]
    simp only [sig_eq13, mul_zero, zero_add]
    exact add_pos (mul_pos hax hACD) (mul_pos hbx hccw.2.1)
  calc
    0 < sig (v X) (v C) (v D) := hXCD
    _ = sig (v C) (v D) (v X) := sig_rotate _ _ _

lemma orbitIRow_sum
    (v : Fin 8 → Point) (P C A D X : Fin 8)
    (hm : minTri v ≠ 0) :
    let r := orbitIRow v P C A D X
    r.x + r.j + r.y = normalizedSig v P C A := by
  dsimp [orbitIRow, normalizedSig]
  field_simp [hm]
  simp only [sig]
  ring

lemma orbitIRow_prime_sum
    (v : Fin 8 → Point) (P C A D X : Fin 8)
    (hm : minTri v ≠ 0) :
    let r := orbitIRow v P C A D X
    r.x' + r.j + r.y' = normalizedSig v P D A := by
  dsimp [orbitIRow, normalizedSig]
  field_simp [hm]
  simp only [sig]
  ring

/-- Identity (47), already cleared into the `cyclicXNum` convention. -/
lemma orbitIRow_xnum
    (v : Fin 8 → Point) (P C A D X : Fin 8)
    (hm : minTri v ≠ 0) :
    let r := orbitIRow v P C A D X
    cyclicXNum (normalizedSig v P D A) (normalizedSig v P C D)
        r.x r.j =
      normalizedSig v P C A * r.x' := by
  dsimp [orbitIRow, normalizedSig, cyclicXNum]
  field_simp [hm]
  simp only [sig]
  ring

/-- Identity (48), with `cyclicW = normalizedSig A C D`. -/
lemma orbitIRow_ynum
    (v : Fin 8 → Point) (P C A D X : Fin 8)
    (hm : minTri v ≠ 0) :
    let r := orbitIRow v P C A D X
    cyclicYNum (normalizedSig v P C A) (normalizedSig v P D A)
        (normalizedSig v P C D) r.y r.j =
      normalizedSig v P C A * r.y' := by
  dsimp [orbitIRow, normalizedSig, cyclicYNum, cyclicW]
  field_simp [hm]
  simp only [sig]
  ring

/-!
The next identities turn positivity of one semantic determinant into a gap
inequality after the universal `minTri` lower bound is applied.  Reversing
`X` and `Y` supplies the opposite orientation.
-/

lemma orbitIRow_gap_C
    (v : Fin 8 → Point) (P C A D X Y : Fin 8)
    (hm : minTri v ≠ 0) :
    let rX := orbitIRow v P C A D X
    let rY := orbitIRow v P C A D Y
    rY.y * rX.x - rY.x * rX.y =
      normalizedSig v P C A * normalizedSig v C X Y := by
  dsimp [orbitIRow, normalizedSig]
  field_simp [hm]
  simp only [sig]
  ring

lemma orbitIRow_gap_A
    (v : Fin 8 → Point) (P C A D X Y : Fin 8)
    (hm : minTri v ≠ 0) :
    let rX := orbitIRow v P C A D X
    let rY := orbitIRow v P C A D Y
    rY.j * rX.y - rY.y * rX.j =
      normalizedSig v P C A * normalizedSig v A X Y := by
  dsimp [orbitIRow, normalizedSig]
  field_simp [hm]
  simp only [sig]
  ring

lemma orbitIRow_gap_P
    (v : Fin 8 → Point) (P C A D X Y : Fin 8)
    (hm : minTri v ≠ 0) :
    let rX := orbitIRow v P C A D X
    let rY := orbitIRow v P C A D Y
    rY.x * rX.j - rY.j * rX.x =
      normalizedSig v P C A * normalizedSig v P X Y := by
  dsimp [orbitIRow, normalizedSig]
  field_simp [hm]
  simp only [sig]
  ring

lemma orbitIRow_prime_gap_D
    (v : Fin 8 → Point) (P C A D X Y : Fin 8)
    (hm : minTri v ≠ 0) :
    let rX := orbitIRow v P C A D X
    let rY := orbitIRow v P C A D Y
    rY.y' * rX.x' - rY.x' * rX.y' =
      normalizedSig v P D A * normalizedSig v D X Y := by
  dsimp [orbitIRow, normalizedSig]
  field_simp [hm]
  simp only [sig]
  ring

lemma orbitIRow_prime_gap_A
    (v : Fin 8 → Point) (P C A D X Y : Fin 8)
    (hm : minTri v ≠ 0) :
    let rX := orbitIRow v P C A D X
    let rY := orbitIRow v P C A D Y
    rY.j * rX.y' - rY.y' * rX.j =
      normalizedSig v P D A * normalizedSig v A X Y := by
  dsimp [orbitIRow, normalizedSig]
  field_simp [hm]
  simp only [sig]
  ring

lemma orbitIRow_prime_gap_P
    (v : Fin 8 → Point) (P C A D X Y : Fin 8)
    (hm : minTri v ≠ 0) :
    let rX := orbitIRow v P C A D X
    let rY := orbitIRow v P C A D Y
    rY.x' * rX.j - rY.j * rX.x' =
      normalizedSig v P D A * normalizedSig v P X Y := by
  dsimp [orbitIRow, normalizedSig]
  field_simp [hm]
  simp only [sig]
  ring

/-- The three-row determinant is exactly the normalized `STR` area. -/
lemma orbitIRow_central
    (v : Fin 8 → Point) (P C A D S T R : Fin 8)
    (hm : minTri v ≠ 0) :
    let s := orbitIRow v P C A D S
    let t := orbitIRow v P C A D T
    let r := orbitIRow v P C A D R
    (-areaDet s.x s.j s.y t.x t.j t.y r.x r.j r.y =
      normalizedSig v P C A * normalizedSig v P C A *
        normalizedSig v S T R) := by
  dsimp [orbitIRow, normalizedSig, areaDet]
  field_simp [hm]
  simp only [sig]
  ring

/-- A `CD` row is a single normalized triangle area. -/
lemma orbitIRow_CD
    (v : Fin 8 → Point) (P C A D X : Fin 8)
    (hm : minTri v ≠ 0) :
    let r := orbitIRow v P C A D X
    normalizedSig v P C D * r.y + normalizedSig v A C D * r.x =
      normalizedSig v P C A * normalizedSig v C D X := by
  dsimp [orbitIRow, normalizedSig]
  field_simp [hm]
  simp only [sig]
  ring

/-! ## Assembly of the cyclic semantic leaf -/

/--
Assemble the complete analytic `CyclicLeaf` from the finite geometric
witnesses and the exact row identities above.

The four scalar equalities identify the common residual core with the
normalized geometric rows.  The common orbit-I placement supplies positivity
of every row entry, the three `DAB` memberships supply the `CDX` signs, and the
two finite witness packets supply precisely the strengthened lower bounds and
pair orientations not implied by the identities themselves.
-/
noncomputable def cyclicLeaf_of_geometryRows
    {v : Fin 8 → Point} {P C A B D S T R : Fin 8} {H : ℝ}
    (core : OrbitIResidualGeometry H)
    (hm : 0 < minTri v)
    (hlabels : Function.Injective
      (orbitICyclicLabels P C A D S T R))
    (hPCA : 0 < sig (v P) (v C) (v A))
    (hPDA : 0 < sig (v P) (v D) (v A))
    (hS_PCA : TriHull.InTriStrict (v S) (v P) (v C) (v A))
    (hT_PCA : TriHull.InTriStrict (v T) (v P) (v C) (v A))
    (hR_PCA : TriHull.InTriStrict (v R) (v P) (v C) (v A))
    (hS_PDA : TriHull.InTriStrict (v S) (v P) (v D) (v A))
    (hT_PDA : TriHull.InTriStrict (v T) (v P) (v D) (v A))
    (hR_PDA : TriHull.InTriStrict (v R) (v P) (v D) (v A))
    (hccw : CCWQuad (v A) (v B) (v C) (v D))
    (hS_DAB : TriHull.InTriStrict (v S) (v D) (v A) (v B))
    (hT_DAB : TriHull.InTriStrict (v T) (v D) (v A) (v B))
    (hR_DAB : TriHull.InTriStrict (v R) (v D) (v A) (v B))
    (hu : core.u = normalizedSig v P C A)
    (hdelta : core.δ = normalizedSig v P D A)
    (hgamma : core.γ = normalizedSig v P C D)
    (hw : core.w = normalizedSig v A C D)
    (hlower : OrbitICyclicLowerWitnesses v P C A D S T R)
    (horient : OrbitICyclicOrientationWitnesses v P C A D S T R) :
    CyclicLeaf H := by
  let s := orbitIRow v P C A D S
  let t := orbitIRow v P C A D T
  let r := orbitIRow v P C A D R
  obtain ⟨hSy, hSjRaw, hSxRaw⟩ :=
    TriHull.inTriStrict_fan_pos hPCA hS_PCA
  obtain ⟨hTy, hTjRaw, hTxRaw⟩ :=
    TriHull.inTriStrict_fan_pos hPCA hT_PCA
  obtain ⟨hRy, hRjRaw, hRxRaw⟩ :=
    TriHull.inTriStrict_fan_pos hPCA hR_PCA
  obtain ⟨hSy', hSjRaw', hSxRaw'⟩ :=
    TriHull.inTriStrict_fan_pos hPDA hS_PDA
  obtain ⟨hTy', hTjRaw', hTxRaw'⟩ :=
    TriHull.inTriStrict_fan_pos hPDA hT_PDA
  obtain ⟨hRy', hRjRaw', hRxRaw'⟩ :=
    TriHull.inTriStrict_fan_pos hPDA hR_PDA
  have hSj : 0 < sig (v P) (v S) (v A) := by
    simpa only [sig_rotate (v S) (v A) (v P),
      sig_rotate (v A) (v P) (v S)] using hSjRaw
  have hTj : 0 < sig (v P) (v T) (v A) := by
    simpa only [sig_rotate (v T) (v A) (v P),
      sig_rotate (v A) (v P) (v T)] using hTjRaw
  have hRj : 0 < sig (v P) (v R) (v A) := by
    simpa only [sig_rotate (v R) (v A) (v P),
      sig_rotate (v A) (v P) (v R)] using hRjRaw
  have hSx : 0 < sig (v P) (v C) (v S) := by
    simpa only [sig_rotate (v S) (v P) (v C)] using hSxRaw
  have hTx : 0 < sig (v P) (v C) (v T) := by
    simpa only [sig_rotate (v T) (v P) (v C)] using hTxRaw
  have hRx : 0 < sig (v P) (v C) (v R) := by
    simpa only [sig_rotate (v R) (v P) (v C)] using hRxRaw
  have hSx' : 0 < sig (v P) (v D) (v S) := by
    simpa only [sig_rotate (v S) (v P) (v D)] using hSxRaw'
  have hTx' : 0 < sig (v P) (v D) (v T) := by
    simpa only [sig_rotate (v T) (v P) (v D)] using hTxRaw'
  have hRx' : 0 < sig (v P) (v D) (v R) := by
    simpa only [sig_rotate (v R) (v P) (v D)] using hRxRaw'
  have label_ne (i j : Fin 7) (hij : i ≠ j) :
      orbitICyclicLabels P C A D S T R i ≠
        orbitICyclicLabels P C A D S T R j :=
    hlabels.ne hij
  have unit_of_pos (i j k : Fin 7)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hpos : 0 < sig
        (v (orbitICyclicLabels P C A D S T R i))
        (v (orbitICyclicLabels P C A D S T R j))
        (v (orbitICyclicLabels P C A D S T R k))) :
      1 ≤ normalizedSig v
        (orbitICyclicLabels P C A D S T R i)
        (orbitICyclicLabels P C A D S T R j)
        (orbitICyclicLabels P C A D S T R k) :=
    one_le_normalizedSig_of_pos v _ _ _ hm
      (label_ne i j hij) (label_ne i k hik) (label_ne j k hjk) hpos
  have hUpos : 0 < core.u := by
    rw [hu, normalizedSig]
    exact div_pos hPCA hm
  have hVpos : 0 < core.δ := by
    rw [hdelta, normalizedSig]
    exact div_pos hPDA hm
  have scaleU (z : ℝ) (hz : 1 ≤ z) : core.u ≤ core.u * z := by
    nlinarith [mul_nonneg hUpos.le (sub_nonneg.mpr hz)]
  have scaleV (z : ℝ) (hz : 1 ≤ z) : core.δ ≤ core.δ * z := by
    nlinarith [mul_nonneg hVpos.le (sub_nonneg.mpr hz)]
  have hCST : 1 ≤ normalizedSig v C S T := by
    simpa using unit_of_pos 1 4 5 (by decide) (by decide) (by decide)
      horient.CST_pos
  have hAST : 1 ≤ normalizedSig v A S T := by
    simpa using unit_of_pos 2 4 5 (by decide) (by decide) (by decide)
      horient.AST_pos
  have hDST : 1 ≤ normalizedSig v D S T := by
    simpa using unit_of_pos 3 4 5 (by decide) (by decide) (by decide)
      horient.DST_pos
  have hCRS : 1 ≤ normalizedSig v C R S := by
    simpa using unit_of_pos 1 6 4 (by decide) (by decide) (by decide)
      horient.CRS_pos
  have hPRS : 1 ≤ normalizedSig v P R S := by
    simpa using unit_of_pos 0 6 4 (by decide) (by decide) (by decide)
      horient.PRS_pos
  have hDRS : 1 ≤ normalizedSig v D R S := by
    simpa using unit_of_pos 3 6 4 (by decide) (by decide) (by decide)
      horient.DRS_pos
  have hATR : 1 ≤ normalizedSig v A T R := by
    simpa using unit_of_pos 2 5 6 (by decide) (by decide) (by decide)
      horient.ATR_pos
  have hPTR : 1 ≤ normalizedSig v P T R := by
    simpa using unit_of_pos 0 5 6 (by decide) (by decide) (by decide)
      horient.PTR_pos
  have hSTR : 1 ≤ normalizedSig v S T R := by
    simpa using unit_of_pos 4 5 6 (by decide) (by decide) (by decide)
      horient.STR_pos
  have hCDSpos : 0 < sig (v C) (v D) (v S) :=
    orbitI_CD_pos_of_in_DAB hccw hS_DAB
  have hCDTpos : 0 < sig (v C) (v D) (v T) :=
    orbitI_CD_pos_of_in_DAB hccw hT_DAB
  have hCDRpos : 0 < sig (v C) (v D) (v R) :=
    orbitI_CD_pos_of_in_DAB hccw hR_DAB
  have hCDS : 1 ≤ normalizedSig v C D S := by
    simpa using unit_of_pos 1 3 4 (by decide) (by decide) (by decide) hCDSpos
  have hCDT : 1 ≤ normalizedSig v C D T := by
    simpa using unit_of_pos 1 3 5 (by decide) (by decide) (by decide) hCDTpos
  have hCDR : 1 ≤ normalizedSig v C D R := by
    simpa using unit_of_pos 1 3 6 (by decide) (by decide) (by decide) hCDRpos
  refine
    { core := core
      Sx := s.x, Sj := s.j, Sy := s.y
      Tx := t.x, Tj := t.j, Ty := t.y
      Rx := r.x, Rj := r.j, Ry := r.y
      Sx' := s.x', Sy' := s.y'
      Tx' := t.x', Ty' := t.y'
      Rx' := r.x', Ry' := r.y'
      S_sum := ?_, T_sum := ?_, R_sum := ?_
      S'_sum := ?_, T'_sum := ?_, R'_sum := ?_
      Sx_num := ?_, Sy_num := ?_, Tx_num := ?_, Ty_num := ?_,
      Rx_num := ?_, Ry_num := ?_
      Sx_lower := hlower.Sx.three_le hm hSx
      Sj_lower := by
        simpa [s, orbitIRow] using
          unit_of_pos 0 4 2 (by decide) (by decide) (by decide) hSj
      Sy_lower := hlower.Sy.three_le hm hSy
      Tx_lower := by
        simpa [t, orbitIRow] using
          unit_of_pos 0 1 5 (by decide) (by decide) (by decide) hTx
      Tj_lower := hlower.Tj.three_le hm hTj
      Ty_lower := hlower.Ty.three_le hm hTy
      Rx_lower := hlower.Rx.three_le hm hRx
      Rj_lower := hlower.Rj.three_le hm hRj
      Ry_lower := by
        simpa [r, orbitIRow] using
          unit_of_pos 6 1 2 (by decide) (by decide) (by decide) hRy
      Sx'_lower := hlower.Sx'.three_le hm hSx'
      Sy'_lower := hlower.Sy'.three_le hm hSy'
      Tx'_lower := by
        simpa [t, orbitIRow] using
          unit_of_pos 0 3 5 (by decide) (by decide) (by decide) hTx'
      Ty'_lower := hlower.Ty'.three_le hm hTy'
      Rx'_lower := hlower.Rx'.three_le hm hRx'
      Ry'_lower := by
        simpa [r, orbitIRow] using
          unit_of_pos 6 3 2 (by decide) (by decide) (by decide) hRy'
      C_ST_XY := ?_, C_ST_YJ := ?_, C_SR_YX := ?_, C_SR_XJ := ?_,
      C_TR_YJ := ?_, C_TR_JX := ?_
      D_ST_XY := ?_, D_ST_YJ := ?_, D_SR_YX := ?_, D_SR_XJ := ?_,
      D_TR_YJ := ?_, D_TR_JX := ?_
      central := ?_, CDS := ?_, CDT := ?_, CDR := ?_ }
  · calc
      core.u = normalizedSig v P C A := hu
      _ = s.x + s.j + s.y :=
        (orbitIRow_sum v P C A D S hm.ne').symm
  · calc
      core.u = normalizedSig v P C A := hu
      _ = t.x + t.j + t.y :=
        (orbitIRow_sum v P C A D T hm.ne').symm
  · calc
      core.u = normalizedSig v P C A := hu
      _ = r.x + r.j + r.y :=
        (orbitIRow_sum v P C A D R hm.ne').symm
  · calc
      core.δ = normalizedSig v P D A := hdelta
      _ = s.x' + s.j + s.y' :=
        (orbitIRow_prime_sum v P C A D S hm.ne').symm
  · calc
      core.δ = normalizedSig v P D A := hdelta
      _ = t.x' + t.j + t.y' :=
        (orbitIRow_prime_sum v P C A D T hm.ne').symm
  · calc
      core.δ = normalizedSig v P D A := hdelta
      _ = r.x' + r.j + r.y' :=
        (orbitIRow_prime_sum v P C A D R hm.ne').symm
  · calc
      cyclicXNum core.δ core.γ s.x s.j =
          cyclicXNum (normalizedSig v P D A) (normalizedSig v P C D)
            s.x s.j := by rw [hdelta, hgamma]
      _ = normalizedSig v P C A * s.x' :=
        orbitIRow_xnum v P C A D S hm.ne'
      _ = core.u * s.x' := by rw [hu]
  · calc
      cyclicYNum core.u core.δ core.γ s.y s.j =
          cyclicYNum (normalizedSig v P C A) (normalizedSig v P D A)
            (normalizedSig v P C D) s.y s.j := by rw [hu, hdelta, hgamma]
      _ = normalizedSig v P C A * s.y' :=
        orbitIRow_ynum v P C A D S hm.ne'
      _ = core.u * s.y' := by rw [hu]
  · calc
      cyclicXNum core.δ core.γ t.x t.j =
          cyclicXNum (normalizedSig v P D A) (normalizedSig v P C D)
            t.x t.j := by rw [hdelta, hgamma]
      _ = normalizedSig v P C A * t.x' :=
        orbitIRow_xnum v P C A D T hm.ne'
      _ = core.u * t.x' := by rw [hu]
  · calc
      cyclicYNum core.u core.δ core.γ t.y t.j =
          cyclicYNum (normalizedSig v P C A) (normalizedSig v P D A)
            (normalizedSig v P C D) t.y t.j := by rw [hu, hdelta, hgamma]
      _ = normalizedSig v P C A * t.y' :=
        orbitIRow_ynum v P C A D T hm.ne'
      _ = core.u * t.y' := by rw [hu]
  · calc
      cyclicXNum core.δ core.γ r.x r.j =
          cyclicXNum (normalizedSig v P D A) (normalizedSig v P C D)
            r.x r.j := by rw [hdelta, hgamma]
      _ = normalizedSig v P C A * r.x' :=
        orbitIRow_xnum v P C A D R hm.ne'
      _ = core.u * r.x' := by rw [hu]
  · calc
      cyclicYNum core.u core.δ core.γ r.y r.j =
          cyclicYNum (normalizedSig v P C A) (normalizedSig v P D A)
            (normalizedSig v P C D) r.y r.j := by rw [hu, hdelta, hgamma]
      _ = normalizedSig v P C A * r.y' :=
        orbitIRow_ynum v P C A D R hm.ne'
      _ = core.u * r.y' := by rw [hu]
  · calc
      core.u ≤ core.u * normalizedSig v C S T := scaleU _ hCST
      _ = normalizedSig v P C A * normalizedSig v C S T := by rw [hu]
      _ = t.y * s.x - t.x * s.y :=
        (orbitIRow_gap_C v P C A D S T hm.ne').symm
  · calc
      core.u ≤ core.u * normalizedSig v A S T := scaleU _ hAST
      _ = normalizedSig v P C A * normalizedSig v A S T := by rw [hu]
      _ = t.j * s.y - t.y * s.j :=
        (orbitIRow_gap_A v P C A D S T hm.ne').symm
  · calc
      core.u ≤ core.u * normalizedSig v C R S := scaleU _ hCRS
      _ = normalizedSig v P C A * normalizedSig v C R S := by rw [hu]
      _ = s.y * r.x - s.x * r.y :=
        (orbitIRow_gap_C v P C A D R S hm.ne').symm
      _ = r.x * s.y - r.y * s.x := by ring
  · calc
      core.u ≤ core.u * normalizedSig v P R S := scaleU _ hPRS
      _ = normalizedSig v P C A * normalizedSig v P R S := by rw [hu]
      _ = s.x * r.j - s.j * r.x :=
        (orbitIRow_gap_P v P C A D R S hm.ne').symm
      _ = r.j * s.x - r.x * s.j := by ring
  · calc
      core.u ≤ core.u * normalizedSig v A T R := scaleU _ hATR
      _ = normalizedSig v P C A * normalizedSig v A T R := by rw [hu]
      _ = r.j * t.y - r.y * t.j :=
        (orbitIRow_gap_A v P C A D T R hm.ne').symm
  · calc
      core.u ≤ core.u * normalizedSig v P T R := scaleU _ hPTR
      _ = normalizedSig v P C A * normalizedSig v P T R := by rw [hu]
      _ = r.x * t.j - r.j * t.x :=
        (orbitIRow_gap_P v P C A D T R hm.ne').symm
  · calc
      core.δ ≤ core.δ * normalizedSig v D S T := scaleV _ hDST
      _ = normalizedSig v P D A * normalizedSig v D S T := by rw [hdelta]
      _ = t.y' * s.x' - t.x' * s.y' :=
        (orbitIRow_prime_gap_D v P C A D S T hm.ne').symm
  · calc
      core.δ ≤ core.δ * normalizedSig v A S T := scaleV _ hAST
      _ = normalizedSig v P D A * normalizedSig v A S T := by rw [hdelta]
      _ = t.j * s.y' - t.y' * s.j :=
        (orbitIRow_prime_gap_A v P C A D S T hm.ne').symm
  · calc
      core.δ ≤ core.δ * normalizedSig v D R S := scaleV _ hDRS
      _ = normalizedSig v P D A * normalizedSig v D R S := by rw [hdelta]
      _ = s.y' * r.x' - s.x' * r.y' :=
        (orbitIRow_prime_gap_D v P C A D R S hm.ne').symm
      _ = r.x' * s.y' - r.y' * s.x' := by ring
  · calc
      core.δ ≤ core.δ * normalizedSig v P R S := scaleV _ hPRS
      _ = normalizedSig v P D A * normalizedSig v P R S := by rw [hdelta]
      _ = s.x' * r.j - s.j * r.x' :=
        (orbitIRow_prime_gap_P v P C A D R S hm.ne').symm
      _ = r.j * s.x' - r.x' * s.j := by ring
  · calc
      core.δ ≤ core.δ * normalizedSig v A T R := scaleV _ hATR
      _ = normalizedSig v P D A * normalizedSig v A T R := by rw [hdelta]
      _ = r.j * t.y' - r.y' * t.j :=
        (orbitIRow_prime_gap_A v P C A D T R hm.ne').symm
  · calc
      core.δ ≤ core.δ * normalizedSig v P T R := scaleV _ hPTR
      _ = normalizedSig v P D A * normalizedSig v P T R := by rw [hdelta]
      _ = r.x' * t.j - r.j * t.x' :=
        (orbitIRow_prime_gap_P v P C A D T R hm.ne').symm
  · calc
      core.u ^ 2 ≤ core.u ^ 2 * normalizedSig v S T R := by
        nlinarith [mul_nonneg (sq_nonneg core.u) (sub_nonneg.mpr hSTR)]
      _ = normalizedSig v P C A * normalizedSig v P C A *
          normalizedSig v S T R := by rw [hu]; ring
      _ = -areaDet s.x s.j s.y t.x t.j t.y r.x r.j r.y :=
        (orbitIRow_central v P C A D S T R hm.ne').symm
  · calc
      core.u ≤ core.u * normalizedSig v C D S := scaleU _ hCDS
      _ = normalizedSig v P C A * normalizedSig v C D S := by rw [hu]
      _ = normalizedSig v P C D * s.y + normalizedSig v A C D * s.x :=
        (orbitIRow_CD v P C A D S hm.ne').symm
      _ = core.γ * s.y + core.w * s.x := by rw [hgamma, hw]
  · calc
      core.u ≤ core.u * normalizedSig v C D T := scaleU _ hCDT
      _ = normalizedSig v P C A * normalizedSig v C D T := by rw [hu]
      _ = normalizedSig v P C D * t.y + normalizedSig v A C D * t.x :=
        (orbitIRow_CD v P C A D T hm.ne').symm
      _ = core.γ * t.y + core.w * t.x := by rw [hgamma, hw]
  · calc
      core.u ≤ core.u * normalizedSig v C D R := scaleU _ hCDR
      _ = normalizedSig v P C A * normalizedSig v C D R := by rw [hu]
      _ = normalizedSig v P C D * r.y + normalizedSig v A C D * r.x :=
        (orbitIRow_CD v P C A D R hm.ne').symm
      _ = core.γ * r.y + core.w * r.x := by rw [hgamma, hw]

/--
The smallest existing seam into `OrbitCertificate`: once a geometric
dispatcher has produced a `CyclicLeaf`, the analytic residual theorem is
already available through `Bridge`.
-/
theorem orbitCertificate_of_cyclicLeaf
    {v : Fin 8 → Point} {A B C D : Fin 8} {H : ℝ}
    (hscale : quadHullArea (v A) (v B) (v C) (v D) = minTri v / 2 * H)
    (leaf : CyclicLeaf H) :
    OrbitCertificate v A B C D :=
  Or.inr ⟨H, hscale, .residual (.cyclic leaf)⟩

end Heilbronn8.QuadHull
