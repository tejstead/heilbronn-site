import Heilbronn8.Cover
import Heilbronn8.TriHull.Core
import Heilbronn8.TriHull.HullFive300SameSectorScalar

/-!
# Geometry adapter for the hull-five same-sector chart

The local labels in the central theorem are

`W,U,V,P,Q,R = e 0,e 1,e 2,e 3,e 4,e 5`.

Both `Q` and `R` lie strictly in `PUV`.  The proof normalizes every doubled
area by `2 / minTri v`, dispatches all six strict orders of their three local
barycentric ratios to the two scalar charts, and obtains the raw central
bound `21`.  The hull wrapper handles all three cyclic fan sectors and adds
the two raw ear floors.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.TriHull

private lemma two_le_or_le_neg {t : ℝ} (h : 2 ≤ |t|) :
    2 ≤ t ∨ t ≤ -2 := by
  by_cases ht : 0 ≤ t
  · left
    simpa [abs_of_nonneg ht] using h
  · right
    have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht'] at h
    linarith

private lemma two_le_scaledSig_of_pos_sameSector
    (v : Fin 8 → ℝ × ℝ) (hm : 0 < minTri v)
    {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpos : 0 < sig (v i) (v j) (v k)) :
    2 ≤ (2 / minTri v) * sig (v i) (v j) (v k) := by
  have hmin := minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
  rw [abs_of_pos hpos] at hmin
  have hscale : 0 < (2 / minTri v) := div_pos (by norm_num) hm
  have hscaleMin : (2 / minTri v) * minTri v = 2 := by
    field_simp [ne_of_gt hm]
  calc
    2 = (2 / minTri v) * minTri v := hscaleMin.symm
    _ ≤ (2 / minTri v) * sig (v i) (v j) (v k) :=
      mul_le_mul_of_nonneg_left hmin hscale.le

private lemma two_le_abs_scaledSig_sameSector
    (v : Fin 8 → ℝ × ℝ) (hm : 0 < minTri v)
    {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    2 ≤ |(2 / minTri v) * sig (v i) (v j) (v k)| := by
  have hmin := minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
  have hscale : 0 < (2 / minTri v) := div_pos (by norm_num) hm
  have hscaleMin : (2 / minTri v) * minTri v = 2 := by
    field_simp [ne_of_gt hm]
  calc
    2 = (2 / minTri v) * minTri v := hscaleMin.symm
    _ ≤ (2 / minTri v) * |sig (v i) (v j) (v k)| :=
      mul_le_mul_of_nonneg_left hmin hscale.le
    _ = |(2 / minTri v) * sig (v i) (v j) (v k)| := by
      rw [abs_mul, abs_of_pos hscale]

private lemma inTriStrict_rotate_sameSector {P A B C : ℝ × ℝ}
    (h : InTriStrict P A B C) : InTriStrict P B C A := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, rfl⟩ := h
  exact ⟨y, z, x, hy, hz, hx, by linarith, by module⟩

/-!
The following dispatcher is the division-free form of the six ratio orders.
The signed minors are

`dP = [PQR]`, `dU = [UQR]`, and `dV = [VQR]`.

The two impossible sign triples are excluded by the alternating relation
`x*dV + y*dU + z*dP = 0`.  The other six are sent to one of the two scalar
charts by swapping `Q,R`, algebraically swapping the local rays `U,V`, or
both.  No geometric orientation is changed by that algebraic symmetry.
-/
private theorem sameSector_allOrders
    {L M N x y z X Y Z dP dU dV : ℝ}
    (hL : 2 ≤ L) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z)
    (hX0 : 2 ≤ X) (hY0 : 2 ≤ Y) (hZ0 : 2 ≤ Z)
    (hsumQ : x + y + z = L) (hsumR : X + Y + Z = L)
    (hcrossQ : 2 * L ≤ |N * y - M * x|)
    (hcrossR : 2 * L ≤ |N * Y - M * X|)
    (hdPAbs : 2 ≤ |dP|) (hdUAbs : 2 ≤ |dU|)
    (hdVAbs : 2 ≤ |dV|)
    (hX : X = x + dP - dU)
    (hY : Y = y + dV - dP)
    (hZ : Z = z + dU - dV)
    (hcycleQ : x * dV + y * dU + z * dP = 0) :
    21 ≤ L + M + N := by
  have hcycleR : X * dV + Y * dU + Z * dP = 0 := by
    rw [hX, hY, hZ]
    nlinarith [hcycleQ]
  have hcrossQrev : 2 * L ≤ |M * x - N * y| := by
    calc
      2 * L ≤ |N * y - M * x| := hcrossQ
      _ = |M * x - N * y| := abs_sub_comm _ _
  have hcrossRrev : 2 * L ≤ |M * X - N * Y| := by
    calc
      2 * L ≤ |N * Y - M * X| := hcrossR
      _ = |M * X - N * Y| := abs_sub_comm _ _

  rcases two_le_or_le_neg hdPAbs with hp | hp
  · rcases two_le_or_le_neg hdUAbs with hu | hu
    · rcases two_le_or_le_neg hdVAbs with hv | hv
      · -- `+++` is an impossible directed ratio cycle.
        have hxdV : 0 < x * dV := mul_pos (by linarith) (by linarith)
        have hydU : 0 < y * dU := mul_pos (by linarith) (by linarith)
        have hzdP : 0 < z * dP := mul_pos (by linarith) (by linarith)
        nlinarith [hcycleQ]
      · -- `++-`: swap `Q,R`, then algebraically swap `U,V` (order one).
        have hscalar := hullFive300_sameSectorScalar_orderOne
          (L := L) (M := N) (N := M)
          (x := Y) (y := X) (z := Z)
          (X := y) (Y := x) (Z := z)
          (a := dP) (b := -dV) (c := dU)
          hL hN hM hY0 hX0 hZ0 hy hx hz
          (by linarith) (by linarith) (by linarith)
          (by nlinarith [hsumR]) (by nlinarith [hsumQ])
          (by nlinarith [hY]) (by nlinarith [hX]) (by nlinarith [hZ])
          (by nlinarith [hcycleR]) hcrossRrev hcrossQrev
        nlinarith
    · rcases two_le_or_le_neg hdVAbs with hv | hv
      · -- `+-+`: the first chart without a symmetry.
        exact hullFive300_sameSectorScalar_orderOne
          (L := L) (M := M) (N := N)
          (x := x) (y := y) (z := z)
          (X := X) (Y := Y) (Z := Z)
          (a := dP) (b := -dU) (c := dV)
          hL hM hN hx hy hz hX0 hY0 hZ0
          (by linarith) (by linarith) (by linarith)
          hsumQ hsumR
          (by nlinarith [hX]) (by nlinarith [hY]) (by nlinarith [hZ])
          (by nlinarith [hcycleQ]) hcrossQ hcrossR
      · -- `+--`: the second chart without a symmetry.
        exact hullFive300_sameSectorScalar_orderTwo
          (L := L) (M := M) (N := N)
          (x := x) (y := y) (z := z)
          (X := X) (Y := Y) (Z := Z)
          (a := -dU) (b := dP) (c := -dV)
          hL hM hN hx hy hz hX0 hY0 hZ0
          (by linarith) (by linarith) (by linarith)
          hsumQ hsumR
          (by nlinarith [hX]) (by nlinarith [hZ]) (by nlinarith [hY])
          (by nlinarith [hcycleQ]) hcrossQ hcrossR
  · rcases two_le_or_le_neg hdUAbs with hu | hu
    · rcases two_le_or_le_neg hdVAbs with hv | hv
      · -- `-++`: swap `Q,R` (order two).
        exact hullFive300_sameSectorScalar_orderTwo
          (L := L) (M := M) (N := N)
          (x := X) (y := Y) (z := Z)
          (X := x) (Y := y) (Z := z)
          (a := dU) (b := -dP) (c := dV)
          hL hM hN hX0 hY0 hZ0 hx hy hz
          (by linarith) (by linarith) (by linarith)
          hsumR hsumQ
          (by nlinarith [hX]) (by nlinarith [hZ]) (by nlinarith [hY])
          (by nlinarith [hcycleR]) hcrossR hcrossQ
      · -- `-+-`: swap `Q,R` (order one).
        exact hullFive300_sameSectorScalar_orderOne
          (L := L) (M := M) (N := N)
          (x := X) (y := Y) (z := Z)
          (X := x) (Y := y) (Z := z)
          (a := -dP) (b := dU) (c := -dV)
          hL hM hN hX0 hY0 hZ0 hx hy hz
          (by linarith) (by linarith) (by linarith)
          hsumR hsumQ
          (by nlinarith [hX]) (by nlinarith [hY]) (by nlinarith [hZ])
          (by nlinarith [hcycleR]) hcrossR hcrossQ
    · rcases two_le_or_le_neg hdVAbs with hv | hv
      · -- `--+`: algebraically swap the two local rays (order one).
        have hscalar := hullFive300_sameSectorScalar_orderOne
          (L := L) (M := N) (N := M)
          (x := y) (y := x) (z := z)
          (X := Y) (Y := X) (Z := Z)
          (a := -dP) (b := dV) (c := -dU)
          hL hN hM hy hx hz hY0 hX0 hZ0
          (by linarith) (by linarith) (by linarith)
          (by nlinarith [hsumQ]) (by nlinarith [hsumR])
          (by nlinarith [hY]) (by nlinarith [hX]) (by nlinarith [hZ])
          (by nlinarith [hcycleQ]) hcrossQrev hcrossRrev
        nlinarith
      · -- `---` is the reverse impossible directed ratio cycle.
        have hxdV : x * dV < 0 :=
          mul_neg_of_pos_of_neg (by linarith) (by linarith)
        have hydU : y * dU < 0 :=
          mul_neg_of_pos_of_neg (by linarith) (by linarith)
        have hzdP : z * dP < 0 :=
          mul_neg_of_pos_of_neg (by linarith) (by linarith)
        nlinarith [hcycleQ]

/--
Anchor-generic central same-sector adapter.  The injective embedding `e` has
roles `W,U,V,P,Q,R`.  Thus callers may choose any of the three interior
points as anchor and any cyclic central fan sector without relabelling the
ambient configuration or changing `minTri`.
-/
theorem hullFive300_sameSector_central_bound
    (v : Fin 8 → ℝ × ℝ) (e : Fin 6 → Fin 8)
    (he : Function.Injective e) (hm : 0 < minTri v)
    (hWUV : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 3)) (v (e 1)) (v (e 2))) :
    21 ≤ (2 / minTri v) * sig (v (e 0)) (v (e 1)) (v (e 2)) := by
  let scale : ℝ := 2 / minTri v
  let n : Fin 6 → Fin 6 → Fin 6 → ℝ :=
    fun i j k ↦ scale * sig (v (e i)) (v (e j)) (v (e k))

  let L : ℝ := n 3 1 2
  let M : ℝ := n 3 2 0
  let N : ℝ := n 3 0 1
  let x : ℝ := n 3 1 4
  let y : ℝ := n 3 4 2
  let z : ℝ := n 4 1 2
  let X : ℝ := n 3 1 5
  let Y : ℝ := n 3 5 2
  let Z : ℝ := n 5 1 2
  let qW : ℝ := n 3 4 0
  let rW : ℝ := n 3 5 0
  let dP : ℝ := n 3 4 5
  let dU : ℝ := n 1 4 5
  let dV : ℝ := n 2 4 5

  have hfloor (i j k : Fin 6)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hpos : 0 < sig (v (e i)) (v (e j)) (v (e k))) :
      2 ≤ n i j k := by
    simpa only [n, scale] using
      two_le_scaledSig_of_pos_sameSector v hm
        (he.ne hij) (he.ne hik) (he.ne hjk) hpos
  have habsFloor (i j k : Fin 6)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      2 ≤ |n i j k| := by
    simpa only [n, scale] using
      two_le_abs_scaledSig_sameSector v hm
        (he.ne hij) (he.ne hik) (he.ne hjk)

  obtain ⟨hLPos, hMPos, hNPos⟩ := inTriStrict_fan_pos hWUV hP
  obtain ⟨hzPos, hyRotPos, hxRotPos⟩ :=
    inTriStrict_fan_pos hLPos hQ
  have hxPos : 0 < sig (v (e 3)) (v (e 1)) (v (e 4)) := by
    rwa [sig_rotate (v (e 4)) (v (e 3)) (v (e 1))] at hxRotPos
  have hyPos : 0 < sig (v (e 3)) (v (e 4)) (v (e 2)) := by
    rw [sig_rotate (v (e 4)) (v (e 2)) (v (e 3)),
      sig_rotate (v (e 2)) (v (e 3)) (v (e 4))] at hyRotPos
    exact hyRotPos
  obtain ⟨hZPos, hYRotPos, hXRotPos⟩ :=
    inTriStrict_fan_pos hLPos hR
  have hXPos : 0 < sig (v (e 3)) (v (e 1)) (v (e 5)) := by
    rwa [sig_rotate (v (e 5)) (v (e 3)) (v (e 1))] at hXRotPos
  have hYPos : 0 < sig (v (e 3)) (v (e 5)) (v (e 2)) := by
    rw [sig_rotate (v (e 5)) (v (e 2)) (v (e 3)),
      sig_rotate (v (e 2)) (v (e 3)) (v (e 5))] at hYRotPos
    exact hYRotPos

  have hL : 2 ≤ L := hfloor 3 1 2 (by decide) (by decide) (by decide) hLPos
  have hM : 2 ≤ M := hfloor 3 2 0 (by decide) (by decide) (by decide) hMPos
  have hN : 2 ≤ N := hfloor 3 0 1 (by decide) (by decide) (by decide) hNPos
  have hx : 2 ≤ x := hfloor 3 1 4 (by decide) (by decide) (by decide) hxPos
  have hy : 2 ≤ y := hfloor 3 4 2 (by decide) (by decide) (by decide) hyPos
  have hz : 2 ≤ z := hfloor 4 1 2 (by decide) (by decide) (by decide) hzPos
  have hX0 : 2 ≤ X := hfloor 3 1 5 (by decide) (by decide) (by decide) hXPos
  have hY0 : 2 ≤ Y := hfloor 3 5 2 (by decide) (by decide) (by decide) hYPos
  have hZ0 : 2 ≤ Z := hfloor 5 1 2 (by decide) (by decide) (by decide) hZPos
  have hqWAbs : 2 ≤ |qW| :=
    habsFloor 3 4 0 (by decide) (by decide) (by decide)
  have hrWAbs : 2 ≤ |rW| :=
    habsFloor 3 5 0 (by decide) (by decide) (by decide)
  have hdPAbs : 2 ≤ |dP| :=
    habsFloor 3 4 5 (by decide) (by decide) (by decide)
  have hdUAbs : 2 ≤ |dU| :=
    habsFloor 1 4 5 (by decide) (by decide) (by decide)
  have hdVAbs : 2 ≤ |dV| :=
    habsFloor 2 4 5 (by decide) (by decide) (by decide)

  have hsumQ : x + y + z = L := by
    dsimp [x, y, z, L, n, scale]
    simp only [sig]
    ring
  have hsumR : X + Y + Z = L := by
    dsimp [X, Y, Z, L, n, scale]
    simp only [sig]
    ring
  have hX : X = x + dP - dU := by
    dsimp [X, x, dP, dU, n, scale]
    simp only [sig]
    ring
  have hY : Y = y + dV - dP := by
    dsimp [Y, y, dV, dP, n, scale]
    simp only [sig]
    ring
  have hZ : Z = z + dU - dV := by
    dsimp [Z, z, dU, dV, n, scale]
    simp only [sig]
    ring
  have hcycleQ : x * dV + y * dU + z * dP = 0 := by
    dsimp [x, y, z, dP, dU, dV, n, scale]
    simp only [sig]
    ring
  have hqW : L * qW = M * x - N * y := by
    dsimp [L, qW, M, x, N, y, n, scale]
    simp only [sig]
    ring
  have hrW : L * rW = M * X - N * Y := by
    dsimp [L, rW, M, X, N, Y, n, scale]
    simp only [sig]
    ring

  have hLPos' : 0 < L := by linarith
  have hcrossQ : 2 * L ≤ |N * y - M * x| := by
    have hmul := mul_le_mul_of_nonneg_left hqWAbs hLPos'.le
    have habsId : |N * y - M * x| = L * |qW| := by
      rw [show N * y - M * x = -(L * qW) by nlinarith [hqW],
        abs_neg, abs_mul, abs_of_pos hLPos']
    rw [habsId]
    nlinarith [hmul]
  have hcrossR : 2 * L ≤ |N * Y - M * X| := by
    have hmul := mul_le_mul_of_nonneg_left hrWAbs hLPos'.le
    have habsId : |N * Y - M * X| = L * |rW| := by
      rw [show N * Y - M * X = -(L * rW) by nlinarith [hrW],
        abs_neg, abs_mul, abs_of_pos hLPos']
    rw [habsId]
    nlinarith [hmul]

  have hscalar : 21 ≤ L + M + N :=
    sameSector_allOrders hL hM hN hx hy hz hX0 hY0 hZ0
      hsumQ hsumR hcrossQ hcrossR hdPAbs hdUAbs hdVAbs
      hX hY hZ hcycleQ
  calc
    21 ≤ L + M + N := hscalar
    _ = (2 / minTri v) * sig (v (e 0)) (v (e 1)) (v (e 2)) := by
      dsimp [L, M, N, n, scale]
      simp only [sig]
      ring

/-- Fixed hull-five occupancy data with a repeated fan sector at `P = v 5`.
The disjunction lists the three cyclic sectors `PBC`, `PCA`, and `PAB`. -/
structure HullFive300SameSectorCell (v : Fin 8 → ℝ × ℝ) : Prop where
  abc_pos : 0 < sig (v 0) (v 1) (v 2)
  p_in_abc : InTriStrict (v 5) (v 0) (v 1) (v 2)
  same_sector :
    (InTriStrict (v 6) (v 5) (v 1) (v 2) ∧
      InTriStrict (v 7) (v 5) (v 1) (v 2)) ∨
    (InTriStrict (v 6) (v 5) (v 2) (v 0) ∧
      InTriStrict (v 7) (v 5) (v 2) (v 0)) ∨
    (InTriStrict (v 6) (v 5) (v 0) (v 1) ∧
      InTriStrict (v 7) (v 5) (v 0) (v 1))
  bxc_pos : 0 < sig (v 1) (v 4) (v 2)
  cda_pos : 0 < sig (v 2) (v 3) (v 0)

/-- A repeated sector at the fixed anchor forces the normalized hull fan
bound.  The generic central theorem above supplies the corresponding result
for an arbitrary choice of anchor labels. -/
theorem hullFive300_sameSector_forces_fan_bound
    (v : Fin 8 → ℝ × ℝ) (hm : 0 < minTri v)
    (hcell : HullFive300SameSectorCell v) :
    minTri v * 25 ≤
      2 * (sig (v 5) (v 1) (v 4) +
        sig (v 5) (v 4) (v 2) +
        sig (v 5) (v 2) (v 3) +
        sig (v 5) (v 3) (v 0) +
        sig (v 5) (v 0) (v 1)) := by
  let scale : ℝ := 2 / minTri v
  let T : ℝ := scale * sig (v 0) (v 1) (v 2)
  let E : ℝ := scale * sig (v 1) (v 4) (v 2)
  let F : ℝ := scale * sig (v 2) (v 3) (v 0)
  let H : ℝ := scale *
    (sig (v 5) (v 1) (v 4) +
      sig (v 5) (v 4) (v 2) +
      sig (v 5) (v 2) (v 3) +
      sig (v 5) (v 3) (v 0) +
      sig (v 5) (v 0) (v 1))

  have hT : 21 ≤ T := by
    rcases hcell.same_sector with hPBC | hPCA | hPAB
    · let e : Fin 6 → Fin 8 := ![0, 1, 2, 5, 6, 7]
      have he : Function.Injective e := by decide
      have hWUV_e : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)) := by
        change 0 < sig (v 0) (v 1) (v 2)
        exact hcell.abc_pos
      have hP_e :
          InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)) := by
        change InTriStrict (v 5) (v 0) (v 1) (v 2)
        exact hcell.p_in_abc
      have hQ_e :
          InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)) := by
        change InTriStrict (v 6) (v 5) (v 1) (v 2)
        exact hPBC.1
      have hR_e :
          InTriStrict (v (e 5)) (v (e 3)) (v (e 1)) (v (e 2)) := by
        change InTriStrict (v 7) (v 5) (v 1) (v 2)
        exact hPBC.2
      have hcentral := hullFive300_sameSector_central_bound v e he hm
        hWUV_e hP_e hQ_e hR_e
      change 21 ≤ (2 / minTri v) * sig (v 0) (v 1) (v 2) at hcentral
      simpa only [T, scale] using hcentral
    · let e : Fin 6 → Fin 8 := ![1, 2, 0, 5, 6, 7]
      have he : Function.Injective e := by decide
      have hP' := inTriStrict_rotate_sameSector hcell.p_in_abc
      have hWUV' : 0 < sig (v 1) (v 2) (v 0) := by
        rw [← sig_rotate (v 0) (v 1) (v 2)]
        exact hcell.abc_pos
      have hWUV_e : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)) := by
        change 0 < sig (v 1) (v 2) (v 0)
        exact hWUV'
      have hP_e :
          InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)) := by
        change InTriStrict (v 5) (v 1) (v 2) (v 0)
        exact hP'
      have hQ_e :
          InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)) := by
        change InTriStrict (v 6) (v 5) (v 2) (v 0)
        exact hPCA.1
      have hR_e :
          InTriStrict (v (e 5)) (v (e 3)) (v (e 1)) (v (e 2)) := by
        change InTriStrict (v 7) (v 5) (v 2) (v 0)
        exact hPCA.2
      have hcentral := hullFive300_sameSector_central_bound v e he hm
        hWUV_e hP_e hQ_e hR_e
      have hcentral' :
          21 ≤ (2 / minTri v) * sig (v 1) (v 2) (v 0) := by
        change 21 ≤ (2 / minTri v) * sig (v 1) (v 2) (v 0) at hcentral
        exact hcentral
      rw [← sig_rotate (v 0) (v 1) (v 2)] at hcentral'
      simpa only [T, scale] using hcentral'
    · let e : Fin 6 → Fin 8 := ![2, 0, 1, 5, 6, 7]
      have he : Function.Injective e := by decide
      have hP' := inTriStrict_rotate_sameSector
        (inTriStrict_rotate_sameSector hcell.p_in_abc)
      have hWUV' : 0 < sig (v 2) (v 0) (v 1) := by
        rw [sig_rotate (v 2) (v 0) (v 1)]
        exact hcell.abc_pos
      have hWUV_e : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)) := by
        change 0 < sig (v 2) (v 0) (v 1)
        exact hWUV'
      have hP_e :
          InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)) := by
        change InTriStrict (v 5) (v 2) (v 0) (v 1)
        exact hP'
      have hQ_e :
          InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)) := by
        change InTriStrict (v 6) (v 5) (v 0) (v 1)
        exact hPAB.1
      have hR_e :
          InTriStrict (v (e 5)) (v (e 3)) (v (e 1)) (v (e 2)) := by
        change InTriStrict (v 7) (v 5) (v 0) (v 1)
        exact hPAB.2
      have hcentral := hullFive300_sameSector_central_bound v e he hm
        hWUV_e hP_e hQ_e hR_e
      have hcentral' :
          21 ≤ (2 / minTri v) * sig (v 2) (v 0) (v 1) := by
        change 21 ≤ (2 / minTri v) * sig (v 2) (v 0) (v 1) at hcentral
        exact hcentral
      rw [sig_rotate (v 2) (v 0) (v 1)] at hcentral'
      simpa only [T, scale] using hcentral'

  have hE : 2 ≤ E := by
    simpa only [E, scale] using
      two_le_scaledSig_of_pos_sameSector v hm
        (by decide) (by decide) (by decide) hcell.bxc_pos
  have hF : 2 ≤ F := by
    simpa only [F, scale] using
      two_le_scaledSig_of_pos_sameSector v hm
        (by decide) (by decide) (by decide) hcell.cda_pos
  have hH : H = T + E + F := by
    dsimp [H, T, E, F]
    simp only [sig]
    ring
  have hscalar : 25 ≤ H := by nlinarith
  have hminScale : minTri v * scale = 2 := by
    dsimp [scale]
    field_simp [ne_of_gt hm]
  calc
    minTri v * 25 ≤ minTri v * H :=
      mul_le_mul_of_nonneg_left hscalar hm.le
    _ = 2 * (sig (v 5) (v 1) (v 4) +
        sig (v 5) (v 4) (v 2) +
        sig (v 5) (v 2) (v 3) +
        sig (v 5) (v 3) (v 0) +
        sig (v 5) (v 0) (v 1)) := by
      dsimp [H]
      rw [← mul_assoc, hminScale]

end Heilbronn8.TriHull
