import Heilbronn8.Cover
import Heilbronn8.HullDispatch
import Heilbronn8.PolyVolumeGen
import Heilbronn8.TriHull.HullFive111Geometry
import Heilbronn8.TriHull.HullFive111CompactScalar

/-!
# Reusable geometry packets for hull-five `1 + 1 + 1`

The cyclic hull chart is `A-B-X-C-D`.  A relabelling `e` uses the canonical
slots `A=0`, `B=1`, `C=2`, `D=3`, `X=4`, `P=5`, `Q=6`, `R=7`.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Heilbronn8.TriHull

/-- Canonical cycle order `A-B-X-C-D` inside the relabelling slots. -/
def hullFive111CycleSlot : Fin 5 → Fin 8 := ![0, 1, 4, 2, 3]

private lemma hullFive111_fanSum_finFive
    (v : Configuration) (c : Fin 5 → Fin 8) :
    fanSum v c =
      sig (v (c 0)) (v (c 1)) (v (c 2)) +
      sig (v (c 0)) (v (c 2)) (v (c 3)) +
      sig (v (c 0)) (v (c 3)) (v (c 4)) := by
  have hfp : fanPairs 5 =
      {((1 : Fin 5), (2 : Fin 5)), (2, 3), (3, 4)} := by decide
  rw [fanSum, hfp]
  simp [add_assoc]

/-- Positive orientations for the seven hull triangles in the cyclic chart
`A-B-X-C-D`. -/
structure HullFive111PositiveChart
    (v : Configuration) (e : Fin 8 → Fin 8) : Prop where
  abc_pos : 0 < sig (v (e 0)) (v (e 1)) (v (e 2))
  abx_pos : 0 < sig (v (e 0)) (v (e 1)) (v (e 4))
  axc_pos : 0 < sig (v (e 0)) (v (e 4)) (v (e 2))
  bxc_pos : 0 < sig (v (e 1)) (v (e 4)) (v (e 2))
  abd_pos : 0 < sig (v (e 0)) (v (e 1)) (v (e 3))
  bcd_pos : 0 < sig (v (e 1)) (v (e 2)) (v (e 3))
  cda_pos : 0 < sig (v (e 2)) (v (e 3)) (v (e 0))

/-- Membership data for the canonical `VZ` packet. -/
structure HullFive111VZPacket
    (v : Configuration) (e : Fin 8 → Fin 8)
    extends HullFive111PositiveChart v e : Prop where
  p_in_abc : InTriStrict (v (e 5)) (v (e 0)) (v (e 1)) (v (e 2))
  p_in_abx : InTriStrict (v (e 5)) (v (e 0)) (v (e 1)) (v (e 4))
  p_in_abd : InTriStrict (v (e 5)) (v (e 0)) (v (e 1)) (v (e 3))
  q_in_axc : InTriStrict (v (e 6)) (v (e 0)) (v (e 4)) (v (e 2))
  q_in_bxc : InTriStrict (v (e 6)) (v (e 1)) (v (e 4)) (v (e 2))
  r_in_bcd : InTriStrict (v (e 7)) (v (e 1)) (v (e 2)) (v (e 3))
  r_in_cda : InTriStrict (v (e 7)) (v (e 2)) (v (e 3)) (v (e 0))

/-- Membership data for the canonical `UZ` packet. -/
structure HullFive111UZPacket
    (v : Configuration) (e : Fin 8 → Fin 8)
    extends HullFive111PositiveChart v e : Prop where
  p_in_abx : InTriStrict (v (e 5)) (v (e 0)) (v (e 1)) (v (e 4))
  p_in_bxc : InTriStrict (v (e 5)) (v (e 1)) (v (e 4)) (v (e 2))
  q_in_abc : InTriStrict (v (e 6)) (v (e 0)) (v (e 1)) (v (e 2))
  q_in_axc : InTriStrict (v (e 6)) (v (e 0)) (v (e 4)) (v (e 2))
  q_in_abd : InTriStrict (v (e 6)) (v (e 0)) (v (e 1)) (v (e 3))
  r_in_bcd : InTriStrict (v (e 7)) (v (e 1)) (v (e 2)) (v (e 3))
  r_in_cda : InTriStrict (v (e 7)) (v (e 2)) (v (e 3)) (v (e 0))

private lemma one_le_normalized_sig_of_pos
    (v : Configuration) (e : Fin 8 → Fin 8)
    (he : Function.Injective e) (hm : 0 < minTri v)
    {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpos : 0 < sig (v (e i)) (v (e j)) (v (e k))) :
    1 ≤ sig (v (e i)) (v (e j)) (v (e k)) / minTri v := by
  have hmin := minTri_le_abs_sig_of_pairwise_ne v
    (a := e i) (b := e j) (c := e k)
    (fun h => hij (he h)) (fun h => hik (he h)) (fun h => hjk (he h))
  rw [abs_of_pos hpos] at hmin
  apply (le_div_iff₀ hm).2
  simpa using hmin

private lemma three_le_normalized_sig_of_mem
    (v : Configuration) (e : Fin 8 → Fin 8)
    (he : Function.Injective e) (hm : 0 < minTri v)
    {p a b c : Fin 8}
    (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpos : 0 < sig (v (e a)) (v (e b)) (v (e c)))
    (hmem : InTriStrict (v (e p)) (v (e a)) (v (e b)) (v (e c))) :
    3 ≤ sig (v (e a)) (v (e b)) (v (e c)) / minTri v := by
  obtain ⟨hpbc, hpca, hpab⟩ := inTriStrict_fan_pos hpos hmem
  have h1 := one_le_normalized_sig_of_pos v e he hm hpb hpc hbc hpbc
  have h2 := one_le_normalized_sig_of_pos v e he hm hpc hpa hac.symm hpca
  have h3 := one_le_normalized_sig_of_pos v e he hm hpa hpb hab hpab
  have hsum :
      sig (v (e p)) (v (e b)) (v (e c)) / minTri v +
          sig (v (e p)) (v (e c)) (v (e a)) / minTri v +
          sig (v (e p)) (v (e a)) (v (e b)) / minTri v =
        sig (v (e a)) (v (e b)) (v (e c)) / minTri v := by
    field_simp [ne_of_gt hm]
    exact fan_sum (v (e p)) (v (e a)) (v (e b)) (v (e c))
  linarith

/-- An arbitrary injective relabelling of the `VZ` membership packet forces
the strict normalized hull-area bound. -/
theorem hullFive111_vz_packet_forces_hull_bound
    (v : Configuration) (e : Fin 8 → Fin 8)
    (he : Function.Injective e) (hm : 0 < minTri v)
    (hcell : HullFive111VZPacket v e) :
    minTri v * 25 < 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 1)) (v (e 4)) (v (e 2)) +
        sig (v (e 2)) (v (e 3)) (v (e 0))) := by
  let n : Fin 8 → Fin 8 → Fin 8 → ℝ :=
    fun i j k => sig (v (e i)) (v (e j)) (v (e k)) / minTri v
  let T : ℝ := n 0 1 2
  let U : ℝ := n 0 1 4
  let V : ℝ := n 0 4 2
  let E : ℝ := n 1 4 2
  let W : ℝ := n 0 1 3
  let Z : ℝ := n 1 2 3
  let F : ℝ := n 2 3 0

  have hT : 3 ≤ T := by
    simpa only [T, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 5) (a := 0) (b := 1) (c := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.abc_pos hcell.p_in_abc
  have hU : 3 ≤ U := by
    simpa only [U, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 5) (a := 0) (b := 1) (c := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.abx_pos hcell.p_in_abx
  have hV : 3 ≤ V := by
    simpa only [V, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 6) (a := 0) (b := 4) (c := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.axc_pos hcell.q_in_axc
  have hE : 3 ≤ E := by
    simpa only [E, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 6) (a := 1) (b := 4) (c := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.bxc_pos hcell.q_in_bxc
  have hW : 3 ≤ W := by
    simpa only [W, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 5) (a := 0) (b := 1) (c := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.abd_pos hcell.p_in_abd
  have hZ : 3 ≤ Z := by
    simpa only [Z, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 7) (a := 1) (b := 2) (c := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.bcd_pos hcell.r_in_bcd
  have hF : 3 ≤ F := by
    simpa only [F, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 7) (a := 2) (b := 3) (c := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.cda_pos hcell.r_in_cda

  have right_sum : U + V = T + E := by
    dsimp [U, V, T, E, n]
    field_simp [ne_of_gt hm]
    exact hullFive111_right_sum
      (v (e 0)) (v (e 1)) (v (e 4)) (v (e 2))
  have left_sum : W + Z = T + F := by
    dsimp [W, Z, T, F, n]
    field_simp [ne_of_gt hm]
    exact hullFive111_left_sum
      (v (e 0)) (v (e 1)) (v (e 2)) (v (e 3))

  obtain ⟨hQXC, hQCA, hQAX⟩ :=
    inTriStrict_fan_pos hcell.axc_pos hcell.q_in_axc
  obtain ⟨_, hQCB, _⟩ :=
    inTriStrict_fan_pos hcell.bxc_pos hcell.q_in_bxc
  let aR : ℝ := n 6 4 2
  let bR : ℝ := n 6 0 4
  let cR : ℝ := n 6 2 0
  let qR : ℝ := n 6 2 1
  have haR : 1 ≤ aR := by
    simpa only [aR, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 6) (j := 4) (k := 2)
      (by decide) (by decide) (by decide) hQXC
  have hbR : 1 ≤ bR := by
    simpa only [bR, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 6) (j := 0) (k := 4)
      (by decide) (by decide) (by decide) hQAX
  have hqR : 1 ≤ qR := by
    simpa only [qR, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 6) (j := 2) (k := 1)
      (by decide) (by decide) (by decide) hQCB
  have hfanR : aR + bR + cR = V := by
    dsimp [aR, bR, cR, V, n]
    field_simp [ne_of_gt hm]
    simpa [add_comm, add_left_comm, add_assoc] using
      fan_sum (v (e 6)) (v (e 0)) (v (e 4)) (v (e 2))
  have hcrossR : V * qR = cR * E - aR * T := by
    dsimp [V, qR, cR, E, aR, T, n]
    field_simp [ne_of_gt hm]
    exact hullFive111_ear_v_identity
      (v (e 0)) (v (e 1)) (v (e 4)) (v (e 2)) (v (e 6))
  have rightEar : T + 2 ≤ (V - 2) * (E - 1) :=
    hullFive111_ear (le_trans (by norm_num) hT)
      (le_trans (by norm_num) hV) (le_trans (by norm_num) hE)
      haR hbR hqR hfanR hcrossR

  obtain ⟨hRCD, hRDB, hRBC⟩ :=
    inTriStrict_fan_pos hcell.bcd_pos hcell.r_in_bcd
  obtain ⟨_, hRAC, _⟩ :=
    inTriStrict_fan_pos hcell.cda_pos hcell.r_in_cda
  let aL : ℝ := n 7 2 3
  let bL : ℝ := n 7 3 1
  let cL : ℝ := n 7 1 2
  let qL : ℝ := n 7 0 2
  have haL : 1 ≤ aL := by
    simpa only [aL, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 7) (j := 2) (k := 3)
      (by decide) (by decide) (by decide) hRCD
  have hbL : 1 ≤ bL := by
    simpa only [bL, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 7) (j := 3) (k := 1)
      (by decide) (by decide) (by decide) hRDB
  have hqL : 1 ≤ qL := by
    simpa only [qL, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 7) (j := 0) (k := 2)
      (by decide) (by decide) (by decide) hRAC
  have hfanL : aL + bL + cL = Z := by
    dsimp [aL, bL, cL, Z, n]
    field_simp [ne_of_gt hm]
    exact fan_sum (v (e 7)) (v (e 1)) (v (e 2)) (v (e 3))
  have hcrossL : Z * qL = cL * F - aL * T := by
    dsimp [Z, qL, cL, F, aL, T, n]
    field_simp [ne_of_gt hm]
    simp only [sig]
    ring
  have leftEar : T + 2 ≤ (Z - 2) * (F - 1) :=
    hullFive111_ear (le_trans (by norm_num) hT)
      (le_trans (by norm_num) hZ) (le_trans (by norm_num) hF)
      haL hbL hqL hfanL hcrossL

  obtain ⟨hPBC, hPCA, hPAB⟩ :=
    inTriStrict_fan_pos hcell.abc_pos hcell.p_in_abc
  obtain ⟨_, hPXA, _⟩ :=
    inTriStrict_fan_pos hcell.abx_pos hcell.p_in_abx
  obtain ⟨hPBD, _, _⟩ :=
    inTriStrict_fan_pos hcell.abd_pos hcell.p_in_abd
  let xx : ℝ := n 5 1 2
  let yy : ℝ := n 5 2 0
  let zz : ℝ := n 5 0 1
  let qq : ℝ := n 5 4 0
  let rr : ℝ := n 5 1 3
  have hqq : 1 ≤ qq := by
    simpa only [qq, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 5) (j := 4) (k := 0)
      (by decide) (by decide) (by decide) hPXA
  have hrr : 1 ≤ rr := by
    simpa only [rr, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 5) (j := 1) (k := 3)
      (by decide) (by decide) (by decide) hPBD
  have hzz : 1 ≤ zz := by
    simpa only [zz, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 5) (j := 0) (k := 1)
      (by decide) (by decide) (by decide) hPAB
  have hfanC : xx + yy + zz = T := by
    dsimp [xx, yy, zz, T, n]
    field_simp [ne_of_gt hm]
    exact fan_sum (v (e 5)) (v (e 0)) (v (e 1)) (v (e 2))
  have hpxa : T * qq = yy * U - zz * V := by
    dsimp [T, qq, yy, U, zz, V, n]
    field_simp [ne_of_gt hm]
    exact hullFive111_central_u_identity
      (v (e 0)) (v (e 1)) (v (e 4)) (v (e 2)) (v (e 5))
  have hpbd : T * rr = xx * W - zz * Z := by
    dsimp [T, rr, xx, W, zz, Z, n]
    field_simp [ne_of_gt hm]
    exact hullFive111_central_w_identity
      (v (e 0)) (v (e 1)) (v (e 2)) (v (e 3)) (v (e 5))
  have central : W * (T + V) + U * (2 * T + F) ≤ T * U * W :=
    hullFive111_vz_central (le_trans (by norm_num) hT)
      (le_trans (by norm_num) hU) (le_trans (by norm_num) hV)
      (le_trans (by norm_num) hW) (le_trans (by norm_num) hZ)
      hfanC left_sum hqq hrr hzz hpxa hpbd

  have hnorm : (25 : ℝ) / 2 < T + E + F :=
    hullFive111_vz_hull_sum_gt hT hU hV hE hW hZ hF
      right_sum left_sum rightEar leftEar central
  have hsum :
      T + E + F =
        (sig (v (e 0)) (v (e 1)) (v (e 2)) +
          sig (v (e 1)) (v (e 4)) (v (e 2)) +
          sig (v (e 2)) (v (e 3)) (v (e 0))) / minTri v := by
    dsimp [T, E, F, n]
    ring
  rw [hsum] at hnorm
  have hmul := (lt_div_iff₀ hm).1 hnorm
  nlinarith

/-- An arbitrary injective relabelling of the `UZ` membership packet forces
the strict normalized hull-area bound. -/
theorem hullFive111_uz_packet_forces_hull_bound
    (v : Configuration) (e : Fin 8 → Fin 8)
    (he : Function.Injective e) (hm : 0 < minTri v)
    (hcell : HullFive111UZPacket v e) :
    minTri v * 25 < 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 1)) (v (e 4)) (v (e 2)) +
        sig (v (e 2)) (v (e 3)) (v (e 0))) := by
  let n : Fin 8 → Fin 8 → Fin 8 → ℝ :=
    fun i j k => sig (v (e i)) (v (e j)) (v (e k)) / minTri v
  let T : ℝ := n 0 1 2
  let U : ℝ := n 0 1 4
  let V : ℝ := n 0 4 2
  let E : ℝ := n 1 4 2
  let W : ℝ := n 0 1 3
  let Z : ℝ := n 1 2 3
  let F : ℝ := n 2 3 0

  have hT : 3 ≤ T := by
    simpa only [T, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 6) (a := 0) (b := 1) (c := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.abc_pos hcell.q_in_abc
  have hU : 3 ≤ U := by
    simpa only [U, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 5) (a := 0) (b := 1) (c := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.abx_pos hcell.p_in_abx
  have hV : 3 ≤ V := by
    simpa only [V, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 6) (a := 0) (b := 4) (c := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.axc_pos hcell.q_in_axc
  have hE : 3 ≤ E := by
    simpa only [E, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 5) (a := 1) (b := 4) (c := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.bxc_pos hcell.p_in_bxc
  have hW : 3 ≤ W := by
    simpa only [W, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 6) (a := 0) (b := 1) (c := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.abd_pos hcell.q_in_abd
  have hZ : 3 ≤ Z := by
    simpa only [Z, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 7) (a := 1) (b := 2) (c := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.bcd_pos hcell.r_in_bcd
  have hF : 3 ≤ F := by
    simpa only [F, n] using three_le_normalized_sig_of_mem v e he hm
      (p := 7) (a := 2) (b := 3) (c := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hcell.cda_pos hcell.r_in_cda

  have right_sum : U + V = T + E := by
    dsimp [U, V, T, E, n]
    field_simp [ne_of_gt hm]
    exact hullFive111_right_sum
      (v (e 0)) (v (e 1)) (v (e 4)) (v (e 2))
  have left_sum : W + Z = T + F := by
    dsimp [W, Z, T, F, n]
    field_simp [ne_of_gt hm]
    exact hullFive111_left_sum
      (v (e 0)) (v (e 1)) (v (e 2)) (v (e 3))

  obtain ⟨hPBX, hPXA, hPAB⟩ :=
    inTriStrict_fan_pos hcell.abx_pos hcell.p_in_abx
  obtain ⟨_, hPCB, _⟩ :=
    inTriStrict_fan_pos hcell.bxc_pos hcell.p_in_bxc
  let aR : ℝ := n 5 1 4
  let bR : ℝ := n 5 4 0
  let cR : ℝ := n 5 0 1
  let qR : ℝ := n 5 2 1
  have haR : 1 ≤ aR := by
    simpa only [aR, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 5) (j := 1) (k := 4)
      (by decide) (by decide) (by decide) hPBX
  have hbR : 1 ≤ bR := by
    simpa only [bR, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 5) (j := 4) (k := 0)
      (by decide) (by decide) (by decide) hPXA
  have hqR : 1 ≤ qR := by
    simpa only [qR, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 5) (j := 2) (k := 1)
      (by decide) (by decide) (by decide) hPCB
  have hfanR : aR + bR + cR = U := by
    dsimp [aR, bR, cR, U, n]
    field_simp [ne_of_gt hm]
    exact fan_sum (v (e 5)) (v (e 0)) (v (e 1)) (v (e 4))
  have hcrossR : U * qR = cR * E - aR * T := by
    dsimp [U, qR, cR, E, aR, T, n]
    field_simp [ne_of_gt hm]
    exact hullFive111_ear_u_identity
      (v (e 0)) (v (e 1)) (v (e 4)) (v (e 2)) (v (e 5))
  have rightEar : T + 2 ≤ (U - 2) * (E - 1) :=
    hullFive111_ear (le_trans (by norm_num) hT)
      (le_trans (by norm_num) hU) (le_trans (by norm_num) hE)
      haR hbR hqR hfanR hcrossR

  obtain ⟨hRCD, hRDB, hRBC⟩ :=
    inTriStrict_fan_pos hcell.bcd_pos hcell.r_in_bcd
  obtain ⟨_, hRAC, _⟩ :=
    inTriStrict_fan_pos hcell.cda_pos hcell.r_in_cda
  let aL : ℝ := n 7 2 3
  let bL : ℝ := n 7 3 1
  let cL : ℝ := n 7 1 2
  let qL : ℝ := n 7 0 2
  have haL : 1 ≤ aL := by
    simpa only [aL, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 7) (j := 2) (k := 3)
      (by decide) (by decide) (by decide) hRCD
  have hbL : 1 ≤ bL := by
    simpa only [bL, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 7) (j := 3) (k := 1)
      (by decide) (by decide) (by decide) hRDB
  have hqL : 1 ≤ qL := by
    simpa only [qL, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 7) (j := 0) (k := 2)
      (by decide) (by decide) (by decide) hRAC
  have hfanL : aL + bL + cL = Z := by
    dsimp [aL, bL, cL, Z, n]
    field_simp [ne_of_gt hm]
    exact fan_sum (v (e 7)) (v (e 1)) (v (e 2)) (v (e 3))
  have hcrossL : Z * qL = cL * F - aL * T := by
    dsimp [Z, qL, cL, F, aL, T, n]
    field_simp [ne_of_gt hm]
    simp only [sig]
    ring
  have leftEar : T + 2 ≤ (Z - 2) * (F - 1) :=
    hullFive111_ear (le_trans (by norm_num) hT)
      (le_trans (by norm_num) hZ) (le_trans (by norm_num) hF)
      haL hbL hqL hfanL hcrossL

  obtain ⟨hQBC, hQCA, hQAB⟩ :=
    inTriStrict_fan_pos hcell.abc_pos hcell.q_in_abc
  obtain ⟨_, _, hQAX⟩ :=
    inTriStrict_fan_pos hcell.axc_pos hcell.q_in_axc
  obtain ⟨hQBD, _, _⟩ :=
    inTriStrict_fan_pos hcell.abd_pos hcell.q_in_abd
  let xx : ℝ := n 6 1 2
  let yy : ℝ := n 6 2 0
  let zz : ℝ := n 6 0 1
  let aa : ℝ := n 6 0 4
  let bb : ℝ := n 6 1 3
  have hyy : 1 ≤ yy := by
    simpa only [yy, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 6) (j := 2) (k := 0)
      (by decide) (by decide) (by decide) hQCA
  have haa : 1 ≤ aa := by
    simpa only [aa, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 6) (j := 0) (k := 4)
      (by decide) (by decide) (by decide) hQAX
  have hbb : 1 ≤ bb := by
    simpa only [bb, n] using one_le_normalized_sig_of_pos v e he hm
      (i := 6) (j := 1) (k := 3)
      (by decide) (by decide) (by decide) hQBD
  have hfanC : xx + yy + zz = T := by
    dsimp [xx, yy, zz, T, n]
    field_simp [ne_of_gt hm]
    exact fan_sum (v (e 6)) (v (e 0)) (v (e 1)) (v (e 2))
  have hqax : T * aa = V * zz - U * yy := by
    dsimp [T, aa, V, zz, U, yy, n]
    field_simp [ne_of_gt hm]
    simp only [sig]
    ring
  have hqbd : T * bb = W * xx - Z * zz := by
    dsimp [T, bb, W, xx, Z, zz, n]
    field_simp [ne_of_gt hm]
    simpa [mul_comm] using hullFive111_central_w_identity
      (v (e 0)) (v (e 1)) (v (e 2)) (v (e 3)) (v (e 6))
  have central :
      V * W + W * (T + U) + T * V + Z * (T + U) ≤ T * V * W :=
    hullFive111_uz_central (le_trans (by norm_num) hT)
      (le_trans (by norm_num) hU) (le_trans (by norm_num) hV)
      (le_trans (by norm_num) hW) (le_trans (by norm_num) hZ)
      hfanC hyy haa hbb hqax hqbd

  have hnorm : (25 : ℝ) / 2 < T + E + F :=
    hullFive111_uz_hull_sum_gt hT hU hV hE hW hZ hF
      right_sum left_sum rightEar leftEar central
  have hsum :
      T + E + F =
        (sig (v (e 0)) (v (e 1)) (v (e 2)) +
          sig (v (e 1)) (v (e 4)) (v (e 2)) +
          sig (v (e 2)) (v (e 3)) (v (e 0))) / minTri v := by
    dsimp [T, E, F, n]
    ring
  rw [hsum] at hnorm
  have hmul := (lt_div_iff₀ hm).1 hnorm
  nlinarith

/-- A packet aligned with a genuine five-cycle contradicts a strict beat at
`v8`.  This is the geometry endpoint consumed by the hull-five semantic
classifier. -/
theorem hullFive111_packet_not_beats_of_hullCycle
    {v : Configuration} {S : StrictSignData v} {d : HullCycleData}
    (hcycle : HullCycleOf S d) (h5 : d.cycle.length = 5)
    (e : Fin 8 → Fin 8) (he : Function.Injective e)
    (hchart : ∀ i : Fin 5,
      e (hullFive111CycleSlot i) = d.castGet h5 i)
    (hpacket : HullFive111UZPacket v e ∨ HullFive111VZPacket v e) :
    ¬ Beats doubledHullArea v8 v := by
  intro hbeat
  have hm : 0 < minTri v :=
    (mul_pos v8_pos hbeat.1).trans hbeat.2
  have hbound : minTri v * 25 < 2 *
      (sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 1)) (v (e 4)) (v (e 2)) +
        sig (v (e 2)) (v (e 3)) (v (e 0))) := by
    rcases hpacket with huz | hvz
    · exact hullFive111_uz_packet_forces_hull_bound v e he hm huz
    · exact hullFive111_vz_packet_forces_hull_bound v e he hm hvz
  have hcertified : doubledHullArea v = d.fanExpr v :=
    doubledHullArea_eq_of_isHullArea hcycle.isHullArea
  have hcast : fanSum v (d.castGet h5) = d.fanExpr v :=
    HullCycleData.fanSum_castGet d h5
  have hcycleArea : doubledHullArea v = fanSum v (d.castGet h5) :=
    hcertified.trans hcast.symm
  have hfun :
      (fun i : Fin 5 => e (hullFive111CycleSlot i)) = d.castGet h5 :=
    funext hchart
  have hfan :
      fanSum v (fun i : Fin 5 => e (hullFive111CycleSlot i)) =
        sig (v (e 0)) (v (e 1)) (v (e 4)) +
        sig (v (e 0)) (v (e 4)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) := by
    rw [hullFive111_fanSum_finFive]
    simp [hullFive111CycleSlot]
  have harea : doubledHullArea v =
      sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 1)) (v (e 4)) (v (e 2)) +
        sig (v (e 2)) (v (e 3)) (v (e 0)) := by
    calc
      doubledHullArea v = fanSum v (d.castGet h5) := hcycleArea
      _ = fanSum v (fun i : Fin 5 => e (hullFive111CycleSlot i)) := by
        rw [hfun]
      _ = sig (v (e 0)) (v (e 1)) (v (e 4)) +
          sig (v (e 0)) (v (e 4)) (v (e 2)) +
          sig (v (e 0)) (v (e 2)) (v (e 3)) := hfan
      _ = sig (v (e 0)) (v (e 1)) (v (e 2)) +
          sig (v (e 1)) (v (e 4)) (v (e 2)) +
          sig (v (e 2)) (v (e 3)) (v (e 0)) := by
        have hright := hullFive111_right_sum
          (v (e 0)) (v (e 1)) (v (e 4)) (v (e 2))
        have hrotate :
            sig (v (e 0)) (v (e 2)) (v (e 3)) =
              sig (v (e 2)) (v (e 3)) (v (e 0)) := by
          exact sig_rotate (v (e 0)) (v (e 2)) (v (e 3))
        linarith
  have hq : (2 / 25 : ℝ) < v8 := by
    exact lt_trans (by norm_num) v8_lb
  have hcut : (2 / 25 : ℝ) * doubledHullArea v < minTri v :=
    lt_trans (mul_lt_mul_of_pos_right hq hbeat.1) hbeat.2
  rw [harea] at hcut
  nlinarith

end Heilbronn8.TriHull
