import Heilbronn8.CoverGeometry
import Heilbronn8.PolyVolumeGen
import Heilbronn8.Survivors.Join.HullEightOctagonScalar

/-!
# The universal eight-vertex hull bound

This is the geometric adapter for `hullEight_octagon_scalar_of_product`.
It uses one fixed alternating decomposition of a strict convex eight-cycle;
all statements are invariant under the labels carried by that cycle.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Heilbronn8

private lemma minTri_le_pos_sig_of_eightCycle
    (v : Configuration) (c : Fin 8 -> Fin 8)
    (hc : Function.Injective c) {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpos : 0 < sig (v (c i)) (v (c j)) (v (c k))) :
    minTri v <= sig (v (c i)) (v (c j)) (v (c k)) := by
  have h := minTri_le_abs_sig_of_pairwise_ne v
    (hc.ne hij) (hc.ne hik) (hc.ne hjk)
  rwa [abs_of_pos hpos] at h

private lemma fanSum_eight_explicit
    (v : Configuration) (c : Fin 8 -> Fin 8) :
    fanSum v c =
      sig (v (c 0)) (v (c 1)) (v (c 2)) +
      sig (v (c 0)) (v (c 2)) (v (c 3)) +
      sig (v (c 0)) (v (c 3)) (v (c 4)) +
      sig (v (c 0)) (v (c 4)) (v (c 5)) +
      sig (v (c 0)) (v (c 5)) (v (c 6)) +
      sig (v (c 0)) (v (c 6)) (v (c 7)) := by
  have hfp : fanPairs 8 =
      {((1 : Fin 8), (2 : Fin 8)), (2, 3), (3, 4), (4, 5), (5, 6),
        (6, 7)} := by
    decide
  rw [fanSum, hfp]
  simp
  ring

/--
Every strict convex eight-cycle has a consecutive vertex triangle whose
doubled area is at most `2/25` of the doubled fan area.
-/
theorem strictOctagon_twentyFive_minTri_le_two_fanSum
    {v : Configuration} {c : Fin 8 -> Fin 8}
    (hc : Function.Injective c)
    (hcyc : StrictCyclicPos c v) :
    25 * minTri v <= 2 * fanSum v c := by
  let p : Fin 8 -> Real × Real := fun i => v (c i)
  let m : Real := minTri v
  change 25 * m <= 2 * fanSum v c
  by_cases hm : 0 < m
  · have hpos (i j k : Fin 8) (hij : i < j) (hjk : j < k) :
        0 < sig (p i) (p j) (p k) := by
      simpa [p] using hcyc.pos i j k hij hjk
    have hfloor (i j k : Fin 8)
        (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
        (hs : 0 < sig (p i) (p j) (p k)) :
        m <= sig (p i) (p j) (p k) := by
      have hs' : 0 < sig (v (c i)) (v (c j)) (v (c k)) := by
        simpa [p] using hs
      simpa [m, p] using
        (minTri_le_pos_sig_of_eightCycle v c hc hij hik hjk hs')

    -- Central quadrilateral ears, in increasing-index orientations.
    let q0 : Real := sig (p 0) (p 2) (p 6)
    let q1 : Real := sig (p 0) (p 2) (p 4)
    let q2 : Real := sig (p 2) (p 4) (p 6)
    let q3 : Real := sig (p 0) (p 4) (p 6)

    -- The four cap ears and the four intervening original ears.
    let c0 : Real := sig (p 0) (p 1) (p 2)
    let c1 : Real := sig (p 2) (p 3) (p 4)
    let c2 : Real := sig (p 4) (p 5) (p 6)
    let c3 : Real := sig (p 0) (p 6) (p 7)
    let b0 : Real := sig (p 0) (p 1) (p 7)
    let b1 : Real := sig (p 1) (p 2) (p 3)
    let b2 : Real := sig (p 3) (p 4) (p 5)
    let b3 : Real := sig (p 5) (p 6) (p 7)

    -- Auxiliary triangles used in the two Pluecker identities.
    let X0 : Real := sig (p 0) (p 1) (p 6)
    let X1 : Real := sig (p 0) (p 2) (p 3)
    let X2 : Real := sig (p 2) (p 4) (p 5)
    let X3 : Real := sig (p 4) (p 6) (p 7)
    let Z0 : Real := sig (p 0) (p 2) (p 7)
    let Z1 : Real := sig (p 1) (p 2) (p 4)
    let Z2 : Real := sig (p 3) (p 4) (p 6)
    let Z3 : Real := sig (p 0) (p 5) (p 6)

    -- Division-free numerators `q_(i+1) * r_i` from the scalar proof.
    let N0 : Real := q0 * q1 + c0 * (q0 - q3)
    let N1 : Real := q1 * q2 + c1 * (q1 - q0)
    let N2 : Real := q2 * q3 + c2 * (q2 - q1)
    let N3 : Real := q3 * q0 + c3 * (q3 - q2)

    have hq0 : 0 < q0 := by
      simpa [q0] using hpos 0 2 6 (by decide) (by decide)
    have hq1 : 0 < q1 := by
      simpa [q1] using hpos 0 2 4 (by decide) (by decide)
    have hq2 : 0 < q2 := by
      simpa [q2] using hpos 2 4 6 (by decide) (by decide)
    have hq3 : 0 < q3 := by
      simpa [q3] using hpos 0 4 6 (by decide) (by decide)
    have hqsum : q0 + q2 = q1 + q3 := by
      dsimp [q0, q1, q2, q3, p]
      simp only [sig]
      ring

    have hc0 : m <= c0 := by
      simpa [c0] using hfloor 0 1 2 (by decide) (by decide) (by decide)
        (hpos 0 1 2 (by decide) (by decide))
    have hc1 : m <= c1 := by
      simpa [c1] using hfloor 2 3 4 (by decide) (by decide) (by decide)
        (hpos 2 3 4 (by decide) (by decide))
    have hc2 : m <= c2 := by
      simpa [c2] using hfloor 4 5 6 (by decide) (by decide) (by decide)
        (hpos 4 5 6 (by decide) (by decide))
    have hc3 : m <= c3 := by
      simpa [c3] using hfloor 0 6 7 (by decide) (by decide) (by decide)
        (hpos 0 6 7 (by decide) (by decide))
    have hb0 : m <= b0 := by
      simpa [b0] using hfloor 0 1 7 (by decide) (by decide) (by decide)
        (hpos 0 1 7 (by decide) (by decide))
    have hb1 : m <= b1 := by
      simpa [b1] using hfloor 1 2 3 (by decide) (by decide) (by decide)
        (hpos 1 2 3 (by decide) (by decide))
    have hb2 : m <= b2 := by
      simpa [b2] using hfloor 3 4 5 (by decide) (by decide) (by decide)
        (hpos 3 4 5 (by decide) (by decide))
    have hb3 : m <= b3 := by
      simpa [b3] using hfloor 5 6 7 (by decide) (by decide) (by decide)
        (hpos 5 6 7 (by decide) (by decide))

    have hX0 : 0 < X0 := by
      simpa [X0] using hpos 0 1 6 (by decide) (by decide)
    have hX1 : 0 < X1 := by
      simpa [X1] using hpos 0 2 3 (by decide) (by decide)
    have hX2 : 0 < X2 := by
      simpa [X2] using hpos 2 4 5 (by decide) (by decide)
    have hX3 : 0 < X3 := by
      simpa [X3] using hpos 4 6 7 (by decide) (by decide)
    have hZ0 : 0 < Z0 := by
      simpa [Z0] using hpos 0 2 7 (by decide) (by decide)
    have hZ1 : 0 < Z1 := by
      simpa [Z1] using hpos 1 2 4 (by decide) (by decide)
    have hZ2 : 0 < Z2 := by
      simpa [Z2] using hpos 3 4 6 (by decide) (by decide)
    have hZ3 : 0 < Z3 := by
      simpa [Z3] using hpos 0 5 6 (by decide) (by decide)

    have hXZ0 : X0 * Z0 = q0 * b0 + c3 * c0 := by
      dsimp [X0, Z0, q0, b0, c3, c0, p]
      simp only [sig]
      ring
    have hXZ1 : X1 * Z1 = q1 * b1 + c0 * c1 := by
      dsimp [X1, Z1, q1, b1, c0, c1, p]
      simp only [sig]
      ring
    have hXZ2 : X2 * Z2 = q2 * b2 + c1 * c2 := by
      dsimp [X2, Z2, q2, b2, c1, c2, p]
      simp only [sig]
      ring
    have hXZ3 : X3 * Z3 = q3 * b3 + c2 * c3 := by
      dsimp [X3, Z3, q3, b3, c2, c3, p]
      simp only [sig]
      ring

    have hNId0 : q1 * X0 + q0 * Z1 = N0 := by
      dsimp [N0, q0, q1, q3, c0, X0, Z1, p]
      simp only [sig]
      ring
    have hNId1 : q2 * X1 + q1 * Z2 = N1 := by
      dsimp [N1, q0, q1, q2, c1, X1, Z2, p]
      simp only [sig]
      ring
    have hNId2 : q3 * X2 + q2 * Z3 = N2 := by
      dsimp [N2, q1, q2, q3, c2, X2, Z3, p]
      simp only [sig]
      ring
    have hNId3 : q0 * X3 + q3 * Z0 = N3 := by
      dsimp [N3, q0, q2, q3, c3, X3, Z0, p]
      simp only [sig]
      ring

    have hN0 : 0 < N0 := by
      rw [← hNId0]
      exact add_pos (mul_pos hq1 hX0) (mul_pos hq0 hZ1)
    have hN1 : 0 < N1 := by
      rw [← hNId1]
      exact add_pos (mul_pos hq2 hX1) (mul_pos hq1 hZ2)
    have hN2 : 0 < N2 := by
      rw [← hNId2]
      exact add_pos (mul_pos hq3 hX2) (mul_pos hq2 hZ3)
    have hN3 : 0 < N3 := by
      rw [← hNId3]
      exact add_pos (mul_pos hq0 hX3) (mul_pos hq3 hZ0)

    have hD0 : m * q0 + c3 * c0 <= X0 * Z0 := by
      rw [hXZ0]
      have hmul := mul_le_mul_of_nonneg_left hb0 hq0.le
      nlinarith only [hmul]
    have hD1 : m * q1 + c0 * c1 <= X1 * Z1 := by
      rw [hXZ1]
      have hmul := mul_le_mul_of_nonneg_left hb1 hq1.le
      nlinarith only [hmul]
    have hD2 : m * q2 + c1 * c2 <= X2 * Z2 := by
      rw [hXZ2]
      have hmul := mul_le_mul_of_nonneg_left hb2 hq2.le
      nlinarith only [hmul]
    have hD3 : m * q3 + c2 * c3 <= X3 * Z3 := by
      rw [hXZ3]
      have hmul := mul_le_mul_of_nonneg_left hb3 hq3.le
      nlinarith only [hmul]

    have hAM0 : 4 * q0 * q1 * X0 * Z1 <= N0 ^ 2 := by
      rw [← hNId0]
      nlinarith only [sq_nonneg (q1 * X0 - q0 * Z1)]
    have hAM1 : 4 * q1 * q2 * X1 * Z2 <= N1 ^ 2 := by
      rw [← hNId1]
      nlinarith only [sq_nonneg (q2 * X1 - q1 * Z2)]
    have hAM2 : 4 * q2 * q3 * X2 * Z3 <= N2 ^ 2 := by
      rw [← hNId2]
      nlinarith only [sq_nonneg (q3 * X2 - q2 * Z3)]
    have hAM3 : 4 * q3 * q0 * X3 * Z0 <= N3 ^ 2 := by
      rw [← hNId3]
      nlinarith only [sq_nonneg (q0 * X3 - q3 * Z0)]

    have hAM01 :
        (4 * q0 * q1 * X0 * Z1) * (4 * q1 * q2 * X1 * Z2) <=
          N0 ^ 2 * N1 ^ 2 :=
      mul_le_mul hAM0 hAM1 (by positivity) (by positivity)
    have hAM23 :
        (4 * q2 * q3 * X2 * Z3) * (4 * q3 * q0 * X3 * Z0) <=
          N2 ^ 2 * N3 ^ 2 :=
      mul_le_mul hAM2 hAM3 (by positivity) (by positivity)
    have hAMall :
        ((4 * q0 * q1 * X0 * Z1) * (4 * q1 * q2 * X1 * Z2)) *
            ((4 * q2 * q3 * X2 * Z3) * (4 * q3 * q0 * X3 * Z0)) <=
          (N0 ^ 2 * N1 ^ 2) * (N2 ^ 2 * N3 ^ 2) :=
      mul_le_mul hAM01 hAM23 (by positivity) (by positivity)
    have hXZAux :
        256 * (X0 * Z0) * (X1 * Z1) * (X2 * Z2) * (X3 * Z3) *
            (q0 * q1 * q2 * q3) ^ 2 <=
          (N0 * N1 * N2 * N3) ^ 2 := by
      calc
        256 * (X0 * Z0) * (X1 * Z1) * (X2 * Z2) * (X3 * Z3) *
              (q0 * q1 * q2 * q3) ^ 2 =
            ((4 * q0 * q1 * X0 * Z1) * (4 * q1 * q2 * X1 * Z2)) *
              ((4 * q2 * q3 * X2 * Z3) * (4 * q3 * q0 * X3 * Z0)) := by
                ring
        _ <= (N0 ^ 2 * N1 ^ 2) * (N2 ^ 2 * N3 ^ 2) := hAMall
        _ = (N0 * N1 * N2 * N3) ^ 2 := by ring

    have hc0pos : 0 < c0 := lt_of_lt_of_le hm hc0
    have hc1pos : 0 < c1 := lt_of_lt_of_le hm hc1
    have hc2pos : 0 < c2 := lt_of_lt_of_le hm hc2
    have hc3pos : 0 < c3 := lt_of_lt_of_le hm hc3
    have hD01 :
        (m * q0 + c3 * c0) * (m * q1 + c0 * c1) <=
          (X0 * Z0) * (X1 * Z1) :=
      mul_le_mul hD0 hD1 (by positivity) (by positivity)
    have hD23 :
        (m * q2 + c1 * c2) * (m * q3 + c2 * c3) <=
          (X2 * Z2) * (X3 * Z3) :=
      mul_le_mul hD2 hD3 (by positivity) (by positivity)
    have hDall :
        ((m * q0 + c3 * c0) * (m * q1 + c0 * c1)) *
            ((m * q2 + c1 * c2) * (m * q3 + c2 * c3)) <=
          ((X0 * Z0) * (X1 * Z1)) * ((X2 * Z2) * (X3 * Z3)) :=
      mul_le_mul hD01 hD23 (by positivity) (by positivity)
    have hproduct :
        256 * (m * q0 + c3 * c0) * (m * q1 + c0 * c1) *
              (m * q2 + c1 * c2) * (m * q3 + c2 * c3) *
              (q0 * q1 * q2 * q3) ^ 2 <=
            (N0 * N1 * N2 * N3) ^ 2 := by
      have hfactor :
          0 <= (256 : Real) * (q0 * q1 * q2 * q3) ^ 2 :=
        mul_nonneg (by norm_num) (sq_nonneg (q0 * q1 * q2 * q3))
      have hscale := mul_le_mul_of_nonneg_left hDall hfactor
      calc
        256 * (m * q0 + c3 * c0) * (m * q1 + c0 * c1) *
              (m * q2 + c1 * c2) * (m * q3 + c2 * c3) *
              (q0 * q1 * q2 * q3) ^ 2 =
            (256 * (q0 * q1 * q2 * q3) ^ 2) *
              (((m * q0 + c3 * c0) * (m * q1 + c0 * c1)) *
                ((m * q2 + c1 * c2) * (m * q3 + c2 * c3))) := by ring
        _ <= (256 * (q0 * q1 * q2 * q3) ^ 2) *
              (((X0 * Z0) * (X1 * Z1)) * ((X2 * Z2) * (X3 * Z3))) := hscale
        _ = 256 * (X0 * Z0) * (X1 * Z1) * (X2 * Z2) * (X3 * Z3) *
              (q0 * q1 * q2 * q3) ^ 2 := by ring
        _ <= (N0 * N1 * N2 * N3) ^ 2 := hXZAux

    have hcentral : 17 * m <= 2 * (q0 + q2) :=
      hullEight_octagon_scalar_of_product hm hq0 hq1 hq2 hq3
        hc0 hc1 hc2 hc3 hqsum hN0 hN1 hN2 hN3 hproduct

    have hfan : fanSum v c = q0 + q2 + c0 + c1 + c2 + c3 := by
      rw [fanSum_eight_explicit]
      dsimp [q0, q2, c0, c1, c2, c3, p]
      simp only [sig]
      ring
    rw [hfan]
    nlinarith only [hc0, hc1, hc2, hc3, hcentral]
  · have hm0 : m = 0 := by
      exact le_antisymm (le_of_not_gt hm) (by simpa [m] using minTri_nonneg v)
    rw [hm0]
    have hfanNonneg := fanSum_nonneg hcyc
    nlinarith only [hfanNonneg]

private lemma fanCovers_eight_of_injective
    (v : Configuration) (c : Fin 8 -> Fin 8)
    (hc : Function.Injective c) :
    FanCovers v c := by
  intro p hp
  have hbijective : Function.Bijective c :=
    (Fintype.bijective_iff_injective_and_card _).mpr <| by
      exact And.intro hc rfl
  obtain ⟨i, hi⟩ := hbijective.2 p
  exact False.elim (hp ⟨i, hi⟩)

/-- The same bound stated for the actual doubled convex-hull area. -/
theorem strictOctagon_twentyFive_minTri_le_two_doubledHullArea
    {v : Configuration} {c : Fin 8 -> Fin 8}
    (hc : Function.Injective c)
    (hcyc : StrictCyclicPos c v) :
    25 * minTri v <= 2 * doubledHullArea v := by
  have hcover : FanCovers v c := fanCovers_eight_of_injective v c hc
  have hisHull : IsHullArea v (fanSum v c) :=
    IsHullArea.hull8 c hc hcyc hcover rfl
  rw [doubledHullArea_eq_of_isHullArea hisHull]
  exact strictOctagon_twentyFive_minTri_le_two_fanSum hc hcyc

/-- A strict convex eight-cycle cannot beat any target strictly above `2/25`. -/
theorem strictOctagon_not_Beats_of_two_div_twentyFive_lt
    {v : Configuration} {c : Fin 8 -> Fin 8} {q : Real}
    (hq : (2 : Real) / 25 < q)
    (hc : Function.Injective c)
    (hcyc : StrictCyclicPos c v) :
    ¬ Beats doubledHullArea q v := by
  intro hbeat
  have hscaled :
      (2 : Real) / 25 * doubledHullArea v < q * doubledHullArea v :=
    mul_lt_mul_of_pos_right hq hbeat.1
  have hsmall :
      (2 : Real) / 25 * doubledHullArea v < minTri v :=
    lt_trans hscaled hbeat.2
  have hbound :=
    strictOctagon_twentyFive_minTri_le_two_doubledHullArea hc hcyc
  nlinarith only [hsmall, hbound]

end Heilbronn8
