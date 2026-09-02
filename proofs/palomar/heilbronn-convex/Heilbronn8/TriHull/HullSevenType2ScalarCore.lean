import Heilbronn8.TriHull.HullSevenType2Bernstein

/-!
# The retained hull-seven type-2 scalar inequality

This file is the topology-free closer for the full-retained type-2 chamber.
It uses four reflection-geometric-mean Pluecker rows, two paired ear facts,
and the central cap.  The only finite certificates are the six small
Bernstein sign checks in `HullSevenType2Bernstein`.

The variables are geometric means of reflected chord pairs.  In particular
`X,Y,Z,W` are boundary-cell means, `r,s,U,Q,R,M` are chord means, and `A,B`
are half-sums of reflected boundary pairs.  All quantities have already been
divided by the positive minimum triangle area.
-/

set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Heilbronn8.TriHull

noncomputable section

/-! ## The two-variable rational core -/

def hullSevenType2D (rho t : ℝ) : ℝ := t + 1 - rho ^ 2

def hullSevenType2X0 (rho t : ℝ) : ℝ :=
  (t + 1 + rho ^ 2 + 2 * rho) / hullSevenType2D rho t

def hullSevenType2R0 (rho t : ℝ) : ℝ :=
  ((t + 1) / rho + rho) / 2

def hullSevenType2G0 (rho t : ℝ) : ℝ :=
  (t + 1) * (rho * (hullSevenType2X0 rho t + 1) - t) / t

def hullSevenType2C0 (rho t : ℝ) : ℝ :=
  23 / 4 - t / 2 - 1 / rho

def hullSevenType2Eps (rho t : ℝ) : ℝ :=
  hullSevenType2C0 rho t - 1 - hullSevenType2R0 rho t

def hullSevenType2U0 (rho t : ℝ) : ℝ :=
  hullSevenType2C0 rho t - 1 - hullSevenType2G0 rho t -
    hullSevenType2X0 rho t

def hullSevenType2F0 (rho t : ℝ) : ℝ :=
  (hullSevenType2C0 rho t - 1) ^ 2 +
    ((hullSevenType2C0 rho t - 1 - hullSevenType2G0 rho t) ^ 2 -
      (hullSevenType2X0 rho t) ^ 2) / 2 -
    2 * hullSevenType2G0 rho t / 3

private def hullSevenType2T0 (rho : ℝ) : ℝ :=
  (19 * rho - 2 * rho ^ 2 - 6) / (2 * (rho + 1))

private def hullSevenType2Te (rho : ℝ) : ℝ :=
  (303 * rho - 32 * rho ^ 2 - 96) / (32 * (rho + 1))

private lemma hullSevenType2_T0_factors {rho : ℝ}
    (hrho : 0 < rho) (hT : 0 < hullSevenType2T0 rho)
    (hD : 0 < hullSevenType2D rho (hullSevenType2T0 rho)) :
    0 < 4 * rho * (rho + 1) *
      (2 * rho ^ 2 - 19 * rho + 6) *
      (2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4) := by
  have hrho1 : 0 < rho + 1 := by linarith
  have hf2 : 2 * rho ^ 2 - 19 * rho + 6 < 0 := by
    have hid :
        2 * rho ^ 2 - 19 * rho + 6 =
          -2 * (rho + 1) * hullSevenType2T0 rho := by
      unfold hullSevenType2T0
      field_simp [hrho1.ne']
      <;> ring
    rw [hid]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hrho1) hT
  have hf3 : 2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4 < 0 := by
    have hid :
        2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4 =
          -2 * (rho + 1) *
            hullSevenType2D rho (hullSevenType2T0 rho) := by
      unfold hullSevenType2D hullSevenType2T0
      field_simp [hrho1.ne']
      <;> ring
    rw [hid]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hrho1) hD
  have hff : 0 <
      (2 * rho ^ 2 - 19 * rho + 6) *
        (2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4) :=
    mul_pos_of_neg_of_neg hf2 hf3
  simpa [mul_assoc] using
    mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hrho) hrho1) hff

private lemma hullSevenType2_U_T0_cross {rho : ℝ}
    (hrho : 0 < rho) (hT : 0 < hullSevenType2T0 rho)
    (hD : 0 < hullSevenType2D rho (hullSevenType2T0 rho)) :
    (4 * rho * (rho + 1) *
        (2 * rho ^ 2 - 19 * rho + 6) *
        (2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4)) *
      hullSevenType2U0 rho (hullSevenType2T0 rho) =
      -8 * rho ^ 8 + 244 * rho ^ 7 - 732 * rho ^ 6 -
        9456 * rho ^ 5 + 12836 * rho ^ 4 - 2157 * rho ^ 3 -
        2662 * rho ^ 2 + 1024 * rho - 96 := by
  have hrho1 : 0 < rho + 1 := by linarith
  unfold hullSevenType2U0 hullSevenType2C0 hullSevenType2G0
    hullSevenType2X0
  field_simp [hrho.ne', hT.ne', hD.ne']
  simp only [hullSevenType2D, hullSevenType2T0]
  field_simp [hrho1.ne']
  ring

private lemma hullSevenType2_V_neg_left (rho : ℝ)
    (hrho : 0 < rho) (hT : 0 < hullSevenType2T0 rho)
    (hD : 0 < hullSevenType2D rho (hullSevenType2T0 rho))
    (hlo : (13 : ℝ) / 40 ≤ rho) (hhi : rho ≤ 5 / 8) :
    hullSevenType2U0 rho (hullSevenType2T0 rho) < 0 := by
  have hp := hullSevenType2_outer_left_pos rho hlo hhi
  have hden := hullSevenType2_T0_factors hrho hT hD
  have hid := hullSevenType2_U_T0_cross hrho hT hD
  by_contra hn
  have hu : 0 ≤ hullSevenType2U0 rho (hullSevenType2T0 rho) :=
    le_of_not_gt hn
  have := mul_nonneg hden.le hu
  nlinarith

private lemma hullSevenType2_V_neg_right (rho : ℝ)
    (hrho : 0 < rho) (hT : 0 < hullSevenType2T0 rho)
    (hD : 0 < hullSevenType2D rho (hullSevenType2T0 rho))
    (hlo : (5 : ℝ) / 7 ≤ rho) (hhi : rho ≤ 5 / 2) :
    hullSevenType2U0 rho (hullSevenType2T0 rho) < 0 := by
  have hp := hullSevenType2_outer_right_pos rho hlo hhi
  have hden := hullSevenType2_T0_factors hrho hT hD
  have hid := hullSevenType2_U_T0_cross hrho hT hD
  by_contra hn
  have hu : 0 ≤ hullSevenType2U0 rho (hullSevenType2T0 rho) :=
    le_of_not_gt hn
  have := mul_nonneg hden.le hu
  nlinarith

private lemma hullSevenType2_G_T0 (rho : ℝ)
    (hrho : 0 < rho) (hT : 0 < hullSevenType2T0 rho)
    (hD : 0 < hullSevenType2D rho (hullSevenType2T0 rho))
    (hlo : (5 : ℝ) / 8 ≤ rho) (hhi : rho ≤ 5 / 7) :
    (1 : ℝ) / 3 < hullSevenType2G0 rho (hullSevenType2T0 rho) := by
  have hp := hullSevenType2_g_endpoint_pos rho hlo hhi
  have hden0 := hullSevenType2_T0_factors hrho hT hD
  have hden : 0 <
      6 * (rho + 1) * (2 * rho ^ 2 - 19 * rho + 6) *
        (2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4) := by
    have hrho1 : 0 < rho + 1 := by linarith
    have hf2 : 2 * rho ^ 2 - 19 * rho + 6 < 0 := by
      have := hullSevenType2_T0_factors hrho hT hD
      have hid : 2 * rho ^ 2 - 19 * rho + 6 =
          -2 * (rho + 1) * hullSevenType2T0 rho := by
        unfold hullSevenType2T0
        field_simp [hrho1.ne']
        <;> ring
      rw [hid]
      exact mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by norm_num) hrho1) hT
    have hf3 : 2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4 < 0 := by
      have hid : 2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4 =
          -2 * (rho + 1) *
            hullSevenType2D rho (hullSevenType2T0 rho) := by
        unfold hullSevenType2D hullSevenType2T0
        field_simp [hrho1.ne']
        <;> ring
      rw [hid]
      exact mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by norm_num) hrho1) hD
    have hff := mul_pos_of_neg_of_neg hf2 hf3
    simpa [mul_assoc] using
      mul_pos (mul_pos (by norm_num : (0 : ℝ) < 6) hrho1) hff
  have hid :
      (6 * (rho + 1) * (2 * rho ^ 2 - 19 * rho + 6) *
          (2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4)) *
        (hullSevenType2G0 rho (hullSevenType2T0 rho) - 1 / 3) =
        24 * rho ^ 7 - 440 * rho ^ 6 + 802 * rho ^ 5 +
          14516 * rho ^ 4 - 26507 * rho ^ 3 + 15664 * rho ^ 2 -
          3388 * rho + 240 := by
    have hrho1 : 0 < rho + 1 := by linarith
    unfold hullSevenType2G0 hullSevenType2X0
    field_simp [hrho.ne', hT.ne', hD.ne']
    simp only [hullSevenType2D, hullSevenType2T0]
    field_simp [hrho1.ne']
    ring
  have hmul : 0 <
      (6 * (rho + 1) * (2 * rho ^ 2 - 19 * rho + 6) *
          (2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4)) *
        (hullSevenType2G0 rho (hullSevenType2T0 rho) - 1 / 3) := by
    rw [hid]
    exact hp
  rcases mul_pos_iff.mp hmul with h | h
  · exact sub_pos.mp h.2
  · exact (not_lt_of_ge hden.le h.1).elim

private lemma hullSevenType2_U_T0_lt (rho : ℝ)
    (hrho : 0 < rho) (hT : 0 < hullSevenType2T0 rho)
    (hD : 0 < hullSevenType2D rho (hullSevenType2T0 rho))
    (hlo : (5 : ℝ) / 8 ≤ rho) (hhi : rho ≤ 5 / 7) :
    hullSevenType2U0 rho (hullSevenType2T0 rho) < (1 : ℝ) / 32 := by
  have hp := hullSevenType2_u_endpoint_pos rho hlo hhi
  have hden0 := hullSevenType2_T0_factors hrho hT hD
  have hden : 0 < 32 * rho * (rho + 1) *
      (2 * rho ^ 2 - 19 * rho + 6) *
      (2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4) := by
    nlinarith [hden0]
  have hid :
      (32 * rho * (rho + 1) *
          (2 * rho ^ 2 - 19 * rho + 6) *
          (2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4)) *
        (1 / 32 - hullSevenType2U0 rho (hullSevenType2T0 rho)) =
        64 * rho ^ 8 - 1948 * rho ^ 7 + 5830 * rho ^ 6 +
          75512 * rho ^ 5 - 102363 * rho ^ 4 + 17485 * rho ^ 3 +
          21118 * rho ^ 2 - 8168 * rho + 768 := by
    have hrho1 : 0 < rho + 1 := by linarith
    unfold hullSevenType2U0 hullSevenType2C0 hullSevenType2G0
      hullSevenType2X0
    field_simp [hrho.ne', hT.ne', hD.ne']
    simp only [hullSevenType2D, hullSevenType2T0]
    field_simp [hrho1.ne']
    ring
  have hmul : 0 <
      (32 * rho * (rho + 1) *
          (2 * rho ^ 2 - 19 * rho + 6) *
          (2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4)) *
        (1 / 32 - hullSevenType2U0 rho (hullSevenType2T0 rho)) := by
    rw [hid]
    exact hp
  rcases mul_pos_iff.mp hmul with h | h
  · linarith [h.2]
  · exact (not_lt_of_ge hden.le h.1).elim

private lemma hullSevenType2_U_Te_neg (rho : ℝ)
    (hrho : 0 < rho) (hTe : 0 < hullSevenType2Te rho)
    (hD : 0 < hullSevenType2D rho (hullSevenType2Te rho))
    (hp : 0 <
      32768 * rho ^ 8 - 997376 * rho ^ 7 + 2974240 * rho ^ 6 +
        38523136 * rho ^ 5 - 52170591 * rho ^ 4 + 8796688 * rho ^ 3 +
        10845760 * rho ^ 2 - 4184064 * rho + 393216) :
    hullSevenType2U0 rho (hullSevenType2Te rho) < 0 := by
  have hrho1 : 0 < rho + 1 := by linarith
  have hf2 : 32 * rho ^ 2 - 303 * rho + 96 < 0 := by
    have hid : 32 * rho ^ 2 - 303 * rho + 96 =
        -32 * (rho + 1) * hullSevenType2Te rho := by
      unfold hullSevenType2Te
      field_simp [hrho1.ne']
      <;> ring
    rw [hid]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hrho1) hTe
  have hf3 : 32 * rho ^ 3 + 64 * rho ^ 2 - 335 * rho + 64 < 0 := by
    have hid : 32 * rho ^ 3 + 64 * rho ^ 2 - 335 * rho + 64 =
        -32 * (rho + 1) *
          hullSevenType2D rho (hullSevenType2Te rho) := by
      unfold hullSevenType2D hullSevenType2Te
      field_simp [hrho1.ne']
      <;> ring
    rw [hid]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hrho1) hD
  have hden : 0 < 64 * rho * (rho + 1) *
      (32 * rho ^ 2 - 303 * rho + 96) *
      (32 * rho ^ 3 + 64 * rho ^ 2 - 335 * rho + 64) := by
    have hff := mul_pos_of_neg_of_neg hf2 hf3
    simpa [mul_assoc] using
      mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 64) hrho) hrho1) hff
  have hid :
      -(64 * rho * (rho + 1) *
          (32 * rho ^ 2 - 303 * rho + 96) *
          (32 * rho ^ 3 + 64 * rho ^ 2 - 335 * rho + 64) *
          hullSevenType2U0 rho (hullSevenType2Te rho)) =
        32768 * rho ^ 8 - 997376 * rho ^ 7 + 2974240 * rho ^ 6 +
          38523136 * rho ^ 5 - 52170591 * rho ^ 4 +
          8796688 * rho ^ 3 + 10845760 * rho ^ 2 -
          4184064 * rho + 393216 := by
    unfold hullSevenType2U0 hullSevenType2C0 hullSevenType2G0
      hullSevenType2X0
    field_simp [hrho.ne', hTe.ne', hD.ne']
    simp only [hullSevenType2D, hullSevenType2Te]
    field_simp [hrho1.ne']
    ring
  by_contra hn
  have hu : 0 ≤ hullSevenType2U0 rho (hullSevenType2Te rho) :=
    le_of_not_gt hn
  have hmul := mul_nonneg hden.le hu
  nlinarith

private lemma hullSevenType2_U_Te_left (rho : ℝ)
    (hrho : 0 < rho) (hTe : 0 < hullSevenType2Te rho)
    (hD : 0 < hullSevenType2D rho (hullSevenType2Te rho))
    (hlo : (5 : ℝ) / 8 ≤ rho) (hhi : rho ≤ 2 / 3) :
    hullSevenType2U0 rho (hullSevenType2Te rho) < 0 :=
  hullSevenType2_U_Te_neg rho hrho hTe hD
    (hullSevenType2_epsilon_left_pos rho hlo hhi)

private lemma hullSevenType2_U_Te_right (rho : ℝ)
    (hrho : 0 < rho) (hTe : 0 < hullSevenType2Te rho)
    (hD : 0 < hullSevenType2D rho (hullSevenType2Te rho))
    (hlo : (2 : ℝ) / 3 ≤ rho) (hhi : rho ≤ 5 / 7) :
    hullSevenType2U0 rho (hullSevenType2Te rho) < 0 :=
  hullSevenType2_U_Te_neg rho hrho hTe hD
    (hullSevenType2_epsilon_right_pos rho hlo hhi)

/-! The monotonicity needed below is algebraic.  These divided-difference
identities avoid derivatives and the mean-value theorem. -/

private lemma hullSevenType2_U_mono {rho t T : ℝ}
    (hrho : 0 < rho) (ht : 0 < t) (hT : 0 < T)
    (hDt : 0 < hullSevenType2D rho t)
    (hDT : 0 < hullSevenType2D rho T) (htT : t ≤ T) :
    hullSevenType2U0 rho t ≤ hullSevenType2U0 rho T := by
  rcases le_total rho 1 with hrle | hrge
  · have hrho0 : 0 ≤ rho := hrho.le
    have hrho1 : 0 ≤ 1 - rho := by linarith
    have hsquare : 0 ≤ 1 - rho ^ 2 := by
      have := mul_nonneg hrho1 (by linarith : 0 ≤ 1 + rho)
      nlinarith
    let K : ℝ :=
      t ^ 2 * T ^ 2 + (1 - rho ^ 2) * (t ^ 2 * T + t * T ^ 2) +
      (rho ^ 4 + 4 * rho ^ 3 + 6 * rho ^ 2 + 8 * rho + 1) * t * T +
      4 * rho * (rho + 1) * (t + T) +
      4 * rho * (1 - rho) * (rho + 1) ^ 2
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    have hid :
        hullSevenType2U0 rho T - hullSevenType2U0 rho t =
          (T - t) * K /
            (2 * T * t * hullSevenType2D rho T *
              hullSevenType2D rho t) := by
      unfold hullSevenType2U0 hullSevenType2C0 hullSevenType2G0
        hullSevenType2X0
      field_simp [hrho.ne', ht.ne', hT.ne', hDt.ne', hDT.ne']
      dsimp [K]
      simp only [hullSevenType2D]
      ring
    rw [← sub_nonneg, hid]
    positivity
  · have hrho1 : 1 ≤ rho := hrge
    have hsquare : 0 ≤ rho ^ 2 - 1 := by
      have := mul_nonneg (by linarith : 0 ≤ rho - 1)
        (by linarith : 0 ≤ rho + 1)
      nlinarith
    have hcubic : 0 ≤ rho ^ 3 + rho ^ 2 - 1 := by
      have hc : 0 ≤ rho ^ 3 := by positivity
      nlinarith
    let d : ℝ := hullSevenType2D rho t
    let e : ℝ := hullSevenType2D rho T
    let K : ℝ :=
      d ^ 2 * e ^ 2 + (rho ^ 2 - 1) * (d ^ 2 * e + d * e ^ 2) +
      (rho ^ 4 + 4 * rho ^ 3 + 6 * rho ^ 2 + 8 * rho + 1) * d * e +
      4 * rho * (rho + 1) * (rho ^ 3 + rho ^ 2 - 1) * (d + e) +
      4 * rho * (rho - 1) * (rho + 1) ^ 2 *
        (rho ^ 3 + rho ^ 2 - 1)
    have hd : 0 < d := by simpa [d] using hDt
    have he : 0 < e := by simpa [e] using hDT
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    have hid :
        hullSevenType2U0 rho T - hullSevenType2U0 rho t =
          (T - t) * K /
            (2 * T * t * hullSevenType2D rho T *
              hullSevenType2D rho t) := by
      unfold hullSevenType2U0 hullSevenType2C0 hullSevenType2G0
        hullSevenType2X0
      field_simp [hrho.ne', ht.ne', hT.ne', hDt.ne', hDT.ne']
      dsimp [K, d, e]
      simp only [hullSevenType2D]
      ring
    rw [← sub_nonneg, hid]
    positivity

private lemma hullSevenType2_G_anti {rho t T : ℝ}
    (hrho : 0 < rho) (ht : 0 < t) (hT : 0 < T)
    (hDt : 0 < hullSevenType2D rho t)
    (hDT : 0 < hullSevenType2D rho T) (htT : t ≤ T) :
    hullSevenType2G0 rho T ≤ hullSevenType2G0 rho t := by
  rcases le_total rho 1 with hrle | hrge
  · have hrho1 : 0 ≤ 1 - rho := by linarith
    have hsquare : 0 ≤ 1 - rho ^ 2 := by
      have := mul_nonneg hrho1 (by linarith : 0 ≤ 1 + rho)
      nlinarith
    let K : ℝ :=
      t ^ 2 * T ^ 2 + (1 - rho ^ 2) * (t ^ 2 * T + t * T ^ 2) +
      (rho ^ 4 + 2 * rho ^ 3 + 2 * rho + 1) * t * T +
      2 * rho * (rho + 1) * (t + T) +
      2 * rho * (1 - rho) * (rho + 1) ^ 2
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    have hid :
        hullSevenType2G0 rho t - hullSevenType2G0 rho T =
          (T - t) * K /
            (T * t * hullSevenType2D rho T *
              hullSevenType2D rho t) := by
      unfold hullSevenType2G0 hullSevenType2X0
      field_simp [hrho.ne', ht.ne', hT.ne', hDt.ne', hDT.ne']
      dsimp [K]
      simp only [hullSevenType2D]
      ring
    rw [← sub_nonneg, hid]
    positivity
  · have hrho1 : 1 ≤ rho := hrge
    have hsquare : 0 ≤ rho ^ 2 - 1 := by
      have := mul_nonneg (by linarith : 0 ≤ rho - 1)
        (by linarith : 0 ≤ rho + 1)
      nlinarith
    let d : ℝ := hullSevenType2D rho t
    let e : ℝ := hullSevenType2D rho T
    let K : ℝ :=
      d ^ 2 * e ^ 2 + (rho ^ 2 - 1) * (d ^ 2 * e + d * e ^ 2) +
      (rho ^ 4 + 2 * rho ^ 3 + 2 * rho + 1) * d * e +
      2 * rho ^ 4 * (rho + 1) * (d + e) +
      2 * rho ^ 4 * (rho - 1) * (rho + 1) ^ 2
    have hd : 0 < d := by simpa [d] using hDt
    have he : 0 < e := by simpa [e] using hDT
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    have hid :
        hullSevenType2G0 rho t - hullSevenType2G0 rho T =
          (T - t) * K /
            (T * t * hullSevenType2D rho T *
              hullSevenType2D rho t) := by
      unfold hullSevenType2G0 hullSevenType2X0
      field_simp [hrho.ne', ht.ne', hT.ne', hDt.ne', hDT.ne']
      dsimp [K, d, e]
      simp only [hullSevenType2D]
      ring
    rw [← sub_nonneg, hid]
    positivity

/-- The exact two-variable obstruction at the heart of the type-2 proof. -/
theorem hullSevenType2_rho_core (rho t : ℝ)
    (hrho : 0 < rho) (ht : 0 < t) (hD : 0 < hullSevenType2D rho t)
    (heps : 0 ≤ hullSevenType2Eps rho t)
    (hu : 0 ≤ hullSevenType2U0 rho t) :
    hullSevenType2F0 rho t < (hullSevenType2R0 rho t) ^ 2 := by
  have hrho1 : 0 < rho + 1 := by linarith
  have htT0 : t ≤ hullSevenType2T0 rho := by
    have hid :
        (2 * rho) * hullSevenType2Eps rho t =
          (rho + 1) * (hullSevenType2T0 rho - t) := by
      unfold hullSevenType2Eps hullSevenType2C0 hullSevenType2R0
        hullSevenType2T0
      field_simp [hrho.ne', hrho1.ne']
      <;> ring
    have hp : 0 ≤ (2 * rho) * hullSevenType2Eps rho t :=
      mul_nonneg (by positivity) heps
    rw [hid] at hp
    by_contra hn
    have hneg : hullSevenType2T0 rho - t < 0 := by linarith
    have := mul_neg_of_pos_of_neg hrho1 hneg
    linarith
  have hT0 : 0 < hullSevenType2T0 rho := lt_of_lt_of_le ht htT0
  have hDT0 : 0 < hullSevenType2D rho (hullSevenType2T0 rho) := by
    unfold hullSevenType2D at hD ⊢
    linarith
  have hV : 0 ≤ hullSevenType2U0 rho (hullSevenType2T0 rho) :=
    le_trans hu
      (hullSevenType2_U_mono hrho ht hT0 hD hDT0 htT0)
  have hf2 : 2 * rho ^ 2 - 19 * rho + 6 < 0 := by
    have hid : 2 * rho ^ 2 - 19 * rho + 6 =
        -2 * (rho + 1) * hullSevenType2T0 rho := by
      unfold hullSevenType2T0
      field_simp [hrho1.ne']
      <;> ring
    rw [hid]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hrho1) hT0
  have hf3 : 2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4 < 0 := by
    have hid : 2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4 =
        -2 * (rho + 1) *
          hullSevenType2D rho (hullSevenType2T0 rho) := by
      unfold hullSevenType2D hullSevenType2T0
      field_simp [hrho1.ne']
      <;> ring
    rw [hid]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hrho1) hDT0
  have hrhoCoarseL : (13 : ℝ) / 40 < rho := by
    by_contra hn
    have hw : 0 ≤ (13 : ℝ) / 40 - rho := by linarith
    have hid : 19 * rho - 2 * rho ^ 2 - 6 =
        -2 * ((13 : ℝ) / 40 - rho) ^ 2 -
          (177 : ℝ) / 10 * ((13 : ℝ) / 40 - rho) - 29 / 800 := by
      ring
    have hq : 0 < 19 * rho - 2 * rho ^ 2 - 6 := by
      nlinarith [hf2]
    rw [hid] at hq
    nlinarith [sq_nonneg ((13 : ℝ) / 40 - rho)]
  have hrhoCoarseR : rho < (5 : ℝ) / 2 := by
    by_contra hn
    have hw : 0 ≤ rho - (5 : ℝ) / 2 := by linarith
    have hid : 2 * rho ^ 3 + 4 * rho ^ 2 - 21 * rho + 4 =
        2 * (rho - 5 / 2) ^ 3 + 19 * (rho - 5 / 2) ^ 2 +
          (73 : ℝ) / 2 * (rho - 5 / 2) + 31 / 4 := by
      ring
    have hpos : 0 <
        2 * (rho - 5 / 2) ^ 3 + 19 * (rho - 5 / 2) ^ 2 +
          (73 : ℝ) / 2 * (rho - 5 / 2) + 31 / 4 := by
      positivity
    linarith
  have hrhoL : (5 : ℝ) / 8 < rho := by
    by_contra hn
    have hneg := hullSevenType2_V_neg_left rho hrho hT0 hDT0
      (le_of_lt hrhoCoarseL) (le_of_not_gt hn)
    linarith
  have hrhoR : rho < (5 : ℝ) / 7 := by
    by_contra hn
    have hneg := hullSevenType2_V_neg_right rho hrho hT0 hDT0
      (le_of_not_gt hn) (le_of_lt hrhoCoarseR)
    linarith
  have htL : (3 : ℝ) / 2 < t := by
    by_contra hn
    have ht15 : t ≤ (3 : ℝ) / 2 := le_of_not_gt hn
    have hD15 : 0 < hullSevenType2D rho (3 / 2) := by
      unfold hullSevenType2D at hD ⊢
      linarith
    have hu15 : 0 ≤ hullSevenType2U0 rho (3 / 2) :=
      le_trans hu
        (hullSevenType2_U_mono hrho ht (by norm_num) hD hD15 ht15)
    have hw : 0 ≤ rho - 5 / 8 := by linarith
    have hnid : 130 * rho ^ 3 + 112 * rho ^ 2 - 165 * rho + 30 =
        130 * (rho - 5 / 8) ^ 3 + (1423 : ℝ) / 4 * (rho - 5 / 8) ^ 2 +
          (4075 : ℝ) / 32 * (rho - 5 / 8) + 605 / 256 := by
      ring
    have hnpos : 0 < 130 * rho ^ 3 + 112 * rho ^ 2 - 165 * rho + 30 := by
      rw [hnid]
      positivity
    have hrhoLtOne : rho < 1 := lt_trans hrhoR (by norm_num)
    have hdenneg : 6 * rho * (2 * rho ^ 2 - 5) < 0 := by
      have hs : 0 < (1 - rho) * (1 + rho) :=
        mul_pos (sub_pos.mpr hrhoLtOne) (by linarith)
      have hr2 : rho ^ 2 < 1 := by nlinarith
      exact mul_neg_of_pos_of_neg (by positivity) (by nlinarith)
    have hD32 : 0 < hullSevenType2D rho (3 / 2) := hD15
    have huid :
        (6 * rho * (2 * rho ^ 2 - 5)) * hullSevenType2U0 rho (3 / 2) =
          130 * rho ^ 3 + 112 * rho ^ 2 - 165 * rho + 30 := by
      unfold hullSevenType2U0 hullSevenType2C0 hullSevenType2G0
        hullSevenType2X0
      field_simp [hrho.ne', hD32.ne']
      simp only [hullSevenType2D]
      ring
    have hnonpos :
        (6 * rho * (2 * rho ^ 2 - 5)) *
            hullSevenType2U0 rho (3 / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hdenneg.le hu15
    rw [huid] at hnonpos
    linarith
  have htR : t < 2 := by
    have hw : 0 ≤ 5 / 7 - rho := by linarith
    have hpid : -2 * rho ^ 2 + 15 * rho - 10 =
        -2 * (5 / 7 - rho) ^ 2 - (85 : ℝ) / 7 * (5 / 7 - rho) -
          15 / 49 := by
      ring
    have hpneg : -2 * rho ^ 2 + 15 * rho - 10 < 0 := by
      rw [hpid]
      nlinarith [sq_nonneg (5 / 7 - rho)]
    have hTid : hullSevenType2T0 rho - 2 =
        (-2 * rho ^ 2 + 15 * rho - 10) / (2 * (rho + 1)) := by
      unfold hullSevenType2T0
      field_simp [hrho1.ne']
      <;> ring
    have hTlt : hullSevenType2T0 rho < 2 := by
      have : hullSevenType2T0 rho - 2 < 0 := by
        rw [hTid]
        exact div_neg_of_neg_of_pos hpneg (by positivity)
      linarith
    exact lt_of_le_of_lt htT0 hTlt
  have hG : (1 : ℝ) / 3 < hullSevenType2G0 rho t :=
    lt_of_lt_of_le
      (hullSevenType2_G_T0 rho hrho hT0 hDT0
        (le_of_lt hrhoL) (le_of_lt hrhoR))
      (hullSevenType2_G_anti hrho ht hT0 hD hDT0 htT0)
  have hU32 : hullSevenType2U0 rho t < (1 : ℝ) / 32 :=
    lt_of_le_of_lt
      (hullSevenType2_U_mono hrho ht hT0 hD hDT0 htT0)
      (hullSevenType2_U_T0_lt rho hrho hT0 hDT0
        (le_of_lt hrhoL) (le_of_lt hrhoR))
  have hE64 : hullSevenType2Eps rho t < (1 : ℝ) / 64 := by
    by_contra hn
    have hge : (1 : ℝ) / 64 ≤ hullSevenType2Eps rho t :=
      le_of_not_gt hn
    have htTe : t ≤ hullSevenType2Te rho := by
      have hid :
          (2 * rho) * (hullSevenType2Eps rho t - 1 / 64) =
            (rho + 1) * (hullSevenType2Te rho - t) := by
        unfold hullSevenType2Eps hullSevenType2C0 hullSevenType2R0
          hullSevenType2Te
        field_simp [hrho.ne', hrho1.ne']
        <;> ring
      have hp : 0 ≤
          (2 * rho) * (hullSevenType2Eps rho t - 1 / 64) :=
        mul_nonneg (by positivity) (by linarith)
      rw [hid] at hp
      by_contra hnot
      have hneg : hullSevenType2Te rho - t < 0 := by linarith
      have := mul_neg_of_pos_of_neg hrho1 hneg
      linarith
    have hTe : 0 < hullSevenType2Te rho := lt_of_lt_of_le ht htTe
    have hDTe : 0 < hullSevenType2D rho (hullSevenType2Te rho) := by
      unfold hullSevenType2D at hD ⊢
      linarith
    have huTe : 0 ≤ hullSevenType2U0 rho (hullSevenType2Te rho) :=
      le_trans hu
        (hullSevenType2_U_mono hrho ht hTe hD hDTe htTe)
    rcases le_total rho ((2 : ℝ) / 3) with hcase | hcase
    · have hneg := hullSevenType2_U_Te_left rho hrho hTe hDTe
        (le_of_lt hrhoL) hcase
      linarith
    · have hneg := hullSevenType2_U_Te_right rho hrho hTe hDTe
        hcase (le_of_lt hrhoR)
      linarith
  have hinv : (7 : ℝ) / 5 < 1 / rho := by
    rw [lt_div_iff₀ hrho]
    nlinarith [hrhoR]
  have hC : hullSevenType2C0 rho t - 1 < (13 : ℝ) / 5 := by
    unfold hullSevenType2C0
    linarith
  have hRpos : 0 < hullSevenType2R0 rho t := by
    unfold hullSevenType2R0
    positivity
  have hRbd : hullSevenType2R0 rho t < (13 : ℝ) / 5 := by
    unfold hullSevenType2Eps at heps
    linarith
  have hXpos : 0 < hullSevenType2X0 rho t := by
    unfold hullSevenType2X0
    exact div_pos (by positivity) hD
  have hAbar :
      hullSevenType2X0 rho t + hullSevenType2U0 rho t < (13 : ℝ) / 5 := by
    have hid :
        hullSevenType2X0 rho t + hullSevenType2U0 rho t =
          hullSevenType2C0 rho t - 1 - hullSevenType2G0 rho t := by
      unfold hullSevenType2U0
      ring
    rw [hid]
    nlinarith
  have hXsum :
      2 * hullSevenType2X0 rho t + hullSevenType2U0 rho t <
        (26 : ℝ) / 5 := by
    nlinarith
  have hRsum :
      2 * hullSevenType2R0 rho t + hullSevenType2Eps rho t <
        (26 : ℝ) / 5 + 1 / 64 := by
    nlinarith
  have hEterm :
      hullSevenType2Eps rho t *
          (2 * hullSevenType2R0 rho t + hullSevenType2Eps rho t) <
        (1669 : ℝ) / 20480 := by
    have hvpos : 0 <
        2 * hullSevenType2R0 rho t + hullSevenType2Eps rho t := by
      nlinarith
    have h1 : 0 ≤
        (1 / 64 - hullSevenType2Eps rho t) *
          (2 * hullSevenType2R0 rho t + hullSevenType2Eps rho t) :=
      mul_nonneg (by linarith) hvpos.le
    have h2 : 0 < (1 : ℝ) / 64 *
        ((26 / 5 + 1 / 64) -
          (2 * hullSevenType2R0 rho t + hullSevenType2Eps rho t)) := by
      positivity
    nlinarith
  have hUterm :
      hullSevenType2U0 rho t *
          (2 * hullSevenType2X0 rho t + hullSevenType2U0 rho t) / 2 <
        (13 : ℝ) / 160 := by
    have hvpos : 0 <
        2 * hullSevenType2X0 rho t + hullSevenType2U0 rho t := by
      nlinarith
    have h1 : 0 ≤
        (1 / 32 - hullSevenType2U0 rho t) *
          (2 * hullSevenType2X0 rho t + hullSevenType2U0 rho t) :=
      mul_nonneg (by linarith) hvpos.le
    have h2 : 0 < (1 : ℝ) / 32 *
        ((26 / 5) -
          (2 * hullSevenType2X0 rho t + hullSevenType2U0 rho t)) := by
      positivity
    nlinarith
  have hexcess :
      hullSevenType2F0 rho t - (hullSevenType2R0 rho t) ^ 2 =
        hullSevenType2Eps rho t *
            (2 * hullSevenType2R0 rho t + hullSevenType2Eps rho t) +
          hullSevenType2U0 rho t *
            (2 * hullSevenType2X0 rho t + hullSevenType2U0 rho t) / 2 -
          2 * hullSevenType2G0 rho t / 3 := by
    unfold hullSevenType2F0 hullSevenType2Eps hullSevenType2U0
    ring
  have hneg :
      hullSevenType2F0 rho t - (hullSevenType2R0 rho t) ^ 2 < 0 := by
    rw [hexcess]
    nlinarith [hEterm, hUterm, hG]
  linarith

end

end Heilbronn8.TriHull
