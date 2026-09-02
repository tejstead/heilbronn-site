import Mathlib

/-!
# A small exact triangular Bernstein checker

This file contains the reusable kernel-checked part of the finite certificate
used by the one-negative hull-six chamber.  A total-degree-six polynomial on a
triangle has 28 Bernstein coefficients.  `tri6Bernstein` fixes their order:

```text
(i,j) = (0,0),(0,1),...,(0,6),(1,0),...,(1,5),...,(6,0),
```

with third barycentric exponent `6-i-j`.  The coefficients include no
multinomial factor; `tri6Bernstein` inserts that factor explicitly.

Certificate files provide a literal `Fin 28 → ℚ`, prove its rational lower
bound by ordinary `decide`, and prove the polynomial/triangle identity by
`ring`.  `tri6Bernstein_rat_pos` then turns those two kernel-checked facts into
strict positivity.  There is no native evaluator and no external certificate
blob in the trusted path.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- Evaluation of the 28 total-degree-six triangular Bernstein coefficients.

The barycentric coordinates are `u`, `v`, and `1-u-v`. -/
def tri6Bernstein (c : Fin 28 → ℝ) (u v : ℝ) : ℝ :=
  let w := 1 - u - v
  c 0 * w ^ 6 +
  6 * c 1 * v * w ^ 5 +
  15 * c 2 * v ^ 2 * w ^ 4 +
  20 * c 3 * v ^ 3 * w ^ 3 +
  15 * c 4 * v ^ 4 * w ^ 2 +
  6 * c 5 * v ^ 5 * w +
  c 6 * v ^ 6 +
  6 * c 7 * u * w ^ 5 +
  30 * c 8 * u * v * w ^ 4 +
  60 * c 9 * u * v ^ 2 * w ^ 3 +
  60 * c 10 * u * v ^ 3 * w ^ 2 +
  30 * c 11 * u * v ^ 4 * w +
  6 * c 12 * u * v ^ 5 +
  15 * c 13 * u ^ 2 * w ^ 4 +
  60 * c 14 * u ^ 2 * v * w ^ 3 +
  90 * c 15 * u ^ 2 * v ^ 2 * w ^ 2 +
  60 * c 16 * u ^ 2 * v ^ 3 * w +
  15 * c 17 * u ^ 2 * v ^ 4 +
  20 * c 18 * u ^ 3 * w ^ 3 +
  60 * c 19 * u ^ 3 * v * w ^ 2 +
  60 * c 20 * u ^ 3 * v ^ 2 * w +
  20 * c 21 * u ^ 3 * v ^ 3 +
  15 * c 22 * u ^ 4 * w ^ 2 +
  30 * c 23 * u ^ 4 * v * w +
  15 * c 24 * u ^ 4 * v ^ 2 +
  6 * c 25 * u ^ 5 * w +
  6 * c 26 * u ^ 5 * v +
  c 27 * u ^ 6

/-- A nonnegative coefficient vector evaluates nonnegatively on the closed
standard triangle. -/
theorem tri6Bernstein_nonneg
    (c : Fin 28 → ℝ) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1)
    (hc : ∀ i, 0 ≤ c i) :
    0 ≤ tri6Bernstein c u v := by
  have hw : 0 ≤ 1 - u - v := by linarith
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  have hc3 := hc 3
  have hc4 := hc 4
  have hc5 := hc 5
  have hc6 := hc 6
  have hc7 := hc 7
  have hc8 := hc 8
  have hc9 := hc 9
  have hc10 := hc 10
  have hc11 := hc 11
  have hc12 := hc 12
  have hc13 := hc 13
  have hc14 := hc 14
  have hc15 := hc 15
  have hc16 := hc 16
  have hc17 := hc 17
  have hc18 := hc 18
  have hc19 := hc 19
  have hc20 := hc 20
  have hc21 := hc 21
  have hc22 := hc 22
  have hc23 := hc 23
  have hc24 := hc 24
  have hc25 := hc 25
  have hc26 := hc 26
  have hc27 := hc 27
  simp only [tri6Bernstein]
  positivity

/-- The degree-six triangular Bernstein basis is a partition of unity. -/
theorem tri6Bernstein_const (d u v : ℝ) :
    tri6Bernstein (fun _ => d) u v = d := by
  simp only [tri6Bernstein]
  ring

/-- A common positive lower bound for the 28 coefficients gives strict
positivity everywhere on the closed standard triangle. -/
theorem tri6Bernstein_pos_of_lower
    (c : Fin 28 → ℝ) (d u v : ℝ)
    (hd : 0 < d) (hc : ∀ i, d ≤ c i)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) :
    0 < tri6Bernstein c u v := by
  let e : Fin 28 → ℝ := fun i => c i - d
  have he : ∀ i, 0 ≤ e i := by
    intro i
    simp only [e]
    linarith only [hc i]
  have herest : 0 ≤ tri6Bernstein e u v :=
    tri6Bernstein_nonneg e u v hu hv huv he
  have hsplit :
      tri6Bernstein c u v =
        tri6Bernstein (fun _ => d) u v + tri6Bernstein e u v := by
    simp only [tri6Bernstein, e]
    ring
  rw [hsplit, tri6Bernstein_const]
  linarith

/-- Rational certificate wrapper.  In applications `hd` and `hc` are proved
by ordinary `decide`; `exact_mod_cast` is the only bridge to real arithmetic. -/
theorem tri6Bernstein_rat_pos
    (c : Fin 28 → ℚ) (d : ℚ) (u v : ℝ)
    (hd : 0 < d) (hc : ∀ i, d ≤ c i)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) :
    0 < tri6Bernstein (fun i => (c i : ℝ)) u v := by
  apply tri6Bernstein_pos_of_lower
      (fun i => (c i : ℝ)) (d : ℝ) u v
  · exact_mod_cast hd
  · intro i
    exact_mod_cast hc i
  · exact hu
  · exact hv
  · exact huv

/-! ## Degree ten

The direct, especially robust one-negative certificate uses degree ten.  It is
kept beside the smaller degree-six checker so the fallback and the compressed
endpoint proof share exactly the same trusted mechanism. -/

/-- Evaluation of the 66 total-degree-ten triangular Bernstein coefficients,
in the same lexicographic `(i,j)` order as `tri6Bernstein`. -/
def tri10Bernstein (c : Fin 66 → ℝ) (u v : ℝ) : ℝ :=
  let w := 1 - u - v
  c 0 * w ^ 10 +
  10 * c 1 * v * w ^ 9 +
  45 * c 2 * v ^ 2 * w ^ 8 +
  120 * c 3 * v ^ 3 * w ^ 7 +
  210 * c 4 * v ^ 4 * w ^ 6 +
  252 * c 5 * v ^ 5 * w ^ 5 +
  210 * c 6 * v ^ 6 * w ^ 4 +
  120 * c 7 * v ^ 7 * w ^ 3 +
  45 * c 8 * v ^ 8 * w ^ 2 +
  10 * c 9 * v ^ 9 * w +
  c 10 * v ^ 10 +
  10 * c 11 * u * w ^ 9 +
  90 * c 12 * u * v * w ^ 8 +
  360 * c 13 * u * v ^ 2 * w ^ 7 +
  840 * c 14 * u * v ^ 3 * w ^ 6 +
  1260 * c 15 * u * v ^ 4 * w ^ 5 +
  1260 * c 16 * u * v ^ 5 * w ^ 4 +
  840 * c 17 * u * v ^ 6 * w ^ 3 +
  360 * c 18 * u * v ^ 7 * w ^ 2 +
  90 * c 19 * u * v ^ 8 * w +
  10 * c 20 * u * v ^ 9 +
  45 * c 21 * u ^ 2 * w ^ 8 +
  360 * c 22 * u ^ 2 * v * w ^ 7 +
  1260 * c 23 * u ^ 2 * v ^ 2 * w ^ 6 +
  2520 * c 24 * u ^ 2 * v ^ 3 * w ^ 5 +
  3150 * c 25 * u ^ 2 * v ^ 4 * w ^ 4 +
  2520 * c 26 * u ^ 2 * v ^ 5 * w ^ 3 +
  1260 * c 27 * u ^ 2 * v ^ 6 * w ^ 2 +
  360 * c 28 * u ^ 2 * v ^ 7 * w +
  45 * c 29 * u ^ 2 * v ^ 8 +
  120 * c 30 * u ^ 3 * w ^ 7 +
  840 * c 31 * u ^ 3 * v * w ^ 6 +
  2520 * c 32 * u ^ 3 * v ^ 2 * w ^ 5 +
  4200 * c 33 * u ^ 3 * v ^ 3 * w ^ 4 +
  4200 * c 34 * u ^ 3 * v ^ 4 * w ^ 3 +
  2520 * c 35 * u ^ 3 * v ^ 5 * w ^ 2 +
  840 * c 36 * u ^ 3 * v ^ 6 * w +
  120 * c 37 * u ^ 3 * v ^ 7 +
  210 * c 38 * u ^ 4 * w ^ 6 +
  1260 * c 39 * u ^ 4 * v * w ^ 5 +
  3150 * c 40 * u ^ 4 * v ^ 2 * w ^ 4 +
  4200 * c 41 * u ^ 4 * v ^ 3 * w ^ 3 +
  3150 * c 42 * u ^ 4 * v ^ 4 * w ^ 2 +
  1260 * c 43 * u ^ 4 * v ^ 5 * w +
  210 * c 44 * u ^ 4 * v ^ 6 +
  252 * c 45 * u ^ 5 * w ^ 5 +
  1260 * c 46 * u ^ 5 * v * w ^ 4 +
  2520 * c 47 * u ^ 5 * v ^ 2 * w ^ 3 +
  2520 * c 48 * u ^ 5 * v ^ 3 * w ^ 2 +
  1260 * c 49 * u ^ 5 * v ^ 4 * w +
  252 * c 50 * u ^ 5 * v ^ 5 +
  210 * c 51 * u ^ 6 * w ^ 4 +
  840 * c 52 * u ^ 6 * v * w ^ 3 +
  1260 * c 53 * u ^ 6 * v ^ 2 * w ^ 2 +
  840 * c 54 * u ^ 6 * v ^ 3 * w +
  210 * c 55 * u ^ 6 * v ^ 4 +
  120 * c 56 * u ^ 7 * w ^ 3 +
  360 * c 57 * u ^ 7 * v * w ^ 2 +
  360 * c 58 * u ^ 7 * v ^ 2 * w +
  120 * c 59 * u ^ 7 * v ^ 3 +
  45 * c 60 * u ^ 8 * w ^ 2 +
  90 * c 61 * u ^ 8 * v * w +
  45 * c 62 * u ^ 8 * v ^ 2 +
  10 * c 63 * u ^ 9 * w +
  10 * c 64 * u ^ 9 * v +
  c 65 * u ^ 10

theorem tri10Bernstein_nonneg
    (c : Fin 66 → ℝ) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1)
    (hc : ∀ i, 0 ≤ c i) :
    0 ≤ tri10Bernstein c u v := by
  have hw : 0 ≤ 1 - u - v := by linarith
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  have hc3 := hc 3
  have hc4 := hc 4
  have hc5 := hc 5
  have hc6 := hc 6
  have hc7 := hc 7
  have hc8 := hc 8
  have hc9 := hc 9
  have hc10 := hc 10
  have hc11 := hc 11
  have hc12 := hc 12
  have hc13 := hc 13
  have hc14 := hc 14
  have hc15 := hc 15
  have hc16 := hc 16
  have hc17 := hc 17
  have hc18 := hc 18
  have hc19 := hc 19
  have hc20 := hc 20
  have hc21 := hc 21
  have hc22 := hc 22
  have hc23 := hc 23
  have hc24 := hc 24
  have hc25 := hc 25
  have hc26 := hc 26
  have hc27 := hc 27
  have hc28 := hc 28
  have hc29 := hc 29
  have hc30 := hc 30
  have hc31 := hc 31
  have hc32 := hc 32
  have hc33 := hc 33
  have hc34 := hc 34
  have hc35 := hc 35
  have hc36 := hc 36
  have hc37 := hc 37
  have hc38 := hc 38
  have hc39 := hc 39
  have hc40 := hc 40
  have hc41 := hc 41
  have hc42 := hc 42
  have hc43 := hc 43
  have hc44 := hc 44
  have hc45 := hc 45
  have hc46 := hc 46
  have hc47 := hc 47
  have hc48 := hc 48
  have hc49 := hc 49
  have hc50 := hc 50
  have hc51 := hc 51
  have hc52 := hc 52
  have hc53 := hc 53
  have hc54 := hc 54
  have hc55 := hc 55
  have hc56 := hc 56
  have hc57 := hc 57
  have hc58 := hc 58
  have hc59 := hc 59
  have hc60 := hc 60
  have hc61 := hc 61
  have hc62 := hc 62
  have hc63 := hc 63
  have hc64 := hc 64
  have hc65 := hc 65
  simp only [tri10Bernstein]
  positivity

theorem tri10Bernstein_const (d u v : ℝ) :
    tri10Bernstein (fun _ => d) u v = d := by
  simp only [tri10Bernstein]
  ring

theorem tri10Bernstein_pos_of_lower
    (c : Fin 66 → ℝ) (d u v : ℝ)
    (hd : 0 < d) (hc : ∀ i, d ≤ c i)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) :
    0 < tri10Bernstein c u v := by
  let e : Fin 66 → ℝ := fun i => c i - d
  have he : ∀ i, 0 ≤ e i := by
    intro i
    simp only [e]
    linarith only [hc i]
  have herest : 0 ≤ tri10Bernstein e u v :=
    tri10Bernstein_nonneg e u v hu hv huv he
  have hsplit :
      tri10Bernstein c u v =
        tri10Bernstein (fun _ => d) u v + tri10Bernstein e u v := by
    simp only [tri10Bernstein, e]
    ring
  rw [hsplit, tri10Bernstein_const]
  linarith

theorem tri10Bernstein_rat_pos
    (c : Fin 66 → ℚ) (d : ℚ) (u v : ℝ)
    (hd : 0 < d) (hc : ∀ i, d ≤ c i)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) :
    0 < tri10Bernstein (fun i => (c i : ℝ)) u v := by
  apply tri10Bernstein_pos_of_lower
      (fun i => (c i : ℝ)) (d : ℝ) u v
  · exact_mod_cast hd
  · intro i
    exact_mod_cast hc i
  · exact hu
  · exact hv
  · exact huv

end HeilbronnChallenge.N7Upper
