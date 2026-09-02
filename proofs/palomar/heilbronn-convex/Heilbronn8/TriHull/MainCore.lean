import Heilbronn8.TriHull.Core

namespace Heilbronn8.TriHull

abbrev Point := ℝ × ℝ

/-- Every triangle on distinct labels has ordinary area at least one. -/
def AllTrianglesMinAreaOne {n : ℕ} (v : Fin n → Point) : Prop :=
  ∀ ⦃i j k : Fin n⦄, i ≠ j → i ≠ k → j ≠ k →
    2 ≤ |sig (v i) (v j) (v k)|

lemma AllTrianglesMinAreaOne.comp {m n : ℕ} {v : Fin n → Point}
    (h : AllTrianglesMinAreaOne v) (e : Fin m → Fin n)
    (he : Function.Injective e) :
    AllTrianglesMinAreaOne (v ∘ e) := by
  intro i j k hij hik hjk
  exact h (fun heq => hij (he heq)) (fun heq => hik (he heq))
    (fun heq => hjk (he heq))

lemma AllTrianglesMinAreaOne.sig_ne_zero {n : ℕ} {v : Fin n → Point}
    (h : AllTrianglesMinAreaOne v) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    sig (v i) (v j) (v k) ≠ 0 := by
  have hmin := h hij hik hjk
  intro hz
  rw [hz, abs_zero] at hmin
  norm_num at hmin

/--
The exact twenty lower bounds used by the two WP2 surcharge statements.
This is definitionally the SixPointMinAreaOne predicate in the WP2 file,
but is local here so Main imports only Core.
-/
def SixPointMinimum (A B C P Q R : Point) : Prop :=
  2 ≤ |sig A B C| ∧
  2 ≤ |sig A B P| ∧
  2 ≤ |sig A B Q| ∧
  2 ≤ |sig A B R| ∧
  2 ≤ |sig A C P| ∧
  2 ≤ |sig A C Q| ∧
  2 ≤ |sig A C R| ∧
  2 ≤ |sig A P Q| ∧
  2 ≤ |sig A P R| ∧
  2 ≤ |sig A Q R| ∧
  2 ≤ |sig B C P| ∧
  2 ≤ |sig B C Q| ∧
  2 ≤ |sig B C R| ∧
  2 ≤ |sig B P Q| ∧
  2 ≤ |sig B P R| ∧
  2 ≤ |sig B Q R| ∧
  2 ≤ |sig C P Q| ∧
  2 ≤ |sig C P R| ∧
  2 ≤ |sig C Q R| ∧
  2 ≤ |sig P Q R|

/-- Exact statement of TH8 Lemma 2(1), supplied by WP2. -/
def Surcharge1Statement : Prop :=
  ∀ {A B C P Q R : Point},
    0 < sig A B C →
    InTriStrict P A B C →
    InTriStrict Q P B C →
    InTriStrict R P C A →
    SixPointMinimum A B C P Q R →
    (17 : ℝ) / 2 ≤ sig A B C / 2

/-- Exact statement of TH8 Lemma 2(2), supplied by WP2. -/
def Surcharge2Statement : Prop :=
  ∀ {A B C P Q R : Point},
    0 < sig A B C →
    InTriStrict P A B C →
    InTriStrict Q P B C →
    InTriStrict R P C A →
    SixPointMinimum A B C P Q R →
    (3 : ℝ) ≤ sig P A B / 2 →
    (21 : ℝ) / 2 ≤ sig A B C / 2

private lemma allTrianglesMinAreaOne_five {v : Fin 5 → Point}
    (h : AllTrianglesMinAreaOne v) :
    FivePointMinAreaOne (v 0) (v 1) (v 2) (v 3) (v 4) := by
  refine ⟨h (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide),
    h (i := 3) (j := 1) (k := 2) (by decide) (by decide) (by decide),
    h (i := 3) (j := 2) (k := 0) (by decide) (by decide) (by decide),
    h (i := 3) (j := 0) (k := 1) (by decide) (by decide) (by decide),
    h (i := 4) (j := 1) (k := 2) (by decide) (by decide) (by decide),
    h (i := 4) (j := 2) (k := 0) (by decide) (by decide) (by decide),
    h (i := 4) (j := 0) (k := 1) (by decide) (by decide) (by decide),
    h (i := 0) (j := 3) (k := 4) (by decide) (by decide) (by decide),
    h (i := 1) (j := 3) (k := 4) (by decide) (by decide) (by decide),
    h (i := 2) (j := 3) (k := 4) (by decide) (by decide) (by decide)⟩

private lemma allTrianglesMinAreaOne_six {v : Fin 6 → Point}
    (h : AllTrianglesMinAreaOne v) :
    SixPointMinimum (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by
  refine ⟨h (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide),
    h (i := 0) (j := 1) (k := 3) (by decide) (by decide) (by decide),
    h (i := 0) (j := 1) (k := 4) (by decide) (by decide) (by decide),
    h (i := 0) (j := 1) (k := 5) (by decide) (by decide) (by decide),
    h (i := 0) (j := 2) (k := 3) (by decide) (by decide) (by decide),
    h (i := 0) (j := 2) (k := 4) (by decide) (by decide) (by decide),
    h (i := 0) (j := 2) (k := 5) (by decide) (by decide) (by decide),
    h (i := 0) (j := 3) (k := 4) (by decide) (by decide) (by decide),
    h (i := 0) (j := 3) (k := 5) (by decide) (by decide) (by decide),
    h (i := 0) (j := 4) (k := 5) (by decide) (by decide) (by decide),
    h (i := 1) (j := 2) (k := 3) (by decide) (by decide) (by decide),
    h (i := 1) (j := 2) (k := 4) (by decide) (by decide) (by decide),
    h (i := 1) (j := 2) (k := 5) (by decide) (by decide) (by decide),
    h (i := 1) (j := 3) (k := 4) (by decide) (by decide) (by decide),
    h (i := 1) (j := 3) (k := 5) (by decide) (by decide) (by decide),
    h (i := 1) (j := 4) (k := 5) (by decide) (by decide) (by decide),
    h (i := 2) (j := 3) (k := 4) (by decide) (by decide) (by decide),
    h (i := 2) (j := 3) (k := 5) (by decide) (by decide) (by decide),
    h (i := 2) (j := 4) (k := 5) (by decide) (by decide) (by decide),
    h (i := 3) (j := 4) (k := 5) (by decide) (by decide) (by decide)⟩

lemma MainAux.empty_bound {n : ℕ} {v : Fin n → Point}
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 3 → Fin n)
    (he : Function.Injective e)
    (hpos : 0 < sig (v (e 0)) (v (e 1)) (v (e 2))) :
    1 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  have h := hmin.comp e he
  have ht := h (i := 0) (j := 1) (k := 2)
    (by decide) (by decide) (by decide)
  change 2 ≤ |sig (v (e 0)) (v (e 1)) (v (e 2))| at ht
  rw [abs_of_pos hpos] at ht
  linarith

lemma MainAux.one_point_bound {n : ℕ} {v : Fin n → Point}
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 4 → Fin n)
    (he : Function.Injective e)
    (hpos : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2))) :
    3 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  have hw := hmin.comp e he
  obtain ⟨hPBC, hPCA, hPAB⟩ := inTriStrict_fan_pos hpos hP
  have h1 := hw (i := 3) (j := 1) (k := 2)
    (by decide) (by decide) (by decide)
  have h2 := hw (i := 3) (j := 2) (k := 0)
    (by decide) (by decide) (by decide)
  have h3 := hw (i := 3) (j := 0) (k := 1)
    (by decide) (by decide) (by decide)
  change 2 ≤ |sig (v (e 3)) (v (e 1)) (v (e 2))| at h1
  change 2 ≤ |sig (v (e 3)) (v (e 2)) (v (e 0))| at h2
  change 2 ≤ |sig (v (e 3)) (v (e 0)) (v (e 1))| at h3
  rw [abs_of_pos hPBC] at h1
  rw [abs_of_pos hPCA] at h2
  rw [abs_of_pos hPAB] at h3
  nlinarith [fan_sum (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2))]

private lemma surcharge1_bound {n : ℕ} {v : Fin n → Point}
    (surcharge1 : Surcharge1Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 6 → Fin n)
    (he : Function.Injective e)
    (hpos : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 3)) (v (e 2)) (v (e 0))) :
    (17 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  exact surcharge1 hpos hP hQ hR
    (allTrianglesMinAreaOne_six (hmin.comp e he))

private lemma surcharge2_bound {n : ℕ} {v : Fin n → Point}
    (surcharge2 : Surcharge2Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 6 → Fin n)
    (he : Function.Injective e)
    (hpos : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 3)) (v (e 2)) (v (e 0)))
    (hgamma : (3 : ℝ) ≤ sig (v (e 3)) (v (e 0)) (v (e 1)) / 2) :
    (21 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  exact surcharge2 hpos hP hQ hR
    (allTrianglesMinAreaOne_six (hmin.comp e he)) hgamma

private lemma bary_min_first {A B C P Q : Point}
    {x y z u v w : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hu : 0 < u) (_hv : 0 < v) (_hw : 0 < w)
    (hxyz : x + y + z = 1) (huvw : u + v + w = 1)
    (hP : P = x • A + y • B + z • C)
    (hQ : Q = u • A + v • B + w • C)
    (hAB : u / x < v / y) (hAC : u / x < w / z) :
    InTriStrict Q P B C := by
  let t : ℝ := u / x
  let s : ℝ := v - t * y
  let r : ℝ := w - t * z
  have ht : 0 < t := div_pos hu hx
  have hs : 0 < s := by
    dsimp [s]
    exact sub_pos.mpr ((lt_div_iff₀ hy).mp (by simpa [t] using hAB))
  have hr : 0 < r := by
    dsimp [r]
    exact sub_pos.mpr ((lt_div_iff₀ hz).mp (by simpa [t] using hAC))
  have htx : t * x = u := by
    dsimp [t]
    exact div_mul_cancel₀ u hx.ne'
  have hsum : t + s + r = 1 := by
    dsimp [s, r]
    calc
      t + (v - t * y) + (w - t * z) =
          u + v + w + t * (1 - (x + y + z)) := by nlinarith
      _ = 1 := by rw [hxyz, huvw]; ring
  refine ⟨t, s, r, ht, hs, hr, hsum, ?_⟩
  rw [hP, hQ]
  dsimp [s, r]
  rw [← htx]
  module

private lemma ratio_ne_ab {A B C P Q : Point}
    {x y z u v w : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hxyz : x + y + z = 1) (huvw : u + v + w = 1)
    (hP : P = x • A + y • B + z • C)
    (hQ : Q = u • A + v • B + w • C)
    (hne : sig P C Q ≠ 0) :
    u / x ≠ v / y := by
  intro hab
  let t : ℝ := u / x
  have htx : t * x = u := by
    dsimp [t]
    exact div_mul_cancel₀ u hx.ne'
  have hty : t * y = v := by
    have ht := congrArg (fun q : ℝ => q * y) hab
    dsimp [t] at ht ⊢
    rw [div_mul_cancel₀ v hy.ne'] at ht
    exact ht
  have htxyz : t * x + t * y + t * z = t := by
    linear_combination t * hxyz
  have htz : t * z + (1 - t) = w := by
    linarith
  apply hne
  rw [hP, hQ]
  rw [← htx, ← hty, ← htz]
  simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, smul_eq_mul]
  ring

lemma strict_fan_partition {A B C P Q : Point}
    (hP : InTriStrict P A B C) (hQ : InTriStrict Q A B C)
    (hPAQ : sig P A Q ≠ 0) (hPBQ : sig P B Q ≠ 0)
    (hPCQ : sig P C Q ≠ 0) :
    InTriStrict Q P B C ∨
      InTriStrict Q P C A ∨
      InTriStrict Q P A B := by
  obtain ⟨x, y, z, hx, hy, hz, hxyz, hPe⟩ := hP
  obtain ⟨u, v, w, hu, hv, hw, huvw, hQe⟩ := hQ
  have hab : u / x ≠ v / y :=
    ratio_ne_ab hx hy hxyz huvw hPe hQe hPCQ
  have hac : u / x ≠ w / z := by
    exact ratio_ne_ab (A := A) (B := C) (C := B) (P := P) (Q := Q)
      (x := x) (y := z) (z := y) (u := u) (v := w) (w := v)
      hx hz (by linarith [hxyz]) (by linarith [huvw])
      (by rw [hPe]; module) (by rw [hQe]; module) hPBQ
  have hbc : v / y ≠ w / z := by
    exact ratio_ne_ab (A := B) (B := C) (C := A) (P := P) (Q := Q)
      (x := y) (y := z) (z := x) (u := v) (v := w) (w := u)
      hy hz (by linarith [hxyz]) (by linarith [huvw])
      (by rw [hPe]; module) (by rw [hQe]; module) hPAQ
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hac with hac | hca
    · exact Or.inl (bary_min_first hx hy hz hu hv hw hxyz huvw
        hPe hQe hab hac)
    · exact Or.inr (Or.inr (bary_min_first
        (A := C) (B := A) (C := B)
        hz hx hy hw hu hv
        (by linarith [hxyz]) (by linarith [huvw])
        (by rw [hPe]; module) (by rw [hQe]; module)
        hca (lt_trans hca hab)))
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact Or.inr (Or.inl (bary_min_first
        (A := B) (B := C) (C := A)
        hy hz hx hv hw hu
        (by linarith [hxyz]) (by linarith [huvw])
        (by rw [hPe]; module) (by rw [hQe]; module)
        hbc hba))
    · exact Or.inr (Or.inr (bary_min_first
        (A := C) (B := A) (C := B)
        hz hx hy hw hu hv
        (by linarith [hxyz]) (by linarith [huvw])
        (by rw [hPe]; module) (by rw [hQe]; module)
        (lt_trans hcb hba) hcb))

def InFanCell (Q P A B C : Point) : Fin 3 → Prop :=
  ![InTriStrict Q P B C, InTriStrict Q P C A, InTriStrict Q P A B]

private lemma fanCell_exists {A B C P Q : Point}
    (hP : InTriStrict P A B C) (hQ : InTriStrict Q A B C)
    (hPAQ : sig P A Q ≠ 0) (hPBQ : sig P B Q ≠ 0)
    (hPCQ : sig P C Q ≠ 0) :
    ∃ i : Fin 3, InFanCell Q P A B C i := by
  rcases strict_fan_partition hP hQ hPAQ hPBQ hPCQ with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

lemma MainAux.fanCell_exists_reindex {n : ℕ} {v : Fin n → Point}
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 5 → Fin n)
    (he : Function.Injective e)
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 0)) (v (e 1)) (v (e 2))) :
    ∃ i : Fin 3,
      InFanCell (v (e 4)) (v (e 3))
        (v (e 0)) (v (e 1)) (v (e 2)) i := by
  have hlocal := hmin.comp e he
  apply fanCell_exists hP hQ
  · change sig ((v ∘ e) 3) ((v ∘ e) 0) ((v ∘ e) 4) ≠ 0
    exact hlocal.sig_ne_zero (by decide) (by decide) (by decide)
  · change sig ((v ∘ e) 3) ((v ∘ e) 1) ((v ∘ e) 4) ≠ 0
    exact hlocal.sig_ne_zero (by decide) (by decide) (by decide)
  · change sig ((v ∘ e) 3) ((v ∘ e) 2) ((v ∘ e) 4) ≠ 0
    exact hlocal.sig_ne_zero (by decide) (by decide) (by decide)

lemma MainAux.inTriStrict_rotate {P A B C : Point}
    (h : InTriStrict P A B C) : InTriStrict P B C A := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, rfl⟩ := h
  exact ⟨y, z, x, hy, hz, hx, by linarith, by module⟩

lemma MainAux.three_halves_le_sqrt_three :
    (3 : ℝ) / 2 ≤ Real.sqrt 3 := by
  nlinarith [sqrt_three_mul_self, sqrt_three_nonneg]

lemma MainAux.two_point_bound {n : ℕ} {v : Fin n → Point}
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 5 → Fin n)
    (he : Function.Injective e)
    (hpos : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 0)) (v (e 1)) (v (e 2))) :
    4 + 2 * Real.sqrt 3 ≤
      sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  obtain ⟨c, hc⟩ := MainAux.fanCell_exists_reindex hmin e he hP hQ
  fin_cases c
  all_goals simp [InFanCell] at hc
  · exact th8_lemma1 hpos hP hc
      (allTrianglesMinAreaOne_five (hmin.comp e he))
  · have hpos' : 0 < sig (v (e 1)) (v (e 2)) (v (e 0)) := by
      rw [← sig_rotate (v (e 0)) (v (e 1)) (v (e 2))]
      exact hpos
    have hb := th8_lemma1 hpos' (MainAux.inTriStrict_rotate hP) hc
      (allTrianglesMinAreaOne_five
        (hmin.comp (e ∘ ![1, 2, 0, 3, 4]) (he.comp (by decide))))
    rw [sig_rotate (v (e 0)) (v (e 1)) (v (e 2))]
    simpa using hb
  · have hpos' : 0 < sig (v (e 2)) (v (e 0)) (v (e 1)) := by
      rw [sig_rotate (v (e 2)) (v (e 0)) (v (e 1))]
      exact hpos
    have hb := th8_lemma1 hpos'
      (MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP)) hc
      (allTrianglesMinAreaOne_five
        (hmin.comp (e ∘ ![2, 0, 1, 3, 4]) (he.comp (by decide))))
    rw [← sig_rotate (v (e 2)) (v (e 0)) (v (e 1))]
    simpa using hb

/-- TH8 Lemma 3: a triangle with three selected interior points. -/
theorem th8_lemma3
    (surcharge1 : Surcharge1Statement)
    (v : Fin 6 → Point)
    (hABC : 0 < sig (v 0) (v 1) (v 2))
    (hP : InTriStrict (v 3) (v 0) (v 1) (v 2))
    (hQ : InTriStrict (v 4) (v 0) (v 1) (v 2))
    (hR : InTriStrict (v 5) (v 0) (v 1) (v 2))
    (hmin : AllTrianglesMinAreaOne v) :
    (17 : ℝ) / 2 ≤ sig (v 0) (v 1) (v 2) / 2 := by
  let A := v 0
  let B := v 1
  let C := v 2
  let P := v 3
  let Q := v 4
  let R := v 5
  obtain ⟨hPBC, hPCA, hPAB⟩ := inTriStrict_fan_pos hABC hP
  obtain ⟨q, hq⟩ :=
    MainAux.fanCell_exists_reindex hmin ![0, 1, 2, 3, 4] (by decide) hP hQ
  obtain ⟨r, hr⟩ :=
    MainAux.fanCell_exists_reindex hmin ![0, 1, 2, 3, 5] (by decide) hP hR
  change (17 : ℝ) / 2 ≤ sig A B C / 2
  fin_cases q <;> fin_cases r
  all_goals simp [InFanCell] at hq hr
  · have htwo := MainAux.two_point_bound hmin ![3, 1, 2, 4, 5] (by decide)
      hPBC (by simpa using hq) (by simpa using hr)
    have he1 := MainAux.empty_bound hmin ![3, 2, 0] (by decide) hPCA
    have he2 := MainAux.empty_bound hmin ![3, 0, 1] (by decide) hPAB
    have hfan := fan_sum P A B C
    dsimp [P, A, B, C] at htwo he1 he2 hfan ⊢
    nlinarith [hfan, MainAux.three_halves_le_sqrt_three]
  · have hb := surcharge1_bound surcharge1 hmin ![0, 1, 2, 3, 4, 5]
      (by decide) hABC hP (by simpa using hq) (by simpa using hr)
    simpa using hb
  · have hpos' : 0 < sig C A B := by
      rw [sig_rotate C A B]
      exact hABC
    have hb := surcharge1_bound surcharge1 hmin ![2, 0, 1, 3, 5, 4]
      (by decide) (by simpa using hpos')
      (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
      (by simpa using hr) (by simpa using hq)
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb := surcharge1_bound surcharge1 hmin ![0, 1, 2, 3, 5, 4]
      (by decide) hABC hP (by simpa using hr) (by simpa using hq)
    simpa using hb
  · have htwo := MainAux.two_point_bound hmin ![3, 2, 0, 4, 5] (by decide)
      hPCA (by simpa using hq) (by simpa using hr)
    have he1 := MainAux.empty_bound hmin ![3, 1, 2] (by decide) hPBC
    have he2 := MainAux.empty_bound hmin ![3, 0, 1] (by decide) hPAB
    have hfan := fan_sum P A B C
    dsimp [P, A, B, C] at htwo he1 he2 hfan ⊢
    nlinarith [hfan, MainAux.three_halves_le_sqrt_three]
  · have hpos' : 0 < sig B C A := by
      rw [← sig_rotate A B C]
      exact hABC
    have hb := surcharge1_bound surcharge1 hmin ![1, 2, 0, 3, 4, 5]
      (by decide) (by simpa using hpos')
      (by simpa using MainAux.inTriStrict_rotate hP)
      (by simpa using hq) (by simpa using hr)
    rw [sig_rotate A B C]
    simpa using hb
  · have hpos' : 0 < sig C A B := by
      rw [sig_rotate C A B]
      exact hABC
    have hb := surcharge1_bound surcharge1 hmin ![2, 0, 1, 3, 4, 5]
      (by decide) (by simpa using hpos')
      (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
      (by simpa using hq) (by simpa using hr)
    rw [← sig_rotate C A B]
    simpa using hb
  · have hpos' : 0 < sig B C A := by
      rw [← sig_rotate A B C]
      exact hABC
    have hb := surcharge1_bound surcharge1 hmin ![1, 2, 0, 3, 5, 4]
      (by decide) (by simpa using hpos')
      (by simpa using MainAux.inTriStrict_rotate hP)
      (by simpa using hr) (by simpa using hq)
    rw [sig_rotate A B C]
    simpa using hb
  · have htwo := MainAux.two_point_bound hmin ![3, 0, 1, 4, 5] (by decide)
      hPAB (by simpa using hq) (by simpa using hr)
    have he1 := MainAux.empty_bound hmin ![3, 1, 2] (by decide) hPBC
    have he2 := MainAux.empty_bound hmin ![3, 2, 0] (by decide) hPCA
    have hfan := fan_sum P A B C
    dsimp [P, A, B, C] at htwo he1 he2 hfan ⊢
    nlinarith [hfan, MainAux.three_halves_le_sqrt_three]

lemma MainAux.lemma3_bound {n : ℕ} {v : Fin n → Point}
    (surcharge1 : Surcharge1Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 6 → Fin n)
    (he : Function.Injective e)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 0)) (v (e 1)) (v (e 2))) :
    (17 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  exact th8_lemma3 surcharge1 (v ∘ e) hABC hP hQ hR (hmin.comp e he)

private lemma lemma4_300 {n : ℕ} {v : Fin n → Point}
    (surcharge1 : Surcharge1Statement)
    (_surcharge2 : Surcharge2Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 7 → Fin n)
    (he : Function.Injective e)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hS : InTriStrict (v (e 6)) (v (e 3)) (v (e 1)) (v (e 2))) :
    (21 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  obtain ⟨hPBC, hPCA, hPAB⟩ := inTriStrict_fan_pos hABC hP
  have hthree := MainAux.lemma3_bound surcharge1 hmin (e ∘ ![3, 1, 2, 4, 5, 6])
    (he.comp (by decide)) hPBC
    (by simpa using hQ) (by simpa using hR) (by simpa using hS)
  have he1 := MainAux.empty_bound hmin (e ∘ ![3, 2, 0])
    (he.comp (by decide)) hPCA
  have he2 := MainAux.empty_bound hmin (e ∘ ![3, 0, 1])
    (he.comp (by decide)) hPAB
  simp at hthree he1 he2
  nlinarith [fan_sum (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2))]

private lemma lemma4_210 {n : ℕ} {v : Fin n → Point}
    (_surcharge1 : Surcharge1Statement)
    (_surcharge2 : Surcharge2Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 7 → Fin n)
    (he : Function.Injective e)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hS : InTriStrict (v (e 6)) (v (e 3)) (v (e 2)) (v (e 0))) :
    (21 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  obtain ⟨hPBC, hPCA, hPAB⟩ := inTriStrict_fan_pos hABC hP
  have htwo := MainAux.two_point_bound hmin (e ∘ ![3, 1, 2, 4, 5])
    (he.comp (by decide)) hPBC
    (by simpa using hQ) (by simpa using hR)
  have hone := MainAux.one_point_bound hmin (e ∘ ![3, 2, 0, 6])
    (he.comp (by decide)) hPCA (by simpa using hS)
  have hempty := MainAux.empty_bound hmin (e ∘ ![3, 0, 1])
    (he.comp (by decide)) hPAB
  simp at htwo hone hempty
  nlinarith [fan_sum (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)),
    MainAux.three_halves_le_sqrt_three]

private lemma lemma4_201 {n : ℕ} {v : Fin n → Point}
    (_surcharge1 : Surcharge1Statement)
    (_surcharge2 : Surcharge2Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 7 → Fin n)
    (he : Function.Injective e)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hS : InTriStrict (v (e 6)) (v (e 3)) (v (e 0)) (v (e 1))) :
    (21 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  obtain ⟨hPBC, hPCA, hPAB⟩ := inTriStrict_fan_pos hABC hP
  have htwo := MainAux.two_point_bound hmin (e ∘ ![3, 1, 2, 4, 5])
    (he.comp (by decide)) hPBC
    (by simpa using hQ) (by simpa using hR)
  have hone := MainAux.one_point_bound hmin (e ∘ ![3, 0, 1, 6])
    (he.comp (by decide)) hPAB (by simpa using hS)
  have hempty := MainAux.empty_bound hmin (e ∘ ![3, 2, 0])
    (he.comp (by decide)) hPCA
  simp at htwo hone hempty
  nlinarith [fan_sum (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)),
    MainAux.three_halves_le_sqrt_three]

private lemma lemma4_111 {n : ℕ} {v : Fin n → Point}
    (_surcharge1 : Surcharge1Statement)
    (surcharge2 : Surcharge2Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 7 → Fin n)
    (he : Function.Injective e)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 3)) (v (e 2)) (v (e 0)))
    (hS : InTriStrict (v (e 6)) (v (e 3)) (v (e 0)) (v (e 1))) :
    (21 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  have hgamma := MainAux.one_point_bound hmin (e ∘ ![3, 0, 1, 6])
    (he.comp (by decide)) (inTriStrict_fan_pos hABC hP).2.2
    (by simpa using hS)
  have hb := surcharge2_bound surcharge2 hmin
    (e ∘ ![0, 1, 2, 3, 4, 5]) (he.comp (by decide))
    (by simpa using hABC) (by simpa using hP)
    (by simpa using hQ) (by simpa using hR) (by simpa using hgamma)
  simpa using hb

/-- TH8 Lemma 4: a triangle with four selected interior points. -/
theorem th8_lemma4
    (surcharge1 : Surcharge1Statement)
    (surcharge2 : Surcharge2Statement)
    (v : Fin 7 → Point)
    (hABC : 0 < sig (v 0) (v 1) (v 2))
    (hP : InTriStrict (v 3) (v 0) (v 1) (v 2))
    (hQ : InTriStrict (v 4) (v 0) (v 1) (v 2))
    (hR : InTriStrict (v 5) (v 0) (v 1) (v 2))
    (hS : InTriStrict (v 6) (v 0) (v 1) (v 2))
    (hmin : AllTrianglesMinAreaOne v) :
    (21 : ℝ) / 2 ≤ sig (v 0) (v 1) (v 2) / 2 := by
  let A := v 0
  let B := v 1
  let C := v 2
  let P := v 3
  let Q := v 4
  let R := v 5
  let S := v 6
  obtain ⟨q, hq⟩ :=
    MainAux.fanCell_exists_reindex hmin ![0, 1, 2, 3, 4] (by decide) hP hQ
  obtain ⟨r, hr⟩ :=
    MainAux.fanCell_exists_reindex hmin ![0, 1, 2, 3, 5] (by decide) hP hR
  obtain ⟨s, hs⟩ :=
    MainAux.fanCell_exists_reindex hmin ![0, 1, 2, 3, 6] (by decide) hP hS
  change (21 : ℝ) / 2 ≤ sig A B C / 2
  fin_cases q <;> fin_cases r <;> fin_cases s
  all_goals simp [InFanCell] at hq hr hs
  · have hb :=
      lemma4_300 surcharge1 surcharge2 hmin ![0,1,2,3,4,5,6] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs)
    simpa using hb
  · have hb :=
      lemma4_210 surcharge1 surcharge2 hmin ![0,1,2,3,4,5,6] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs)
    simpa using hb
  · have hb :=
      lemma4_201 surcharge1 surcharge2 hmin ![0,1,2,3,4,5,6] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs)
    simpa using hb
  · have hb :=
      lemma4_210 surcharge1 surcharge2 hmin ![0,1,2,3,4,6,5] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hs) (by simpa using hr)
    simpa using hb
  · have hb :=
      lemma4_201 surcharge1 surcharge2 hmin ![1,2,0,3,5,6,4] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hr) (by simpa using hs) (by simpa using hq)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma4_111 surcharge1 surcharge2 hmin ![0,1,2,3,4,5,6] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs)
    simpa using hb
  · have hb :=
      lemma4_201 surcharge1 surcharge2 hmin ![0,1,2,3,4,6,5] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hs) (by simpa using hr)
    simpa using hb
  · have hb :=
      lemma4_111 surcharge1 surcharge2 hmin ![0,1,2,3,4,6,5] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hs) (by simpa using hr)
    simpa using hb
  · have hb :=
      lemma4_210 surcharge1 surcharge2 hmin ![2,0,1,3,5,6,4] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hr) (by simpa using hs) (by simpa using hq)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma4_210 surcharge1 surcharge2 hmin ![0,1,2,3,5,6,4] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hr) (by simpa using hs) (by simpa using hq)
    simpa using hb
  · have hb :=
      lemma4_201 surcharge1 surcharge2 hmin ![1,2,0,3,4,6,5] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hs) (by simpa using hr)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma4_111 surcharge1 surcharge2 hmin ![0,1,2,3,5,4,6] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hr) (by simpa using hq) (by simpa using hs)
    simpa using hb
  · have hb :=
      lemma4_201 surcharge1 surcharge2 hmin ![1,2,0,3,4,5,6] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma4_300 surcharge1 surcharge2 hmin ![1,2,0,3,4,5,6] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma4_210 surcharge1 surcharge2 hmin ![1,2,0,3,4,5,6] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma4_111 surcharge1 surcharge2 hmin ![0,1,2,3,6,4,5] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hs) (by simpa using hq) (by simpa using hr)
    simpa using hb
  · have hb :=
      lemma4_210 surcharge1 surcharge2 hmin ![1,2,0,3,4,6,5] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hs) (by simpa using hr)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma4_201 surcharge1 surcharge2 hmin ![2,0,1,3,5,6,4] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hr) (by simpa using hs) (by simpa using hq)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma4_201 surcharge1 surcharge2 hmin ![0,1,2,3,5,6,4] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hr) (by simpa using hs) (by simpa using hq)
    simpa using hb
  · have hb :=
      lemma4_111 surcharge1 surcharge2 hmin ![0,1,2,3,5,6,4] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hr) (by simpa using hs) (by simpa using hq)
    simpa using hb
  · have hb :=
      lemma4_210 surcharge1 surcharge2 hmin ![2,0,1,3,4,6,5] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hs) (by simpa using hr)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma4_111 surcharge1 surcharge2 hmin ![0,1,2,3,6,5,4] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hs) (by simpa using hr) (by simpa using hq)
    simpa using hb
  · have hb :=
      lemma4_210 surcharge1 surcharge2 hmin ![1,2,0,3,5,6,4] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hr) (by simpa using hs) (by simpa using hq)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma4_201 surcharge1 surcharge2 hmin ![2,0,1,3,4,6,5] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hs) (by simpa using hr)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma4_210 surcharge1 surcharge2 hmin ![2,0,1,3,4,5,6] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hr) (by simpa using hs)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma4_201 surcharge1 surcharge2 hmin ![2,0,1,3,4,5,6] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hr) (by simpa using hs)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma4_300 surcharge1 surcharge2 hmin ![2,0,1,3,4,5,6] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hr) (by simpa using hs)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb


end Heilbronn8.TriHull
