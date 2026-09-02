import Heilbronn8.TriHull.MainCore

namespace Heilbronn8.TriHull

private lemma lemma4_bound {n : ℕ} {v : Fin n → Point}
    (surcharge1 : Surcharge1Statement)
    (surcharge2 : Surcharge2Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 7 → Fin n)
    (he : Function.Injective e)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hS : InTriStrict (v (e 6)) (v (e 0)) (v (e 1)) (v (e 2))) :
    (21 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  exact th8_lemma4 surcharge1 surcharge2 (v ∘ e)
    hABC hP hQ hR hS (hmin.comp e he)

private lemma lemma5_400 {n : ℕ} {v : Fin n → Point}
    (surcharge1 : Surcharge1Statement)
    (surcharge2 : Surcharge2Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 8 → Fin n)
    (he : Function.Injective e)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hS : InTriStrict (v (e 6)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hT : InTriStrict (v (e 7)) (v (e 3)) (v (e 1)) (v (e 2))) :
    (25 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  obtain ⟨hPBC, hPCA, hPAB⟩ := inTriStrict_fan_pos hABC hP
  have hfour := lemma4_bound surcharge1 surcharge2 hmin
    (e ∘ ![3, 1, 2, 4, 5, 6, 7]) (he.comp (by decide))
    hPBC (by simpa using hQ) (by simpa using hR)
    (by simpa using hS) (by simpa using hT)
  have he1 := MainAux.empty_bound hmin (e ∘ ![3, 2, 0])
    (he.comp (by decide)) hPCA
  have he2 := MainAux.empty_bound hmin (e ∘ ![3, 0, 1])
    (he.comp (by decide)) hPAB
  simp at hfour he1 he2
  nlinarith [fan_sum (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2))]

private lemma lemma5_310 {n : ℕ} {v : Fin n → Point}
    (surcharge1 : Surcharge1Statement)
    (_surcharge2 : Surcharge2Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 8 → Fin n)
    (he : Function.Injective e)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hS : InTriStrict (v (e 6)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hT : InTriStrict (v (e 7)) (v (e 3)) (v (e 2)) (v (e 0))) :
    (25 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  obtain ⟨hPBC, hPCA, hPAB⟩ := inTriStrict_fan_pos hABC hP
  have hthree := MainAux.lemma3_bound surcharge1 hmin
    (e ∘ ![3, 1, 2, 4, 5, 6]) (he.comp (by decide))
    hPBC (by simpa using hQ) (by simpa using hR) (by simpa using hS)
  have hone := MainAux.one_point_bound hmin (e ∘ ![3, 2, 0, 7])
    (he.comp (by decide)) hPCA (by simpa using hT)
  have hempty := MainAux.empty_bound hmin (e ∘ ![3, 0, 1])
    (he.comp (by decide)) hPAB
  simp at hthree hone hempty
  nlinarith [fan_sum (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2))]

private lemma lemma5_301 {n : ℕ} {v : Fin n → Point}
    (surcharge1 : Surcharge1Statement)
    (_surcharge2 : Surcharge2Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 8 → Fin n)
    (he : Function.Injective e)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hS : InTriStrict (v (e 6)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hT : InTriStrict (v (e 7)) (v (e 3)) (v (e 0)) (v (e 1))) :
    (25 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  obtain ⟨hPBC, hPCA, hPAB⟩ := inTriStrict_fan_pos hABC hP
  have hthree := MainAux.lemma3_bound surcharge1 hmin
    (e ∘ ![3, 1, 2, 4, 5, 6]) (he.comp (by decide))
    hPBC (by simpa using hQ) (by simpa using hR) (by simpa using hS)
  have hone := MainAux.one_point_bound hmin (e ∘ ![3, 0, 1, 7])
    (he.comp (by decide)) hPAB (by simpa using hT)
  have hempty := MainAux.empty_bound hmin (e ∘ ![3, 2, 0])
    (he.comp (by decide)) hPCA
  simp at hthree hone hempty
  nlinarith [fan_sum (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2))]

private lemma lemma5_220 {n : ℕ} {v : Fin n → Point}
    (_surcharge1 : Surcharge1Statement)
    (_surcharge2 : Surcharge2Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 8 → Fin n)
    (he : Function.Injective e)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hS : InTriStrict (v (e 6)) (v (e 3)) (v (e 2)) (v (e 0)))
    (hT : InTriStrict (v (e 7)) (v (e 3)) (v (e 2)) (v (e 0))) :
    (25 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  obtain ⟨hPBC, hPCA, hPAB⟩ := inTriStrict_fan_pos hABC hP
  have htwo1 := MainAux.two_point_bound hmin (e ∘ ![3, 1, 2, 4, 5])
    (he.comp (by decide)) hPBC
    (by simpa using hQ) (by simpa using hR)
  have htwo2 := MainAux.two_point_bound hmin (e ∘ ![3, 2, 0, 6, 7])
    (he.comp (by decide)) hPCA
    (by simpa using hS) (by simpa using hT)
  have hempty := MainAux.empty_bound hmin (e ∘ ![3, 0, 1])
    (he.comp (by decide)) hPAB
  simp at htwo1 htwo2 hempty
  nlinarith [fan_sum (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)),
    MainAux.three_halves_le_sqrt_three]

private lemma lemma5_211 {n : ℕ} {v : Fin n → Point}
    (_surcharge1 : Surcharge1Statement)
    (_surcharge2 : Surcharge2Statement)
    (hmin : AllTrianglesMinAreaOne v) (e : Fin 8 → Fin n)
    (he : Function.Injective e)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hP : InTriStrict (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)))
    (hQ : InTriStrict (v (e 4)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hR : InTriStrict (v (e 5)) (v (e 3)) (v (e 1)) (v (e 2)))
    (hS : InTriStrict (v (e 6)) (v (e 3)) (v (e 2)) (v (e 0)))
    (hT : InTriStrict (v (e 7)) (v (e 3)) (v (e 0)) (v (e 1))) :
    (25 : ℝ) / 2 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) / 2 := by
  obtain ⟨hPBC, hPCA, hPAB⟩ := inTriStrict_fan_pos hABC hP
  have htwo := MainAux.two_point_bound hmin (e ∘ ![3, 1, 2, 4, 5])
    (he.comp (by decide)) hPBC
    (by simpa using hQ) (by simpa using hR)
  have hone1 := MainAux.one_point_bound hmin (e ∘ ![3, 2, 0, 6])
    (he.comp (by decide)) hPCA (by simpa using hS)
  have hone2 := MainAux.one_point_bound hmin (e ∘ ![3, 0, 1, 7])
    (he.comp (by decide)) hPAB (by simpa using hT)
  simp at htwo hone1 hone2
  nlinarith [fan_sum (v (e 3)) (v (e 0)) (v (e 1)) (v (e 2)),
    MainAux.three_halves_le_sqrt_three]

/-- TH8 Lemma 5: a triangle with five selected interior points. -/
theorem th8_lemma5
    (surcharge1 : Surcharge1Statement)
    (surcharge2 : Surcharge2Statement)
    (v : Fin 8 → Point)
    (hABC : 0 < sig (v 0) (v 1) (v 2))
    (hP : InTriStrict (v 3) (v 0) (v 1) (v 2))
    (hQ : InTriStrict (v 4) (v 0) (v 1) (v 2))
    (hR : InTriStrict (v 5) (v 0) (v 1) (v 2))
    (hS : InTriStrict (v 6) (v 0) (v 1) (v 2))
    (hT : InTriStrict (v 7) (v 0) (v 1) (v 2))
    (hmin : AllTrianglesMinAreaOne v) :
    (25 : ℝ) / 2 ≤ sig (v 0) (v 1) (v 2) / 2 := by
  let A := v 0
  let B := v 1
  let C := v 2
  let P := v 3
  let Q := v 4
  let R := v 5
  let S := v 6
  let T := v 7
  obtain ⟨q, hq⟩ :=
    MainAux.fanCell_exists_reindex hmin ![0, 1, 2, 3, 4] (by decide) hP hQ
  obtain ⟨r, hr⟩ :=
    MainAux.fanCell_exists_reindex hmin ![0, 1, 2, 3, 5] (by decide) hP hR
  obtain ⟨s, hs⟩ :=
    MainAux.fanCell_exists_reindex hmin ![0, 1, 2, 3, 6] (by decide) hP hS
  obtain ⟨t, ht⟩ :=
    MainAux.fanCell_exists_reindex hmin ![0, 1, 2, 3, 7] (by decide) hP hT
  change (25 : ℝ) / 2 ≤ sig A B C / 2
  fin_cases q <;> fin_cases r <;> fin_cases s <;> fin_cases t
  all_goals simp [InFanCell] at hq hr hs ht
  · have hb :=
      lemma5_400 surcharge1 surcharge2 hmin ![0,1,2,3,4,5,6,7] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simpa using hb
  · have hb :=
      lemma5_310 surcharge1 surcharge2 hmin ![0,1,2,3,4,5,6,7] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simpa using hb
  · have hb :=
      lemma5_301 surcharge1 surcharge2 hmin ![0,1,2,3,4,5,6,7] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simpa using hb
  · have hb :=
      lemma5_310 surcharge1 surcharge2 hmin ![0,1,2,3,4,5,7,6] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hr) (by simpa using ht) (by simpa using hs)
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![0,1,2,3,4,5,6,7] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![0,1,2,3,4,5,6,7] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simpa using hb
  · have hb :=
      lemma5_301 surcharge1 surcharge2 hmin ![0,1,2,3,4,5,7,6] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hr) (by simpa using ht) (by simpa using hs)
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![0,1,2,3,4,5,7,6] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hr) (by simpa using ht) (by simpa using hs)
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![2,0,1,3,6,7,4,5] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hs) (by simpa using ht) (by simpa using hq) (by simpa using hr)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_310 surcharge1 surcharge2 hmin ![0,1,2,3,4,6,7,5] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hs) (by simpa using ht) (by simpa using hr)
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![0,1,2,3,4,6,5,7] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hs) (by simpa using hr) (by simpa using ht)
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![0,1,2,3,4,6,5,7] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hs) (by simpa using hr) (by simpa using ht)
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![0,1,2,3,4,7,5,6] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using ht) (by simpa using hr) (by simpa using hs)
    simpa using hb
  · have hb :=
      lemma5_301 surcharge1 surcharge2 hmin ![1,2,0,3,5,6,7,4] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hr) (by simpa using hs) (by simpa using ht) (by simpa using hq)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![1,2,0,3,5,6,7,4] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hr) (by simpa using hs) (by simpa using ht) (by simpa using hq)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![0,1,2,3,4,7,5,6] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using ht) (by simpa using hr) (by simpa using hs)
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![1,2,0,3,5,7,6,4] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hr) (by simpa using ht) (by simpa using hs) (by simpa using hq)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![2,0,1,3,6,7,4,5] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hs) (by simpa using ht) (by simpa using hq) (by simpa using hr)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_301 surcharge1 surcharge2 hmin ![0,1,2,3,4,6,7,5] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hs) (by simpa using ht) (by simpa using hr)
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![0,1,2,3,4,6,7,5] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using hs) (by simpa using ht) (by simpa using hr)
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![2,0,1,3,5,7,4,6] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hr) (by simpa using ht) (by simpa using hq) (by simpa using hs)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![0,1,2,3,4,7,6,5] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hq) (by simpa using ht) (by simpa using hs) (by simpa using hr)
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![1,2,0,3,6,7,5,4] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hs) (by simpa using ht) (by simpa using hr) (by simpa using hq)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![2,0,1,3,5,7,4,6] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hr) (by simpa using ht) (by simpa using hq) (by simpa using hs)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![2,0,1,3,5,6,4,7] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hr) (by simpa using hs) (by simpa using hq) (by simpa using ht)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![2,0,1,3,5,6,4,7] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hr) (by simpa using hs) (by simpa using hq) (by simpa using ht)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_310 surcharge1 surcharge2 hmin ![2,0,1,3,5,6,7,4] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hr) (by simpa using hs) (by simpa using ht) (by simpa using hq)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_310 surcharge1 surcharge2 hmin ![0,1,2,3,5,6,7,4] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hr) (by simpa using hs) (by simpa using ht) (by simpa using hq)
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![0,1,2,3,5,6,4,7] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hr) (by simpa using hs) (by simpa using hq) (by simpa using ht)
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![0,1,2,3,5,6,4,7] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hr) (by simpa using hs) (by simpa using hq) (by simpa using ht)
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![0,1,2,3,5,7,4,6] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hr) (by simpa using ht) (by simpa using hq) (by simpa using hs)
    simpa using hb
  · have hb :=
      lemma5_301 surcharge1 surcharge2 hmin ![1,2,0,3,4,6,7,5] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hs) (by simpa using ht) (by simpa using hr)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![1,2,0,3,4,6,7,5] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hs) (by simpa using ht) (by simpa using hr)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![0,1,2,3,5,7,4,6] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hr) (by simpa using ht) (by simpa using hq) (by simpa using hs)
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![1,2,0,3,4,7,6,5] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using ht) (by simpa using hs) (by simpa using hr)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![2,0,1,3,6,7,5,4] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hs) (by simpa using ht) (by simpa using hr) (by simpa using hq)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![0,1,2,3,6,7,4,5] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hs) (by simpa using ht) (by simpa using hq) (by simpa using hr)
    simpa using hb
  · have hb :=
      lemma5_301 surcharge1 surcharge2 hmin ![1,2,0,3,4,5,7,6] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hr) (by simpa using ht) (by simpa using hs)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![1,2,0,3,4,5,7,6] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hr) (by simpa using ht) (by simpa using hs)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_301 surcharge1 surcharge2 hmin ![1,2,0,3,4,5,6,7] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_400 surcharge1 surcharge2 hmin ![1,2,0,3,4,5,6,7] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_310 surcharge1 surcharge2 hmin ![1,2,0,3,4,5,6,7] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![1,2,0,3,4,5,6,7] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_310 surcharge1 surcharge2 hmin ![1,2,0,3,4,5,7,6] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hr) (by simpa using ht) (by simpa using hs)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![1,2,0,3,4,5,6,7] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![0,1,2,3,6,7,4,5] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hs) (by simpa using ht) (by simpa using hq) (by simpa using hr)
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![1,2,0,3,4,7,5,6] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using ht) (by simpa using hr) (by simpa using hs)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![2,0,1,3,5,7,6,4] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hr) (by simpa using ht) (by simpa using hs) (by simpa using hq)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![1,2,0,3,4,6,5,7] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hs) (by simpa using hr) (by simpa using ht)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_310 surcharge1 surcharge2 hmin ![1,2,0,3,4,6,7,5] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hs) (by simpa using ht) (by simpa using hr)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![1,2,0,3,4,6,5,7] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using hs) (by simpa using hr) (by simpa using ht)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![2,0,1,3,5,6,7,4] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hr) (by simpa using hs) (by simpa using ht) (by simpa using hq)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![1,2,0,3,4,7,5,6] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hq) (by simpa using ht) (by simpa using hr) (by simpa using hs)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_301 surcharge1 surcharge2 hmin ![2,0,1,3,5,6,7,4] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hr) (by simpa using hs) (by simpa using ht) (by simpa using hq)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_301 surcharge1 surcharge2 hmin ![0,1,2,3,5,6,7,4] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hr) (by simpa using hs) (by simpa using ht) (by simpa using hq)
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![0,1,2,3,5,6,7,4] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hr) (by simpa using hs) (by simpa using ht) (by simpa using hq)
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![2,0,1,3,4,7,5,6] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using ht) (by simpa using hr) (by simpa using hs)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![0,1,2,3,5,7,6,4] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hr) (by simpa using ht) (by simpa using hs) (by simpa using hq)
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![1,2,0,3,6,7,4,5] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hs) (by simpa using ht) (by simpa using hq) (by simpa using hr)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![2,0,1,3,4,7,5,6] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using ht) (by simpa using hr) (by simpa using hs)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![2,0,1,3,4,6,5,7] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hs) (by simpa using hr) (by simpa using ht)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![2,0,1,3,4,6,5,7] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hs) (by simpa using hr) (by simpa using ht)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_310 surcharge1 surcharge2 hmin ![2,0,1,3,4,6,7,5] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hs) (by simpa using ht) (by simpa using hr)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![0,1,2,3,6,7,5,4] (by decide)
        (by simpa using hABC) (by simpa using hP)
        (by simpa using hs) (by simpa using ht) (by simpa using hr) (by simpa using hq)
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![1,2,0,3,5,7,4,6] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hr) (by simpa using ht) (by simpa using hq) (by simpa using hs)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![2,0,1,3,4,7,6,5] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using ht) (by simpa using hs) (by simpa using hr)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![1,2,0,3,5,6,4,7] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hr) (by simpa using hs) (by simpa using hq) (by simpa using ht)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_310 surcharge1 surcharge2 hmin ![1,2,0,3,5,6,7,4] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hr) (by simpa using hs) (by simpa using ht) (by simpa using hq)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![1,2,0,3,5,6,4,7] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hr) (by simpa using hs) (by simpa using hq) (by simpa using ht)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![2,0,1,3,4,6,7,5] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hs) (by simpa using ht) (by simpa using hr)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![1,2,0,3,5,7,4,6] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hr) (by simpa using ht) (by simpa using hq) (by simpa using hs)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_301 surcharge1 surcharge2 hmin ![2,0,1,3,4,6,7,5] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hs) (by simpa using ht) (by simpa using hr)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![2,0,1,3,4,5,6,7] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![2,0,1,3,4,5,6,7] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_310 surcharge1 surcharge2 hmin ![2,0,1,3,4,5,7,6] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hr) (by simpa using ht) (by simpa using hs)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_211 surcharge1 surcharge2 hmin ![2,0,1,3,4,5,7,6] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hr) (by simpa using ht) (by simpa using hs)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_220 surcharge1 surcharge2 hmin ![1,2,0,3,6,7,4,5] (by decide)
        (by
          have hh : 0 < sig B C A := by
            simpa only [← sig_rotate A B C] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate hP)
        (by simpa using hs) (by simpa using ht) (by simpa using hq) (by simpa using hr)
    simp at hb
    rw [sig_rotate A B C]
    simpa using hb
  · have hb :=
      lemma5_301 surcharge1 surcharge2 hmin ![2,0,1,3,4,5,7,6] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hr) (by simpa using ht) (by simpa using hs)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_310 surcharge1 surcharge2 hmin ![2,0,1,3,4,5,6,7] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_301 surcharge1 surcharge2 hmin ![2,0,1,3,4,5,6,7] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb
  · have hb :=
      lemma5_400 surcharge1 surcharge2 hmin ![2,0,1,3,4,5,6,7] (by decide)
        (by
          have hh : 0 < sig C A B := by
            simpa only [sig_rotate C A B] using hABC
          simpa using hh) (by simpa using MainAux.inTriStrict_rotate (MainAux.inTriStrict_rotate hP))
        (by simpa using hq) (by simpa using hr) (by simpa using hs) (by simpa using ht)
    simp at hb
    rw [← sig_rotate C A B]
    simpa using hb


end Heilbronn8.TriHull
