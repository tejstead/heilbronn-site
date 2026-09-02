import Heilbronn8.Ident

namespace Heilbronn8

/--
An affine map
`(x,y) ↦ (a*x + b*y + e, c*x + d*y + f)`
whose linear determinant is positive.
-/
structure PosAffine where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  f : ℝ
  det_pos : 0 < a * d - b * c

def PosAffine.det (T : PosAffine) : ℝ :=
  T.a * T.d - T.b * T.c

def PosAffine.map (T : PosAffine) (p : ℝ × ℝ) : ℝ × ℝ :=
  (T.a * p.1 + T.b * p.2 + T.e,
   T.c * p.1 + T.d * p.2 + T.f)

lemma PosAffine.det_pos' (T : PosAffine) :
    0 < T.det :=
  T.det_pos

/-- Signed areas transform by the determinant of the linear part. -/
lemma sig_posAffine (T : PosAffine) (p q r : ℝ × ℝ) :
    sig (T.map p) (T.map q) (T.map r) =
      T.det * sig p q r := by
  simp only [PosAffine.map, PosAffine.det, sig]
  ring

/--
The barycentric affine gauge associated to the positively oriented
triangle `A B C`.
-/
noncomputable def gaugeAffine (A B C : ℝ × ℝ)
    (hD : 0 < sig A B C) : PosAffine := by
  let D := sig A B C
  let aa := (C.2 - A.2) / D
  let bb := -(C.1 - A.1) / D
  let cc := -(B.2 - A.2) / D
  let dd := (B.1 - A.1) / D
  let ee := -(aa * A.1 + bb * A.2)
  let ff := -(cc * A.1 + dd * A.2)
  refine ⟨aa, bb, cc, dd, ee, ff, ?_⟩
  have hD' : 0 < D := by
    simpa [D] using hD
  have hDne : D ≠ 0 := ne_of_gt hD'
  have heq : aa * dd - bb * cc = 1 / D := by
    dsimp [aa, bb, cc, dd]
    field_simp [hDne]
    dsimp [D, sig]
    ring
  rw [heq]
  exact one_div_pos.mpr hD'

lemma gaugeAffine_det (A B C : ℝ × ℝ)
    (hD : 0 < sig A B C) :
    (gaugeAffine A B C hD).det = 1 / sig A B C := by
  simp only [gaugeAffine, PosAffine.det]
  field_simp [ne_of_gt hD]
  simp only [sig]
  ring

lemma gaugeAffine_map_A (A B C : ℝ × ℝ)
    (hD : 0 < sig A B C) :
    (gaugeAffine A B C hD).map A = (0, 0) := by
  apply Prod.ext <;>
    simp [gaugeAffine, PosAffine.map]

lemma gaugeAffine_map_B (A B C : ℝ × ℝ)
    (hD : 0 < sig A B C) :
    (gaugeAffine A B C hD).map B = (1, 0) := by
  apply Prod.ext
  · simp only [gaugeAffine, PosAffine.map, Prod.fst]
    field_simp [ne_of_gt hD]
    simp only [sig]
    ring
  · simp only [gaugeAffine, PosAffine.map, Prod.snd]
    field_simp [ne_of_gt hD]
    simp only [sig]
    ring

lemma gaugeAffine_map_C (A B C : ℝ × ℝ)
    (hD : 0 < sig A B C) :
    (gaugeAffine A B C hD).map C = (0, 1) := by
  apply Prod.ext
  · simp only [gaugeAffine, PosAffine.map, Prod.fst]
    field_simp [ne_of_gt hD]
    simp only [sig]
    ring
  · simp only [gaugeAffine, PosAffine.map, Prod.snd]
    field_simp [ne_of_gt hD]
    simp only [sig]
    ring

/--
A maximum over increasing triples also bounds triples in every ordering,
including triples with repeated indices.
-/
lemma abs_sig_le_of_triples_max (v : Fin 8 → ℝ × ℝ)
    {i j k : Fin 8}
    (hmax : ∀ t ∈ triples,
      |sig (v t.1) (v t.2.1) (v t.2.2)| ≤
        |sig (v i) (v j) (v k)|) :
    ∀ a b c : Fin 8,
      |sig (v a) (v b) (v c)| ≤
        |sig (v i) (v j) (v k)| := by
  intro a b c
  by_cases hab : a = b
  · subst b
    simp [sig]
  by_cases hac : a = c
  · subst c
    simp [sig]
  by_cases hbc : b = c
  · subst c
    simp [sig]
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · rcases lt_or_gt_of_ne hbc with hbclt | hcblt
    · exact hmax (a, b, c) (by simp [triples, hablt, hbclt])
    · rcases lt_or_gt_of_ne hac with haclt | hcalt
      · calc
          |sig (v a) (v b) (v c)| =
              |sig (v a) (v c) (v b)| := by
                rw [sig_swap, abs_neg]
          _ ≤ |sig (v i) (v j) (v k)| :=
            hmax (a, c, b) (by simp [triples, haclt, hcblt])
      · calc
          |sig (v a) (v b) (v c)| =
              |sig (v c) (v a) (v b)| := by
                rw [sig_rotate, sig_rotate]
          _ ≤ |sig (v i) (v j) (v k)| :=
            hmax (c, a, b) (by simp [triples, hcalt, hablt])
  · rcases lt_or_gt_of_ne hac with haclt | hcalt
    · calc
        |sig (v a) (v b) (v c)| =
            |sig (v b) (v a) (v c)| := by
              have heq :
                  sig (v a) (v b) (v c) =
                    -sig (v b) (v a) (v c) := by
                simp only [sig]
                ring1
              rw [heq, abs_neg]
        _ ≤ |sig (v i) (v j) (v k)| :=
          hmax (b, a, c) (by simp [triples, hbalt, haclt])
    · rcases lt_or_gt_of_ne hbc with hbclt | hcblt
      · calc
          |sig (v a) (v b) (v c)| =
              |sig (v b) (v c) (v a)| := by
                rw [sig_rotate]
          _ ≤ |sig (v i) (v j) (v k)| :=
            hmax (b, c, a) (by simp [triples, hbclt, hcalt])
      · calc
          |sig (v a) (v b) (v c)| =
              |sig (v c) (v b) (v a)| := by
                have heq :
                    sig (v a) (v b) (v c) =
                      -sig (v c) (v b) (v a) := by
                  simp only [sig]
                  ring1
                rw [heq, abs_neg]
          _ ≤ |sig (v i) (v j) (v k)| :=
            hmax (c, b, a) (by simp [triples, hcblt, hbalt])

def InMaximalityBox (p : ℝ × ℝ) : Prop :=
  p.1 ≤ 1 ∧ p.2 ≤ 1 ∧ 0 ≤ p.1 + p.2

/--
The three pointwise bounds come from replacing one gauge vertex:

* `(A,l,C)` gives `|(u l).1| ≤ 1`;
* `(A,B,l)` gives `|(u l).2| ≤ 1`;
* `(l,B,C)` gives `|1 - (u l).1 - (u l).2| ≤ 1`.
-/
lemma inMaximalityBox_of_normalized
    (u : Fin 8 → ℝ × ℝ) (A B C : Fin 8)
    (hA : u A = (0, 0))
    (hB : u B = (1, 0))
    (hC : u C = (0, 1))
    (hall : ∀ a b c : Fin 8,
      |sig (u a) (u b) (u c)| ≤ 1) :
    ∀ l : Fin 8, InMaximalityBox (u l) := by
  intro l
  have hx : |(u l).1| ≤ 1 := by
    have h := hall A l C
    rw [hA, hC] at h
    simpa [sig] using h
  have hy : |(u l).2| ≤ 1 := by
    have h := hall A B l
    rw [hA, hB] at h
    simpa [sig] using h
  have hs : |1 - (u l).1 - (u l).2| ≤ 1 := by
    have h := hall l B C
    rw [hB, hC] at h
    have heq :
        sig (u l) (1, 0) (0, 1) =
          1 - (u l).1 - (u l).2 := by
      simp only [sig]
      ring
    rwa [heq] at h
  refine
    ⟨le_trans (le_abs_self _) hx,
      le_trans (le_abs_self _) hy, ?_⟩
  have hz :=
    le_trans (le_abs_self (1 - (u l).1 - (u l).2)) hs
  linarith

def NotAllCollinear (v : Fin 8 → ℝ × ℝ) : Prop :=
  ∃ i j k : Fin 8,
    i < j ∧ j < k ∧ sig (v i) (v j) (v k) ≠ 0

/--
The complete compactness gauge.

`i < j < k` is the increasing maximum-area carrier. `A,B,C` is its
counterclockwise ordering, so it can be sent by a positive-determinant
affine map to the standard triangle.
-/
structure MaxGauge (v : Fin 8 → ℝ × ℝ) where
  i : Fin 8
  j : Fin 8
  k : Fin 8
  hij : i < j
  hjk : j < k
  maximal : ∀ a b c : Fin 8,
    |sig (v a) (v b) (v c)| ≤
      |sig (v i) (v j) (v k)|
  A : Fin 8
  B : Fin 8
  C : Fin 8
  oriented_order :
    (A = i ∧ B = j ∧ C = k) ∨
    (A = i ∧ B = k ∧ C = j)
  oriented_area :
    sig (v A) (v B) (v C) =
      |sig (v i) (v j) (v k)|
  T : PosAffine
  det_eq :
    T.det = 1 / |sig (v i) (v j) (v k)|
  map_A : T.map (v A) = (0, 0)
  map_B : T.map (v B) = (1, 0)
  map_C : T.map (v C) = (0, 1)
  transform : ∀ p q r : ℝ × ℝ,
    sig (T.map p) (T.map q) (T.map r) =
      (1 / |sig (v i) (v j) (v k)|) * sig p q r
  transformed_bound : ∀ a b c : Fin 8,
    |sig (T.map (v a)) (T.map (v b)) (T.map (v c))| ≤ 1
  box : ∀ l : Fin 8,
    InMaximalityBox (T.map (v l))

lemma maxGauge_of_oriented (v : Fin 8 → ℝ × ℝ)
    (i j k A B C : Fin 8)
    (hij : i < j) (hjk : j < k)
    (hmax : ∀ a b c : Fin 8,
      |sig (v a) (v b) (v c)| ≤
        |sig (v i) (v j) (v k)|)
    (hMpos : 0 < |sig (v i) (v j) (v k)|)
    (horder :
      (A = i ∧ B = j ∧ C = k) ∨
      (A = i ∧ B = k ∧ C = j))
    (horient :
      sig (v A) (v B) (v C) =
        |sig (v i) (v j) (v k)|) :
    Nonempty (MaxGauge v) := by
  let M := |sig (v i) (v j) (v k)|
  have hM : 0 < M := by
    simpa [M] using hMpos
  have hABC : 0 < sig (v A) (v B) (v C) := by
    rw [horient]
    exact hMpos
  let T := gaugeAffine (v A) (v B) (v C) hABC
  have hdet : T.det = 1 / M := by
    calc
      T.det = 1 / sig (v A) (v B) (v C) :=
        gaugeAffine_det (v A) (v B) (v C) hABC
      _ = 1 / M := by rw [horient]
  have hTA : T.map (v A) = (0, 0) :=
    gaugeAffine_map_A (v A) (v B) (v C) hABC
  have hTB : T.map (v B) = (1, 0) :=
    gaugeAffine_map_B (v A) (v B) (v C) hABC
  have hTC : T.map (v C) = (0, 1) :=
    gaugeAffine_map_C (v A) (v B) (v C) hABC
  have htransform : ∀ p q r : ℝ × ℝ,
      sig (T.map p) (T.map q) (T.map r) =
        (1 / M) * sig p q r := by
    intro p q r
    rw [sig_posAffine, hdet]
  have hnorm : ∀ a b c : Fin 8,
      |sig (T.map (v a)) (T.map (v b)) (T.map (v c))| ≤ 1 := by
    intro a b c
    rw [htransform, abs_mul, abs_of_pos (one_div_pos.mpr hM)]
    calc
      (1 / M) * |sig (v a) (v b) (v c)|
          ≤ (1 / M) * M :=
        mul_le_mul_of_nonneg_left
          (hmax a b c) (one_div_pos.mpr hM).le
      _ = 1 := by
        field_simp [ne_of_gt hM]
  refine ⟨{
    i := i
    j := j
    k := k
    hij := hij
    hjk := hjk
    maximal := hmax
    A := A
    B := B
    C := C
    oriented_order := horder
    oriented_area := horient
    T := T
    det_eq := by simpa [M] using hdet
    map_A := hTA
    map_B := hTB
    map_C := hTC
    transform := by simpa [M] using htransform
    transformed_bound := hnorm
    box := inMaximalityBox_of_normalized
      (fun l => T.map (v l)) A B C hTA hTB hTC hnorm
  }⟩

/--
Select a maximum among the 56 increasing triples and normalize its
counterclockwise ordering.

The normalized determinant factor is exactly `1 / M`, where
`M = |sig (v i) (v j) (v k)|`; equivalently it is `T.det`.
-/
theorem exists_maxGauge (v : Fin 8 → ℝ × ℝ)
    (hnc : NotAllCollinear v) :
    Nonempty (MaxGauge v) := by
  obtain ⟨t, ht, htmax⟩ :=
    Finset.exists_max_image triples
      (fun t => |sig (v t.1) (v t.2.1) (v t.2.2)|)
      triples_nonempty
  have ht' : t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
    simpa [triples] using ht
  let i := t.1
  let j := t.2.1
  let k := t.2.2
  have hij : i < j := by
    simpa [i, j] using ht'.1
  have hjk : j < k := by
    simpa [j, k] using ht'.2
  have hmaxTriples : ∀ s ∈ triples,
      |sig (v s.1) (v s.2.1) (v s.2.2)| ≤
        |sig (v i) (v j) (v k)| := by
    intro s hs
    simpa [i, j, k] using htmax s hs
  have hmax :=
    abs_sig_le_of_triples_max v hmaxTriples
  obtain ⟨i0, j0, k0, hi0j0, hj0k0, hnz⟩ := hnc
  have hMpos : 0 < |sig (v i) (v j) (v k)| :=
    lt_of_lt_of_le (abs_pos.mpr hnz) (hmax i0 j0 k0)
  have hDne : sig (v i) (v j) (v k) ≠ 0 :=
    abs_ne_zero.mp (ne_of_gt hMpos)
  rcases lt_or_gt_of_ne hDne with hneg | hpos
  · apply maxGauge_of_oriented
      v i j k i k j hij hjk hmax hMpos
    · exact Or.inr ⟨rfl, rfl, rfl⟩
    · rw [sig_swap, abs_of_neg hneg]
  · apply maxGauge_of_oriented
      v i j k i j k hij hjk hmax hMpos
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · rw [abs_of_pos hpos]

end Heilbronn8
