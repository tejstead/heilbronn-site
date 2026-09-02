import Heil5.Pentagon
import Heil5.Inside
import Heil5.ConvexPos5
import Heil5.Collinear
import Heil5.Compose
import Heil5.AnyTriple

namespace Heilbronn5

lemma quarter_le_tau : (1/4 : ℝ) ≤ tau := by
  unfold tau
  nlinarith [sqrt5_mul_self, sqrt5_nonneg]

lemma fifth_le_tau : (1/5 : ℝ) ≤ tau := by
  unfold tau
  linarith [sqrt5_lt_three]

lemma minTri_comp_inj_le (v : Fin 5 → ℝ × ℝ) (f : Fin 5 → Fin 5)
    (hf : Function.Injective f) : minTri v ≤ minTri (v ∘ f) := by
  show minTri v ≤
    min (min (min (|sig (v (f 0)) (v (f 1)) (v (f 2))|)
      (|sig (v (f 0)) (v (f 1)) (v (f 3))|))
      (min (|sig (v (f 0)) (v (f 1)) (v (f 4))|)
        (|sig (v (f 0)) (v (f 2)) (v (f 3))|)))
      (min (min (min (|sig (v (f 0)) (v (f 2)) (v (f 4))|)
        (|sig (v (f 0)) (v (f 3)) (v (f 4))|))
        (min (|sig (v (f 1)) (v (f 2)) (v (f 3))|)
          (|sig (v (f 1)) (v (f 2)) (v (f 4))|)))
        (min (|sig (v (f 1)) (v (f 3)) (v (f 4))|)
          (|sig (v (f 2)) (v (f 3)) (v (f 4))|)))
  refine le_min (le_min (le_min ?_ ?_) (le_min ?_ ?_))
    (le_min (le_min (le_min ?_ ?_) (le_min ?_ ?_)) (le_min ?_ ?_)) <;>
    exact minTri_le_any v _ _ _ (hf.ne (by decide)) (hf.ne (by decide))
      (hf.ne (by decide))

lemma inj_of_list (a b c d e : Fin 5) (h01 : a ≠ b) (h02 : a ≠ c) (h03 : a ≠ d)
    (h04 : a ≠ e) (h12 : b ≠ c) (h13 : b ≠ d) (h14 : b ≠ e) (h23 : c ≠ d)
    (h24 : c ≠ e) (h34 : d ≠ e) :
    Function.Injective (![a,b,c,d,e] : Fin 5 → Fin 5) := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;>
    simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      Matrix.cons_val_four]

lemma tuple_eq_comp (v : Fin 5 → ℝ × ℝ) (a b c d e : Fin 5) :
    ![v a, v b, v c, v d, v e] = v ∘ ![a,b,c,d,e] := by
  funext i; fin_cases i <;> rfl

lemma inTri_perm23 (p a b c : ℝ × ℝ) (h : InTri p a b c) : InTri p a c b := by
  obtain ⟨x, y, z, hx, hy, hz, hs, he⟩ := h
  exact ⟨x, z, y, hx, hz, hy, by linarith, by rw [he]; module⟩

inductive IsHullArea (v : Fin 5 → ℝ × ℝ) : ℝ → Prop
  | pent (f : Fin 5 → Fin 5) (hf : Function.Injective f)
      (h : ConvexPos (v ∘ f)) : IsHullArea v (penArea (v ∘ f) / 2)
  | quad (f : Fin 5 → Fin 5) (hf : Function.Injective f)
      (h : QuadPos (v ∘ f))
      (hw : ∃ x y z t : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ 0 ≤ t ∧ x + y + z + t = 1 ∧
        (v ∘ f) 4 = x • (v ∘ f) 0 + y • (v ∘ f) 1 + z • (v ∘ f) 2 + t • (v ∘ f) 3) :
      IsHullArea v (quadArea (v ∘ f) / 2)
  | tri (f : Fin 5 → Fin 5) (hf : Function.Injective f)
      (h012 : 0 ≤ sig ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2))
      (h3 : InTri ((v ∘ f) 3) ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2))
      (h4 : InTri ((v ∘ f) 4) ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2)) :
      IsHullArea v (sig ((v ∘ f) 0) ((v ∘ f) 1) ((v ∘ f) 2) / 2)

theorem main_bound (v : Fin 5 → ℝ × ℝ) (H : ℝ) (h : IsHullArea v H) :
    minTri v / 2 ≤ tau * H := by
  cases h with
  | pent f hf hc =>
      have hm := minTri_comp_inj_le v f hf
      have hp := pentagon_case (v ∘ f) hc
      linarith
  | quad f hf hq hw =>
      have hm := minTri_comp_inj_le v f hf
      have hqc := quad_case (v ∘ f) hq hw
      have hm0 := minTri_nonneg (v ∘ f)
      have hQ0 : 0 ≤ quadArea (v ∘ f) := by linarith
      linarith [mul_nonneg
        (show (0:ℝ) ≤ tau - 1/4 by linarith [quarter_le_tau]) hQ0]
  | tri f hf h012 h3 h4 =>
      have hm := minTri_comp_inj_le v f hf
      have htc := tri_case (v ∘ f) h012 h3 h4
      linarith [mul_nonneg
        (show (0:ℝ) ≤ tau - 1/5 by linarith [fifth_le_tau]) h012]

lemma tri_pack (v : Fin 5 → ℝ × ℝ) (a b c p q : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (haq : a ≠ q)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbq : b ≠ q)
    (hcp : c ≠ p) (hcq : c ≠ q) (hpq : p ≠ q)
    (hp : InTri (v p) (v a) (v b) (v c))
    (hq : InTri (v q) (v a) (v b) (v c)) :
    ∃ H, IsHullArea v H := by
  rcases le_total 0 (sig (v a) (v b) (v c)) with hor | hor
  · exact ⟨_, IsHullArea.tri ![a,b,c,p,q]
      (inj_of_list a b c p q hab hac hap haq hbc hbp hbq hcp hcq hpq)
      hor hp hq⟩
  · have hor' : 0 ≤ sig (v a) (v c) (v b) := by
      rw [show sig (v a) (v c) (v b) = -sig (v a) (v b) (v c) from by
        simp only [sig]; ring]
      linarith
    exact ⟨_, IsHullArea.tri ![a,c,b,p,q]
      (inj_of_list a c b p q hac hab hap haq hbc.symm hcp hcq hbp hbq hpq)
      hor' (inTri_perm23 _ _ _ _ hp) (inTri_perm23 _ _ _ _ hq)⟩

lemma quad_pack (v : Fin 5 → ℝ × ℝ) (a b c d e : Fin 5)
    (h01 : a ≠ b) (h02 : a ≠ c) (h03 : a ≠ d) (h04 : a ≠ e)
    (h12 : b ≠ c) (h13 : b ≠ d) (h14 : b ≠ e) (h23 : c ≠ d) (h24 : c ≠ e)
    (h34 : d ≠ e)
    (hq : QuadCCW (v a) (v b) (v c) (v d))
    (hw : ∃ x y z t : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ 0 ≤ t ∧ x + y + z + t = 1 ∧
      v e = x • v a + y • v b + z • v c + t • v d) :
    ∃ H, IsHullArea v H :=
  ⟨_, IsHullArea.quad ![a,b,c,d,e]
    (inj_of_list a b c d e h01 h02 h03 h04 h12 h13 h14 h23 h24 h34) hq hw⟩

lemma pent_pack (v : Fin 5 → ℝ × ℝ) (a b c d e : Fin 5)
    (h01 : a ≠ b) (h02 : a ≠ c) (h03 : a ≠ d) (h04 : a ≠ e)
    (h12 : b ≠ c) (h13 : b ≠ d) (h14 : b ≠ e) (h23 : c ≠ d) (h24 : c ≠ e)
    (h34 : d ≠ e)
    (hc : ConvexPos ![v a, v b, v c, v d, v e]) : ∃ H, IsHullArea v H := by
  rw [tuple_eq_comp v a b c d e] at hc
  exact ⟨_, IsHullArea.pent ![a,b,c,d,e]
    (inj_of_list a b c d e h01 h02 h03 h04 h12 h13 h14 h23 h24 h34) hc⟩

theorem exists_hullArea (v : Fin 5 → ℝ × ℝ) : ∃ H, IsHullArea v H := by
  by_cases hA : ∃ i j k l : Fin 5, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧
      k ≠ l ∧ InTri (v i) (v j) (v k) (v l)
  · -- some point lies in the triangle of three others
    obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, hmem⟩ := hA
    obtain ⟨m, hmi, hmj, hmk, hml⟩ :=
      (by decide : ∀ (i j k l : Fin 5), ∃ m, m ≠ i ∧ m ≠ j ∧ m ≠ k ∧ m ≠ l)
        i j k l
    by_cases hm2 : InTri (v m) (v j) (v k) (v l)
    · exact tri_pack v j k l i m hjk hjl hij.symm hmj.symm hkl hik.symm
        hmk.symm hil.symm hml.symm hmi.symm hmem hm2
    · obtain ⟨x, y, z, hx, hy, hz, hs, he⟩ := hmem
      rcases radon4 (v j) (v k) (v l) (v m) with
        (hq | hq | hq | hq | hq | hq) | (h | h | h | h)
      · exact quad_pack v j k l m i hjk hjl hmj.symm hij.symm hkl hmk.symm
          hik.symm hml.symm hil.symm hmi hq
          ⟨x, y, z, 0, hx, hy, hz, le_refl 0, by linarith,
            by rw [he]; module⟩
      · exact quad_pack v j k m l i hjk hmj.symm hjl hij.symm hmk.symm hkl
          hik.symm hml hmi hil.symm hq
          ⟨x, y, 0, z, hx, hy, le_refl 0, hz, by linarith,
            by rw [he]; module⟩
      · exact quad_pack v j l k m i hjl hjk hmj.symm hij.symm hkl.symm
          hml.symm hil.symm hmk.symm hik.symm hmi hq
          ⟨x, z, y, 0, hx, hz, hy, le_refl 0, by linarith,
            by rw [he]; module⟩
      · exact quad_pack v j m l k i hmj.symm hjl hjk hij.symm hml hmk hmi
          hkl.symm hil.symm hik.symm hq
          ⟨x, 0, z, y, hx, le_refl 0, hz, hy, by linarith,
            by rw [he]; module⟩
      · exact quad_pack v j l m k i hjl hmj.symm hjk hij.symm hml.symm
          hkl.symm hil.symm hmk hmi hik.symm hq
          ⟨x, z, 0, y, hx, hz, le_refl 0, hy, by linarith,
            by rw [he]; module⟩
      · exact quad_pack v j m k l i hmj.symm hjk hjl hij.symm hmk hml hmi
          hkl hik.symm hil.symm hq
          ⟨x, 0, y, z, hx, le_refl 0, hy, hz, by linarith,
            by rw [he]; module⟩
      · -- v j inside (v k, v l, v m)
        have habs : InTri (v i) (v k) (v l) (v m) :=
          inTri_absorb (by rw [he]; exact ⟨x, y, z, hx, hy, hz, hs, rfl⟩) h
            (inTri_vertexA (v k) (v l) (v m)) (inTri_vertexB (v k) (v l) (v m))
        exact tri_pack v k l m j i hkl hmk.symm hjk.symm hik.symm hml.symm
          hjl.symm hil.symm hmj hmi hij.symm h habs
      · -- v k inside (v j, v l, v m)
        have habs : InTri (v i) (v j) (v l) (v m) :=
          inTri_absorb (by rw [he]; exact ⟨x, y, z, hx, hy, hz, hs, rfl⟩)
            (inTri_vertexA (v j) (v l) (v m)) h
            (inTri_vertexB (v j) (v l) (v m))
        exact tri_pack v j l m k i hjl hmj.symm hjk hij.symm hml.symm
          hkl.symm hil.symm hmk hmi hik.symm h habs
      · -- v l inside (v j, v k, v m)
        have habs : InTri (v i) (v j) (v k) (v m) :=
          inTri_absorb (by rw [he]; exact ⟨x, y, z, hx, hy, hz, hs, rfl⟩)
            (inTri_vertexA (v j) (v k) (v m)) (inTri_vertexB (v j) (v k) (v m))
            h
        exact tri_pack v j k m l i hjk hmj.symm hjl hij.symm hmk.symm hkl
          hik.symm hml hmi hil.symm h habs
      · exact absurd h hm2
  · -- no point in any triangle of three others: the hull is a pentagon
    push_neg at hA
    have hnz : ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
        sig (v i) (v j) (v k) ≠ 0 := by
      intro i j k hij hik hjk h0
      obtain ⟨m, hmi, hmj, hmk, _⟩ :=
        (by decide : ∀ (i j k l : Fin 5), ∃ m, m ≠ i ∧ m ≠ j ∧ m ≠ k ∧ m ≠ l)
          i j k k
      rcases collinear_between (v i) (v j) (v k) (v m) h0 with h | h | h
      · exact hA i j k m hij hik hmi.symm hjk hmj.symm hmk.symm h
      · exact hA j i k m hij.symm hjk hmj.symm hik hmi.symm hmk.symm h
      · exact hA k i j m hik.symm hjk.symm hmk.symm hij hmi.symm hmj.symm h
    have step : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
        c ≠ d → a ≠ 4 → b ≠ 4 → c ≠ 4 → d ≠ 4 →
        QuadCCW (v a) (v b) (v c) (v d) → ∃ H, IsHullArea v H := by
      intro a b c d hab hac had hbc hbd hcd ha4 hb4 hc4 hd4 hq
      obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
      have s1 := lt_of_le_of_ne hq1 (Ne.symm (hnz a b c hab hac hbc))
      have s2 := lt_of_le_of_ne hq2 (Ne.symm (hnz a b d hab had hbd))
      have s3 := lt_of_le_of_ne hq3 (Ne.symm (hnz a c d hac had hcd))
      have s4 := lt_of_le_of_ne hq4 (Ne.symm (hnz b c d hbc hbd hcd))
      rcases insert_or_absorb (v a) (v b) (v c) (v d) (v 4) s1 s2 s3 s4
          (hnz a b 4 hab ha4 hb4) (hnz b c 4 hbc hb4 hc4)
          (hnz c d 4 hcd hc4 hd4) (hnz d a 4 had.symm hd4 ha4)
          (hA 4 a b c ha4.symm hb4.symm hc4.symm hab hac hbc)
          (hA 4 a c d ha4.symm hc4.symm hd4.symm hac had hcd)
          (hA b a c 4 hab.symm hbc hb4 hac ha4 hc4)
          (hA c b d 4 hbc.symm hcd hc4 hbd hb4 hd4)
          (hA d c a 4 hcd.symm had.symm hd4 hac.symm hc4 ha4)
          (hA a d b 4 had hab ha4 hbd.symm hd4 hb4)
          with h | h | h | h
      · exact pent_pack v a b c d 4 hab hac had ha4 hbc hbd hb4 hcd hc4 hd4 h
      · exact pent_pack v b c d a 4 hbc hbd hab.symm hb4 hcd hac.symm hc4
          had.symm hd4 ha4 h
      · exact pent_pack v c d a b 4 hcd hac.symm hbc.symm hc4 had.symm
          hbd.symm hd4 hab ha4 hb4 h
      · exact pent_pack v d a b c 4 had.symm hbd.symm hcd.symm hd4 hab hac
          ha4 hbc hb4 hc4 h
    rcases radon4 (v 0) (v 1) (v 2) (v 3) with
      (hq | hq | hq | hq | hq | hq) | (h | h | h | h)
    · exact step 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hq
    · exact step 0 1 3 2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hq
    · exact step 0 2 1 3 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hq
    · exact step 0 3 2 1 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hq
    · exact step 0 2 3 1 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hq
    · exact step 0 3 1 2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hq
    · exact absurd h (hA 0 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
    · exact absurd h (hA 1 0 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
    · exact absurd h (hA 2 0 1 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
    · exact absurd h (hA 3 0 1 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))

end Heilbronn5
