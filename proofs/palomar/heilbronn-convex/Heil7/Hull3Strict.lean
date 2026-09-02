import Heil7.Hull3CountingRoute

/-!
# Strictness of the hull-three counting route

The nine-cell counting bound for four points in a triangular hull is never an
equality for the canonical minimum over all thirty-five triples.  Equality
would make the three fan areas at every interior point odd multiples of the
minimum.  The resulting ten possible barycentric codes have a compatibility
graph consisting of three disjoint edges, so three distinct interior points
cannot coexist.

This argument deliberately uses mixed triples that need not be cells of one
fixed triangulation.  General position alone does not force the nine cells of
a chosen triangulation to have unequal areas.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-! ### The ten odd barycentric codes -/

/-- Positive odd triples with sum nine, named by their three entries. -/
private inductive OddCode where
  | c711 | c171 | c117
  | c531 | c513 | c351 | c153 | c315 | c135
  | c333
  deriving DecidableEq

private def OddCode.x : OddCode → ℕ
  | .c711 => 7 | .c171 => 1 | .c117 => 1
  | .c531 => 5 | .c513 => 5 | .c351 => 3
  | .c153 => 1 | .c315 => 3 | .c135 => 1
  | .c333 => 3

private def OddCode.y : OddCode → ℕ
  | .c711 => 1 | .c171 => 7 | .c117 => 1
  | .c531 => 3 | .c513 => 1 | .c351 => 5
  | .c153 => 5 | .c315 => 1 | .c135 => 3
  | .c333 => 3

private def OddCode.z : OddCode → ℕ
  | .c711 => 1 | .c171 => 1 | .c117 => 7
  | .c531 => 1 | .c513 => 3 | .c351 => 1
  | .c153 => 3 | .c315 => 5 | .c135 => 5
  | .c333 => 3

/-- The six mixed codes pair by fixing the coordinate containing `3` and
swapping the coordinates containing `1` and `5`.  The other four codes have no
compatible partner. -/
private def OddCode.partner : OddCode → Option OddCode
  | .c531 => some .c135
  | .c135 => some .c531
  | .c513 => some .c153
  | .c153 => some .c513
  | .c351 => some .c315
  | .c315 => some .c351
  | _ => none

/-- All three mixed triangles through the hull vertices have at least the
minimum exactly when all three `2 x 2` barycentric minors have magnitude at
least nine. -/
private def OddCode.Compatible (u w : OddCode) : Prop :=
  (9 : ℝ) ≤
      |(u.y : ℝ) * (w.z : ℝ) - (u.z : ℝ) * (w.y : ℝ)| ∧
  (9 : ℝ) ≤
      |(u.z : ℝ) * (w.x : ℝ) - (u.x : ℝ) * (w.z : ℝ)| ∧
  (9 : ℝ) ≤
      |(u.x : ℝ) * (w.y : ℝ) - (u.y : ℝ) * (w.x : ℝ)|

/-- Explicit finite computation of the compatibility graph. -/
private lemma OddCode.compatible_iff_partner (u w : OddCode) :
    u.Compatible w ↔ u.partner = some w := by
  cases u <;> cases w <;>
    norm_num [OddCode.Compatible, OddCode.partner, OddCode.x, OddCode.y,
      OddCode.z] <;>
    simp

/-- A code has at most one compatible partner. -/
private lemma OddCode.compatible_right_unique (u w₁ w₂ : OddCode)
    (h₁ : u.Compatible w₁) (h₂ : u.Compatible w₂) : w₁ = w₂ := by
  rw [OddCode.compatible_iff_partner] at h₁ h₂
  exact Option.some.inj (h₁.symm.trans h₂)

/-- The three sector counts sum to three, so doubling them and adding one
produces exactly one of the ten odd codes. -/
private lemma oddCode_of_counts (a b c : ℕ) (hsum : a + b + c = 3) :
    ∃ u : OddCode, u.x = 2 * a + 1 ∧ u.y = 2 * b + 1 ∧
      u.z = 2 * c + 1 := by
  have hcases :
      (a = 3 ∧ b = 0 ∧ c = 0) ∨
      (a = 0 ∧ b = 3 ∧ c = 0) ∨
      (a = 0 ∧ b = 0 ∧ c = 3) ∨
      (a = 2 ∧ b = 1 ∧ c = 0) ∨
      (a = 2 ∧ b = 0 ∧ c = 1) ∨
      (a = 1 ∧ b = 2 ∧ c = 0) ∨
      (a = 0 ∧ b = 2 ∧ c = 1) ∨
      (a = 1 ∧ b = 0 ∧ c = 2) ∨
      (a = 0 ∧ b = 1 ∧ c = 2) ∨
      (a = 1 ∧ b = 1 ∧ c = 1) := by
    have ha : a ≤ 3 := by omega
    have hb : b ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;> omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨.c711, rfl, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨.c171, rfl, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨.c117, rfl, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨.c531, rfl, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨.c513, rfl, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨.c351, rfl, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨.c153, rfl, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨.c315, rfl, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨.c135, rfl, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨.c333, rfl, rfl, rfl⟩

/-! ### Fan partition from positive barycentric coordinates -/

/-- If `p` has three positive barycentric coordinates and `q` lies in the
same outer triangle, then `q` belongs to one of the three fan sectors at `p`.
The proof chooses the least of `qx/px`, `qy/py`, and `qz/pz`. -/
private lemma inTri_fan_partition
    (p q A B C : ℝ × ℝ)
    (px py pz : ℝ) (hpx_pos : 0 < px) (hpy_pos : 0 < py)
    (hpz_pos : 0 < pz) (hpsum : px + py + pz = 1)
    (hp_eq : p = px • A + py • B + pz • C)
    (hq : HullBridge.InTri q A B C) :
    HullBridge.InTri q p A B ∨ HullBridge.InTri q p B C ∨
      HullBridge.InTri q p C A := by
  obtain ⟨qx, qy, qz, hqx, hqy, hqz, hqsum, hq_eq⟩ := hq
  have in_pAB (hca : qz / pz ≤ qx / px) (hcb : qz / pz ≤ qy / py) :
      HullBridge.InTri q p A B := by
    let t := qz / pz
    have ht : 0 ≤ t := div_nonneg hqz hpz_pos.le
    have htx : t * px ≤ qx := by
      exact (le_div_iff₀ hpx_pos).mp (by simpa [t] using hca)
    have hty : t * py ≤ qy := by
      exact (le_div_iff₀ hpy_pos).mp (by simpa [t] using hcb)
    have htz : t * pz = qz := by
      dsimp [t]
      field_simp [hpz_pos.ne']
    refine ⟨t, qx - t * px, qy - t * py, ht, by linarith,
      by linarith, ?_, ?_⟩
    · nlinarith
    · rw [hp_eq, hq_eq, ← htz]
      module
  have in_pBC (hab : qx / px ≤ qy / py) (hac : qx / px ≤ qz / pz) :
      HullBridge.InTri q p B C := by
    let t := qx / px
    have ht : 0 ≤ t := div_nonneg hqx hpx_pos.le
    have hty : t * py ≤ qy := by
      exact (le_div_iff₀ hpy_pos).mp (by simpa [t] using hab)
    have htz : t * pz ≤ qz := by
      exact (le_div_iff₀ hpz_pos).mp (by simpa [t] using hac)
    have htx : t * px = qx := by
      dsimp [t]
      field_simp [hpx_pos.ne']
    refine ⟨t, qy - t * py, qz - t * pz, ht, by linarith,
      by linarith, ?_, ?_⟩
    · nlinarith
    · rw [hp_eq, hq_eq, ← htx]
      module
  have in_pCA (hba : qy / py ≤ qx / px) (hbc : qy / py ≤ qz / pz) :
      HullBridge.InTri q p C A := by
    let t := qy / py
    have ht : 0 ≤ t := div_nonneg hqy hpy_pos.le
    have htx : t * px ≤ qx := by
      exact (le_div_iff₀ hpx_pos).mp (by simpa [t] using hba)
    have htz : t * pz ≤ qz := by
      exact (le_div_iff₀ hpz_pos).mp (by simpa [t] using hbc)
    have hty : t * py = qy := by
      dsimp [t]
      field_simp [hpy_pos.ne']
    refine ⟨t, qz - t * pz, qx - t * px, ht, by linarith,
      by linarith, ?_, ?_⟩
    · nlinarith
    · rw [hp_eq, hq_eq, ← hty]
      module
  by_cases hab : qx / px ≤ qy / py
  · by_cases hac : qx / px ≤ qz / pz
    · exact Or.inr (Or.inl (in_pBC hab hac))
    · have hca : qz / pz ≤ qx / px := le_of_not_ge hac
      exact Or.inl (in_pAB hca (hca.trans hab))
  · have hba : qy / py ≤ qx / px := le_of_not_ge hab
    by_cases hbc : qy / py ≤ qz / pz
    · exact Or.inr (Or.inr (in_pCA hba hbc))
    · have hcb : qz / pz ≤ qy / py := le_of_not_ge hbc
      exact Or.inl (in_pAB (hcb.trans hba) hcb)

/-! ### Equality forces an odd code at every interior point -/

/-- Equality in the nine-cell bound quantizes the three fan areas at any
chosen interior point. -/
private lemma oddCode_of_counting_equality
    (v : Configuration7) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      m ≤ |HullBridge.sig (v i) (v j) (v k)|)
    (A B C p : Fin 7) (t : Finset (Fin 7))
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hpA : p ≠ A) (hpB : p ≠ B) (hpC : p ≠ C)
    (hAt : A ∉ t) (hBt : B ∉ t) (hCt : C ∉ t) (hpt : p ∉ t)
    (htcard : t.card = 3)
    (hH : 0 < HullBridge.sig (v A) (v B) (v C))
    (hp_in : HullBridge.InTri (v p) (v A) (v B) (v C))
    (ht_in : ∀ q ∈ t, HullBridge.InTri (v q) (v A) (v B) (v C))
    (heq : 9 * m = HullBridge.sig (v A) (v B) (v C)) :
    ∃ u : OddCode,
      HullBridge.sig (v p) (v B) (v C) = (u.x : ℝ) * m ∧
      HullBridge.sig (v p) (v C) (v A) = (u.y : ℝ) * m ∧
      HullBridge.sig (v p) (v A) (v B) = (u.z : ℝ) * m := by
  classical
  obtain ⟨px, py, pz, hpx, hpy, hpz, hpsum, hp_eq⟩ := hp_in
  have hpBC_coeff : HullBridge.sig (v p) (v B) (v C) =
      px * HullBridge.sig (v A) (v B) (v C) := by
    calc
      HullBridge.sig (v p) (v B) (v C) =
          HullBridge.sig (v B) (v C) (v p) :=
        HullBridge.sig_rotate (v p) (v B) (v C)
      _ = px * HullBridge.sig (v A) (v B) (v C) := by
        rw [hp_eq, HullBridge.sig_affine_third (v B) (v C)
          (v A) (v B) (v C) px py pz hpsum]
        simp only [HullBridge.sig]
        ring
  have hpCA_coeff : HullBridge.sig (v p) (v C) (v A) =
      py * HullBridge.sig (v A) (v B) (v C) := by
    calc
      HullBridge.sig (v p) (v C) (v A) =
          HullBridge.sig (v C) (v A) (v p) :=
        HullBridge.sig_rotate (v p) (v C) (v A)
      _ = py * HullBridge.sig (v A) (v B) (v C) := by
        rw [hp_eq, HullBridge.sig_affine_third (v C) (v A)
          (v A) (v B) (v C) px py pz hpsum]
        simp only [HullBridge.sig]
        ring
  have hpAB_coeff : HullBridge.sig (v p) (v A) (v B) =
      pz * HullBridge.sig (v A) (v B) (v C) := by
    calc
      HullBridge.sig (v p) (v A) (v B) =
          HullBridge.sig (v A) (v B) (v p) :=
        HullBridge.sig_rotate (v p) (v A) (v B)
      _ = pz * HullBridge.sig (v A) (v B) (v C) := by
        rw [hp_eq, HullBridge.sig_affine_third (v A) (v B)
          (v A) (v B) (v C) px py pz hpsum]
        simp only [HullBridge.sig]
        ring
  have hpx_pos : 0 < px := by
    have hb := hmin p B C hpB hpC hBC
    rw [hpBC_coeff] at hb
    by_contra hn
    have : px = 0 := le_antisymm (le_of_not_gt hn) hpx
    simp [this] at hb
    linarith
  have hpy_pos : 0 < py := by
    have hb := hmin p C A hpC hpA hAC.symm
    rw [hpCA_coeff] at hb
    by_contra hn
    have : py = 0 := le_antisymm (le_of_not_gt hn) hpy
    simp [this] at hb
    linarith
  have hpz_pos : 0 < pz := by
    have hb := hmin p A B hpA hpB hAB
    rw [hpAB_coeff] at hb
    by_contra hn
    have : pz = 0 := le_antisymm (le_of_not_gt hn) hpz
    simp [this] at hb
    linarith
  let tAB := t.filter (fun q => HullBridge.InTri (v q) (v p) (v A) (v B))
  let tBC :=
    (t.filter (fun q => ¬HullBridge.InTri (v q) (v p) (v A) (v B))).filter
      (fun q => HullBridge.InTri (v q) (v p) (v B) (v C))
  let tCA :=
    (t.filter (fun q => ¬HullBridge.InTri (v q) (v p) (v A) (v B))).filter
      (fun q => ¬HullBridge.InTri (v q) (v p) (v B) (v C))
  have htAB_sub : tAB ⊆ t := Finset.filter_subset _ _
  have htBC_sub : tBC ⊆ t := by
    intro q hq
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have htCA_sub : tCA ⊆ t := by
    intro q hq
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have htAB_in : ∀ q ∈ tAB,
      HullBridge.InTri (v q) (v p) (v A) (v B) := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have htBC_in : ∀ q ∈ tBC,
      HullBridge.InTri (v q) (v p) (v B) (v C) := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have htCA_in : ∀ q ∈ tCA,
      HullBridge.InTri (v q) (v p) (v C) (v A) := by
    intro q hq
    have hqo := Finset.mem_filter.mp hq
    have hqi := Finset.mem_filter.mp hqo.1
    have hfan := inTri_fan_partition (v p) (v q) (v A) (v B) (v C)
      px py pz hpx_pos hpy_pos hpz_pos hpsum hp_eq
      (ht_in q (htCA_sub hq))
    rcases hfan with h1 | h2 | h3
    · exact (hqi.2 h1).elim
    · exact (hqo.2 h2).elim
    · exact h3
  have hparts : tAB.card + tBC.card + tCA.card = 3 := by
    have hpartition : tAB.card + tBC.card + tCA.card = t.card := by
      calc
        tAB.card + tBC.card + tCA.card =
            tAB.card + (tBC.card + tCA.card) := by omega
        _ = tAB.card +
            (t.filter (fun q =>
              ¬HullBridge.InTri (v q) (v p) (v A) (v B))).card := by
          rw [Finset.card_filter_add_card_filter_not]
        _ = t.card := Finset.card_filter_add_card_filter_not _
    omega
  have hpAB_pos : 0 < HullBridge.sig (v p) (v A) (v B) := by
    rw [hpAB_coeff]
    positivity
  have hpBC_pos : 0 < HullBridge.sig (v p) (v B) (v C) := by
    rw [hpBC_coeff]
    positivity
  have hpCA_pos : 0 < HullBridge.sig (v p) (v C) (v A) := by
    rw [hpCA_coeff]
    positivity
  have hABcount := HullBridge.interior_count_bound v m hm hmin tAB p A B
    hpA hpB hAB
    (fun h => hpt (htAB_sub h))
    (fun h => hAt (htAB_sub h))
    (fun h => hBt (htAB_sub h)) hpAB_pos htAB_in
  have hBCcount := HullBridge.interior_count_bound v m hm hmin tBC p B C
    hpB hpC hBC
    (fun h => hpt (htBC_sub h))
    (fun h => hBt (htBC_sub h))
    (fun h => hCt (htBC_sub h)) hpBC_pos htBC_in
  have hCAcount := HullBridge.interior_count_bound v m hm hmin tCA p C A
    hpC hpA hAC.symm
    (fun h => hpt (htCA_sub h))
    (fun h => hCt (htCA_sub h))
    (fun h => hAt (htCA_sub h)) hpCA_pos htCA_in
  have hfan :
      HullBridge.sig (v p) (v A) (v B) +
        HullBridge.sig (v p) (v B) (v C) +
        HullBridge.sig (v p) (v C) (v A) =
          HullBridge.sig (v A) (v B) (v C) := by
    simp only [HullBridge.sig]
    ring
  have hcoef :
      ((2 * tAB.card + 1 : ℕ) : ℝ) +
        ((2 * tBC.card + 1 : ℕ) : ℝ) +
        ((2 * tCA.card + 1 : ℕ) : ℝ) = 9 := by
    exact_mod_cast (show
      (2 * tAB.card + 1) + (2 * tBC.card + 1) +
        (2 * tCA.card + 1) = 9 by omega)
  have hweighted :
      ((2 * tAB.card + 1 : ℕ) : ℝ) * m +
        ((2 * tBC.card + 1 : ℕ) : ℝ) * m +
        ((2 * tCA.card + 1 : ℕ) : ℝ) * m = 9 * m := by
    rw [← hcoef]
    ring
  have hABeq : HullBridge.sig (v p) (v A) (v B) =
      (2 * tAB.card + 1) * m := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hABcount hBCcount hCAcount hweighted ⊢
    linarith [hfan, heq, hweighted]
  have hBCeq : HullBridge.sig (v p) (v B) (v C) =
      (2 * tBC.card + 1) * m := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hABcount hBCcount hCAcount hweighted ⊢
    linarith [hfan, heq, hweighted]
  have hCAeq : HullBridge.sig (v p) (v C) (v A) =
      (2 * tCA.card + 1) * m := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hABcount hBCcount hCAcount hweighted ⊢
    linarith [hfan, heq, hweighted]
  obtain ⟨u, hux, huy, huz⟩ :=
    oddCode_of_counts tBC.card tCA.card tAB.card (by omega)
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [hux]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hBCeq
  · rw [huy]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hCAeq
  · rw [huz]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hABeq

/-! ### Pluecker compatibility -/

private lemma pluecker_A (A B C p q : ℝ × ℝ) :
    HullBridge.sig A B C * HullBridge.sig A p q =
      HullBridge.sig p C A * HullBridge.sig q A B -
        HullBridge.sig p A B * HullBridge.sig q C A := by
  simp only [HullBridge.sig]
  ring

private lemma pluecker_B (A B C p q : ℝ × ℝ) :
    HullBridge.sig A B C * HullBridge.sig B p q =
      HullBridge.sig p A B * HullBridge.sig q B C -
        HullBridge.sig p B C * HullBridge.sig q A B := by
  simp only [HullBridge.sig]
  ring

private lemma pluecker_C (A B C p q : ℝ × ℝ) :
    HullBridge.sig A B C * HullBridge.sig C p q =
      HullBridge.sig p B C * HullBridge.sig q C A -
        HullBridge.sig p C A * HullBridge.sig q B C := by
  simp only [HullBridge.sig]
  ring

private lemma nine_le_abs_cross (m s d : ℝ) (hm : 0 < m)
    (hid : 9 * s = d * m) (hmin : m ≤ |s|) : 9 ≤ |d| := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs] at hmin
    have hd : 0 ≤ d := by nlinarith
    rw [abs_of_nonneg hd]
    nlinarith
  · rw [abs_of_nonpos hs] at hmin
    have hd : d ≤ 0 := by nlinarith
    rw [abs_of_nonpos hd]
    nlinarith

/-- Fan codes at two points are compatible because all three mixed triangles
through a hull vertex are bounded below by `m`. -/
private lemma compatible_of_fan_codes
    (A B C p q : ℝ × ℝ) (m : ℝ) (hm : 0 < m)
    (heq : 9 * m = HullBridge.sig A B C)
    (u w : OddCode)
    (hpBC : HullBridge.sig p B C = (u.x : ℝ) * m)
    (hpCA : HullBridge.sig p C A = (u.y : ℝ) * m)
    (hpAB : HullBridge.sig p A B = (u.z : ℝ) * m)
    (hqBC : HullBridge.sig q B C = (w.x : ℝ) * m)
    (hqCA : HullBridge.sig q C A = (w.y : ℝ) * m)
    (hqAB : HullBridge.sig q A B = (w.z : ℝ) * m)
    (hA : m ≤ |HullBridge.sig A p q|)
    (hB : m ≤ |HullBridge.sig B p q|)
    (hC : m ≤ |HullBridge.sig C p q|) : u.Compatible w := by
  have hplA := pluecker_A A B C p q
  have hplB := pluecker_B A B C p q
  have hplC := pluecker_C A B C p q
  rw [hpCA, hqAB, hpAB, hqCA] at hplA
  rw [hpAB, hqBC, hpBC, hqAB] at hplB
  rw [hpBC, hqCA, hpCA, hqBC] at hplC
  have hidA : 9 * HullBridge.sig A p q =
      ((u.y : ℝ) * (w.z : ℝ) - (u.z : ℝ) * (w.y : ℝ)) * m := by
    have hfactor : m *
        (9 * HullBridge.sig A p q -
          ((u.y : ℝ) * (w.z : ℝ) - (u.z : ℝ) * (w.y : ℝ)) * m) = 0 := by
      calc
        _ = (9 * m) * HullBridge.sig A p q -
            (((u.y : ℝ) * m) * ((w.z : ℝ) * m) -
              ((u.z : ℝ) * m) * ((w.y : ℝ) * m)) := by ring
        _ = 0 := by rw [heq]; linarith
    rcases mul_eq_zero.mp hfactor with hzero | hrest
    · exact (hm.ne' hzero).elim
    · linarith
  have hidB : 9 * HullBridge.sig B p q =
      ((u.z : ℝ) * (w.x : ℝ) - (u.x : ℝ) * (w.z : ℝ)) * m := by
    have hfactor : m *
        (9 * HullBridge.sig B p q -
          ((u.z : ℝ) * (w.x : ℝ) - (u.x : ℝ) * (w.z : ℝ)) * m) = 0 := by
      calc
        _ = (9 * m) * HullBridge.sig B p q -
            (((u.z : ℝ) * m) * ((w.x : ℝ) * m) -
              ((u.x : ℝ) * m) * ((w.z : ℝ) * m)) := by ring
        _ = 0 := by rw [heq]; linarith
    rcases mul_eq_zero.mp hfactor with hzero | hrest
    · exact (hm.ne' hzero).elim
    · linarith
  have hidC : 9 * HullBridge.sig C p q =
      ((u.x : ℝ) * (w.y : ℝ) - (u.y : ℝ) * (w.x : ℝ)) * m := by
    have hfactor : m *
        (9 * HullBridge.sig C p q -
          ((u.x : ℝ) * (w.y : ℝ) - (u.y : ℝ) * (w.x : ℝ)) * m) = 0 := by
      calc
        _ = (9 * m) * HullBridge.sig C p q -
            (((u.x : ℝ) * m) * ((w.y : ℝ) * m) -
              ((u.y : ℝ) * m) * ((w.x : ℝ) * m)) := by ring
        _ = 0 := by rw [heq]; linarith
    rcases mul_eq_zero.mp hfactor with hzero | hrest
    · exact (hm.ne' hzero).elim
    · linarith
  exact ⟨nine_le_abs_cross m _ _ hm hidA hA,
    nine_le_abs_cross m _ _ hm hidB hB,
    nine_le_abs_cross m _ _ hm hidC hC⟩

/-! ### Strict hull-three route -/

/-- The triangular-hull counting bound is pointwise strict.  If the canonical
minimum vanishes this is immediate; otherwise equality would assign odd fan
codes to three interior points, contradicting uniqueness of compatible codes.
-/
theorem hullThree_counting_strict :
    ∀ (v : Configuration7), HullCCW v 3 →
      (∀ p : Fin 7, 3 ≤ (p : ℕ) → InHullN v 3 p) →
      9 * minTri v < fanArea v 3 := by
  intro v hccw hinHull
  have hle := hullThree_counting v hccw hinHull
  have h012 : 0 < HullBridge.sig (v 0) (v 1) (v 2) := by
    have h := hccw 0 1 2 (by decide) (by decide) (by norm_num)
    simpa only [HullBridge.sig, sig] using h
  by_contra hnstrict
  have hreverse : fanArea v 3 ≤ 9 * minTri v := le_of_not_gt hnstrict
  have heq_fan : 9 * minTri v = fanArea v 3 := le_antisymm hle hreverse
  have heq : 9 * minTri v = HullBridge.sig (v 0) (v 1) (v 2) := by
    simpa only [fanArea, HullBridge.sig, sig] using heq_fan
  have hmpos : 0 < minTri v := by nlinarith
  have hmin : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      minTri v ≤ |HullBridge.sig (v i) (v j) (v k)| := by
    intro i j k hij hik hjk
    exact minTri_le_of_distinct v i j k hij hik hjk
  have hrotate : ∀ a b c : ℝ × ℝ, sig a b c = sig b c a := by
    intro a b c
    simp only [sig]
    ring
  have hinside : ∀ p ∈ ({3, 4, 5, 6} : Finset (Fin 7)),
      HullBridge.InTri (v p) (v 0) (v 1) (v 2) := by
    intro p hp
    have hp_ge : 3 ≤ (p : ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> norm_num
    obtain ⟨hsides, hclose⟩ := hinHull p hp_ge
    have h01 : 0 < sig (v 0) (v 1) (v p) := by
      simpa using hsides 0 (by norm_num)
    have h12 : 0 < sig (v 1) (v 2) (v p) := by
      simpa using hsides 1 (by norm_num)
    have h20 : 0 < sig (v 2) (v 0) (v p) := by
      simpa using hclose 2 (by norm_num)
    apply HullBridge.inTri_of_sig (v p) (v 0) (v 1) (v 2) h012
    · simpa only [HullBridge.sig, sig] using (show 0 ≤ sig (v p) (v 1) (v 2) by
        rw [hrotate]
        exact h12.le)
    · simpa only [HullBridge.sig, sig] using (show 0 ≤ sig (v 0) (v p) (v 2) by
        rw [hrotate, hrotate]
        exact h20.le)
    · simpa only [HullBridge.sig, sig] using h01.le
  have code3 := oddCode_of_counting_equality v (minTri v) hmpos hmin
    0 1 2 3 ({4, 5, 6} : Finset (Fin 7))
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) h012
    (hinside 3 (by decide))
    (by
      intro q hq
      apply hinside q
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      aesop)
    heq
  have code4 := oddCode_of_counting_equality v (minTri v) hmpos hmin
    0 1 2 4 ({3, 5, 6} : Finset (Fin 7))
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) h012
    (hinside 4 (by decide))
    (by
      intro q hq
      apply hinside q
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      aesop)
    heq
  have code5 := oddCode_of_counting_equality v (minTri v) hmpos hmin
    0 1 2 5 ({3, 4, 6} : Finset (Fin 7))
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) h012
    (hinside 5 (by decide))
    (by
      intro q hq
      apply hinside q
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      aesop)
    heq
  obtain ⟨u3, h3BC, h3CA, h3AB⟩ := code3
  obtain ⟨u4, h4BC, h4CA, h4AB⟩ := code4
  obtain ⟨u5, h5BC, h5CA, h5AB⟩ := code5
  have hc34 : u3.Compatible u4 := compatible_of_fan_codes
    (v 0) (v 1) (v 2) (v 3) (v 4) (minTri v) hmpos heq u3 u4
    h3BC h3CA h3AB h4BC h4CA h4AB
    (hmin 0 3 4 (by decide) (by decide) (by decide))
    (hmin 1 3 4 (by decide) (by decide) (by decide))
    (hmin 2 3 4 (by decide) (by decide) (by decide))
  have hc35 : u3.Compatible u5 := compatible_of_fan_codes
    (v 0) (v 1) (v 2) (v 3) (v 5) (minTri v) hmpos heq u3 u5
    h3BC h3CA h3AB h5BC h5CA h5AB
    (hmin 0 3 5 (by decide) (by decide) (by decide))
    (hmin 1 3 5 (by decide) (by decide) (by decide))
    (hmin 2 3 5 (by decide) (by decide) (by decide))
  have hu45 : u4 = u5 := u3.compatible_right_unique u4 u5 hc34 hc35
  have hAB45 : HullBridge.sig (v 0) (v 1) (v 4) =
      HullBridge.sig (v 0) (v 1) (v 5) := by
    rw [← HullBridge.sig_rotate (v 4) (v 0) (v 1),
      ← HullBridge.sig_rotate (v 5) (v 0) (v 1), h4AB, h5AB, hu45]
  have hA4C5 : HullBridge.sig (v 0) (v 4) (v 2) =
      HullBridge.sig (v 0) (v 5) (v 2) := by
    rw [HullBridge.sig_rotate (v 0) (v 4) (v 2),
      HullBridge.sig_rotate (v 0) (v 5) (v 2), h4CA, h5CA, hu45]
  have hv45 : v 4 = v 5 := HullBridge.point_unique_of_sigs
    (v 0) (v 1) (v 2) (v 4) (v 5) h012.ne' hAB45 hA4C5
  have hsmall := hmin 4 5 0 (by decide) (by decide) (by decide)
  rw [hv45, HullBridge.sig_self_left, abs_zero] at hsmall
  linarith

end HeilbronnChallenge.N7Upper
