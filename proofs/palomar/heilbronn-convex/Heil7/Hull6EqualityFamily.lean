import Heil7.Hull6EqualitySignRigidity
import Heil7.Hull6TightPointClassification
import Heil7.OptimizerEqualityRouting

/-!
# Hull-six equality data belongs to the optimizer family

Sign rigidity leaves the two orientations of the alternating tight chamber.
The first is the literal chamber used by `Hull6TightPointClassification`.
For the second we cyclically move hull vertex zero to the final hull slot,
leaving the interior point in slot six.  At array level this turns the second
alternating sign pattern into the first one; only the two ordinary hull rows
`123` and `234` are needed to recover the exact equality parameter interval.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- One positive cyclic step on the six hull labels, fixing the interior
label. -/
def h6EqualityRotate : Equiv.Perm (Fin 7) where
  toFun := ![1, 2, 3, 4, 5, 0, 6]
  invFun := ![5, 0, 1, 2, 3, 4, 6]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Complete the hull-six equality packet to the public affine optimizer
family. -/
theorem hullSixEqualityData_exists_family
    (w : Configuration7) (hdata : HullSixEqualityData w) :
    ∃ t : ℝ, 1 ≤ t ∧ t ≤ 4 / 3 ∧
      AffineEquivalent (sevenFamilyAt t) w := by
  let m : ℝ := minTri w
  let b : Fin 6 → Fin 6 → ℝ := h6PointBracket w
  let a : Fin 6 → ℝ := fun i => b i (i + 1)
  let d : Fin 6 → ℝ := fun i => b i (i + 2)
  let c : Fin 6 → ℝ := fun i => b i (i + 3)
  have hm : 0 < m := by simpa only [m] using hdata.minTri_pos
  have hskew : ∀ i j, b i j = -b j i := by
    intro i j
    simp only [b, h6PointBracket, sig]
    ring
  have hgp : ∀ i j k l,
      b i j * b k l - b i k * b j l + b i l * b j k = 0 := by
    intro i j k l
    simp only [b, h6PointBracket, sig]
    ring
  have hcast6 : ∀ i : Fin 6, i.castSucc ≠ (6 : Fin 7) := by
    intro i hieq
    have hval := congrArg Fin.val hieq
    change i.val = 6 at hval
    omega
  have hradial : ∀ i j, i ≠ j → m ≤ |b i j| := by
    intro i j hij
    exact minTri_le_of_distinct w i.castSucc j.castSucc 6
      ((Fin.castSucc_injective 6).ne hij) (hcast6 i) (hcast6 j)
  have hhull : ∀ i j k : Fin 6, i < j → j < k →
      m ≤ b i j + b j k - b i k := by
    intro i j k hij hjk
    have hpos : 0 < sig (w i.castSucc) (w j.castSucc) (w k.castSucc) :=
      hdata.hullCCW i.castSucc j.castSucc k.castSucc
        (by simpa using hij) (by simpa using hjk) (by simpa using k.isLt)
    have hfloor := minTri_le_of_distinct w
      i.castSucc j.castSucc k.castSucc
      ((Fin.castSucc_injective 6).ne (ne_of_lt hij))
      ((Fin.castSucc_injective 6).ne (ne_of_lt (lt_trans hij hjk)))
      ((Fin.castSucc_injective 6).ne (ne_of_lt hjk))
    rw [abs_of_pos hpos] at hfloor
    have hid :
        b i j + b j k - b i k =
          sig (w i.castSucc) (w j.castSucc) (w k.castSucc) := by
      simp only [b, h6PointBracket, sig]
      ring
    simpa only [m, hid] using hfloor
  have hp6 := hdata.tail_inHull 6 (by norm_num)
  have hedge : ∀ i : Fin 6, 0 < b i (i + 1) := by
    intro i
    fin_cases i
    · simpa [b, h6PointBracket] using hp6.1 0 (by norm_num)
    · simpa [b, h6PointBracket] using hp6.1 1 (by norm_num)
    · simpa [b, h6PointBracket] using hp6.1 2 (by norm_num)
    · simpa [b, h6PointBracket] using hp6.1 3 (by norm_num)
    · simpa [b, h6PointBracket] using hp6.1 4 (by norm_num)
    · simpa [b, h6PointBracket] using hp6.2 5 (by norm_num)
  have hsum :
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 =
        fanArea w 6 := by
    have hcast0 : ((0 : Fin 6).castSucc : Fin 7) = 0 := by decide
    have hcast1 : ((1 : Fin 6).castSucc : Fin 7) = 1 := by decide
    have hcast2 : ((2 : Fin 6).castSucc : Fin 7) = 2 := by decide
    have hcast3 : ((3 : Fin 6).castSucc : Fin 7) = 3 := by decide
    have hcast4 : ((4 : Fin 6).castSucc : Fin 7) = 4 := by decide
    have hcast5 : ((5 : Fin 6).castSucc : Fin 7) = 5 := by decide
    simp only [b, h6PointBracket]
    rw [hcast0, hcast1, hcast2, hcast3, hcast4, hcast5]
    simp only [fanArea, sig]
    ring
  have heq :
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 = 9 * m := by
    calc
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 =
          fanArea w 6 := hsum
      _ = 9 * minTri w := hdata.bound_eq.symm
      _ = 9 * m := by rfl
  obtain ⟨hdall, hcalt⟩ :=
    h6_bracket_equality_signs m b hm hskew hgp hradial hhull hedge heq
  rcases hdall with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
  rcases hcalt with hcanonical | hopposite
  · rcases hcanonical with ⟨hc0, hc1, hc2⟩
    have hchamber : H6TightChamber b :=
      ⟨hd0, hd1, hd2, hd3, hd4, hd5, hc0, hc1, hc2⟩
    exact hullSix_tight_equality_exists_family w hdata.hullCCW
      hdata.tail_inHull hdata.minTri_pos
      (by simpa only [b] using hchamber) hdata.bound_eq.symm
  · rcases hopposite with ⟨hc0, hc1, hc2⟩
    have ha : ∀ i, m ≤ a i := by
      intro i
      have hf := hradial i (i + 1) (by fin_cases i <;> decide)
      rw [abs_of_pos (hedge i)] at hf
      exact hf
    have hdFloor : ∀ i, m ≤ d i := by
      intro i
      have hf := hradial i (i + 2) (by fin_cases i <;> decide)
      have hi : 0 < d i := by
        fin_cases i <;> assumption
      change m ≤ |d i| at hf
      rwa [abs_of_pos hi] at hf
    have hcPosFloor : ∀ i, 0 < c i → m ≤ c i := by
      intro i hi
      have hf := hradial i (i + 3) (by fin_cases i <;> decide)
      change m ≤ |c i| at hf
      rwa [abs_of_pos hi] at hf
    have hcNegFloor : ∀ i, c i < 0 → c i ≤ -m := by
      intro i hi
      have hf := hradial i (i + 3) (by fin_cases i <;> decide)
      change m ≤ |c i| at hf
      rw [abs_of_neg hi] at hf
      linarith
    have hcopp : ∀ i : Fin 6, c (i + 3) = -c i := by
      intro i
      fin_cases i
      · change b 3 0 = -b 0 3; exact hskew 3 0
      · change b 4 1 = -b 1 4; exact hskew 4 1
      · change b 5 2 = -b 2 5; exact hskew 5 2
      · change b 0 3 = -b 3 0; exact hskew 0 3
      · change b 1 4 = -b 4 1; exact hskew 1 4
      · change b 2 5 = -b 5 2; exact hskew 2 5
    have hrel : ∀ i : Fin 6,
        d i * d (i + 1) = a i * a (i + 2) + c i * a (i + 1) := by
      intro i
      fin_cases i
      · have hp := hgp 0 1 2 3
        change b 0 2 * b 1 3 = b 0 1 * b 2 3 + b 0 3 * b 1 2
        linarith
      · have hp := hgp 1 2 3 4
        change b 1 3 * b 2 4 = b 1 2 * b 3 4 + b 1 4 * b 2 3
        linarith
      · have hp := hgp 2 3 4 5
        change b 2 4 * b 3 5 = b 2 3 * b 4 5 + b 2 5 * b 3 4
        linarith
      · have hp := hgp 3 4 5 0
        change b 3 5 * b 4 0 = b 3 4 * b 5 0 + b 3 0 * b 4 5
        linarith
      · have hp := hgp 4 5 0 1
        change b 4 0 * b 5 1 = b 4 5 * b 0 1 + b 4 1 * b 5 0
        linarith
      · have hp := hgp 5 0 1 2
        change b 5 1 * b 0 2 = b 5 0 * b 1 2 + b 5 2 * b 0 1
        linarith
    let aR : Fin 6 → ℝ := fun i => a (1 + i)
    let dR : Fin 6 → ℝ := fun i => d (1 + i)
    let cR : Fin 6 → ℝ := fun i => c (1 + i)
    have haR : ∀ i, m ≤ aR i := fun i => ha (1 + i)
    have hdR : ∀ i, m ≤ dR i := fun i => hdFloor (1 + i)
    have hcR0 : m ≤ cR 0 := by
      change m ≤ c 1
      exact hcPosFloor 1 hc1
    have hcR1 : cR 1 ≤ -m := by
      change c 2 ≤ -m
      exact hcNegFloor 2 hc2
    have hcR2 : m ≤ cR 2 := by
      have hpos : 0 < c 3 := by
        have hop := hcopp 0
        change c 3 = -c 0 at hop
        linarith
      change m ≤ c 3
      exact hcPosFloor 3 hpos
    have hcR3 : cR 3 ≤ -m := by
      have hneg : c 4 < 0 := by
        have hop := hcopp 1
        change c 4 = -c 1 at hop
        linarith
      change c 4 ≤ -m
      exact hcNegFloor 4 hneg
    have hcR4 : m ≤ cR 4 := by
      have hpos : 0 < c 5 := by
        have hop := hcopp 2
        change c 5 = -c 2 at hop
        linarith
      change m ≤ c 5
      exact hcPosFloor 5 hpos
    have hcR5 : cR 5 ≤ -m := by
      change c 0 ≤ -m
      exact hcNegFloor 0 hc0
    have hrelR : ∀ i : Fin 6,
        dR i * dR (i + 1) =
          aR i * aR (i + 2) + cR i * aR (i + 1) := by
      intro i
      simpa only [aR, dR, cR, add_assoc, add_comm, add_left_comm] using
        hrel (1 + i)
    have h012R : m ≤ aR 0 + aR 1 - dR 0 := by
      have h := hhull 1 2 3 (by decide) (by decide)
      simpa [aR, dR, a, d] using h
    have h123R : m ≤ aR 1 + aR 2 - dR 1 := by
      have h := hhull 2 3 4 (by decide) (by decide)
      simpa [aR, dR, a, d] using h
    have heqR :
        aR 0 + aR 1 + aR 2 + aR 3 + aR 4 + aR 5 = 9 * m := by
      calc
        aR 0 + aR 1 + aR 2 + aR 3 + aR 4 + aR 5 =
            a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
          change a 1 + a 2 + a 3 + a 4 + a 5 + a 0 = _
          ring
        _ = 9 * m := by simpa [a] using heq
    obtain ⟨lambda, hlower, hupper, hpR⟩ :=
      h6_tight_array_equality_with_outer_floors m aR dR cR hm haR hdR
        hcR0 hcR1 hcR2 hcR3 hcR4 hcR5 hrelR h012R h123R heqR
    let wR : Configuration7 := w ∘ h6EqualityRotate
    have haPoint :
        (fun i => h6PointBracket wR i (i + 1)) = aR := by
      funext i
      fin_cases i <;>
        simp [wR, h6EqualityRotate, h6PointBracket, aR, a, b]
    have hdPoint :
        (fun i => h6PointBracket wR i (i + 2)) = dR := by
      funext i
      fin_cases i <;>
        simp [wR, h6EqualityRotate, h6PointBracket, dR, d, b]
    have hcPoint :
        (fun i => h6PointBracket wR i (i + 3)) = cR := by
      funext i
      fin_cases i <;>
        simp [wR, h6EqualityRotate, h6PointBracket, cR, c, b]
    have hpPoint : H6TightPacket m lambda
        (fun i => h6PointBracket wR i (i + 1))
        (fun i => h6PointBracket wR i (i + 2))
        (fun i => h6PointBracket wR i (i + 3)) := by
      rw [haPoint, hdPoint, hcPoint]
      exact hpR
    obtain ⟨T, hnormal⟩ := h6_tight_packet_point_normal_form
      wR m lambda hm hlower hupper hpPoint
    let u : Configuration7 := fun i => T.map (wR i)
    have hnormal' : Hull6TightNormalForm u m lambda := by
      simpa only [u] using hnormal
    obtain ⟨t, ht1, ht4, hfamily_u⟩ :=
      hnormal'.exists_family_affineEquivalent
    have hwR_u : GaugeEquivalent wR u := by
      refine ⟨Equiv.refl _, T, ?_⟩
      rfl
    have hfamily_wR : AffineEquivalent (sevenFamilyAt t) wR :=
      affineEquivalent_trans hfamily_u
        (affineEquivalent_symm (affineEquivalent_of_gaugeEquivalent hwR_u))
    have hw_wR : GaugeEquivalent w wR := by
      simpa only [wR] using gaugeEquivalent_relabel w h6EqualityRotate
    have hwR_w : AffineEquivalent wR w :=
      affineEquivalent_symm (affineEquivalent_of_gaugeEquivalent hw_wR)
    exact ⟨t, ht1, ht4, affineEquivalent_trans hfamily_wR hwR_w⟩

end HeilbronnChallenge.N7Upper
