import Heil7.Hull6TightEquality
import Heil7.N7OptimizerAffineReconstruction

/-!
# Point reconstruction from the tight hull-six equality packet

`Hull6TightEquality` deliberately stops at brackets.  This module constructs
the determinant-one affine normalizer at the interior point, turns the bracket
packet into `Hull6TightNormalForm`, and then invokes the public optimizer-family
reconstruction.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- Radial bracket of two hull vertices around point six. -/
def h6PointBracket (v : Configuration7) (i j : Fin 6) : ℝ :=
  sig (v i.castSucc) (v j.castSucc) (v 6)

/-- The determinant-one affine map which sends the interior point to zero and
the first two radial vectors to `(1,0)` and `(0,m)`. -/
noncomputable def h6TightPointNormalizer
    (m : ℝ) (p0 p1 o : ℝ × ℝ) (hm : 0 < m)
    (h01 : sig p0 p1 o = m) : PosAffine where
  a := (p1.2 - o.2) / m
  b := -(p1.1 - o.1) / m
  c := -(p0.2 - o.2)
  d := p0.1 - o.1
  tx := -((p1.2 - o.2) / m) * o.1 - (-(p1.1 - o.1) / m) * o.2
  ty := -(-(p0.2 - o.2)) * o.1 - (p0.1 - o.1) * o.2
  det_pos := by
    have hmne : m ≠ 0 := ne_of_gt hm
    have hid :
        ((p1.2 - o.2) / m) * (p0.1 - o.1) -
            (-(p1.1 - o.1) / m) * (-(p0.2 - o.2)) =
          sig p0 p1 o / m := by
      simp only [sig]
      field_simp [hmne]
      <;> ring
    rw [hid, h01]
    exact div_pos hm hm

/-- Coordinate formula for the normalizer.  It is just Cramer's rule in the
ordered radial basis `(p0-o,p1-o)`. -/
theorem h6TightPointNormalizer_map
    (m : ℝ) (p0 p1 o p : ℝ × ℝ) (hm : 0 < m)
    (h01 : sig p0 p1 o = m) :
    (h6TightPointNormalizer m p0 p1 o hm h01).map p =
      (-sig p1 p o / m, sig p0 p o) := by
  apply Prod.ext <;>
    simp [h6TightPointNormalizer, PosAffine.map, sig] <;>
    field_simp [ne_of_gt hm] <;> ring

@[simp] theorem h6TightPointNormalizer_center
    (m : ℝ) (p0 p1 o : ℝ × ℝ) (hm : 0 < m)
    (h01 : sig p0 p1 o = m) :
    (h6TightPointNormalizer m p0 p1 o hm h01).map o = (0, 0) := by
  rw [h6TightPointNormalizer_map]
  simp only [sig]
  apply Prod.ext <;> simp <;> ring

/-- The point-level reconstruction seam: every exact canonical bracket packet
has a positive-determinant affine image in the coordinate normal form used by
`N7OptimizerAffineReconstruction`. -/
theorem h6_tight_packet_point_normal_form
    (v : Configuration7) (m lambda : ℝ)
    (hm : 0 < m) (hlower : (3 : ℝ) / 2 ≤ lambda)
    (hupper : lambda ≤ 2)
    (hp : H6TightPacket m lambda
      (fun i => h6PointBracket v i (i + 1))
      (fun i => h6PointBracket v i (i + 2))
      (fun i => h6PointBracket v i (i + 3))) :
    ∃ T : PosAffine,
      Hull6TightNormalForm (fun i => T.map (v i)) m lambda := by
  rcases hp with ⟨ha0, ha1, ha2, ha3, ha4, ha5,
    hc0, hc1, hc2, hc3, hc4, hc5,
    hd0, hd1, hd2, hd3, hd4, hd5⟩
  let b : Fin 6 → Fin 6 → ℝ := h6PointBracket v
  have hskew : ∀ i j, b i j = -b j i := by
    intro i j
    simp only [b, h6PointBracket, sig]
    ring
  have hdiag : ∀ i, b i i = 0 := by
    intro i
    simp only [b, h6PointBracket, sig]
    ring
  have hb01 : b 0 1 = m := by simpa [b] using ha0
  have hb12 : b 1 2 = 2 * m := by simpa [b] using ha1
  have hb50 : b 5 0 = 2 * m := by simpa [b] using ha5
  have hb02 : b 0 2 = lambda * m := by simpa [b] using hd0
  have hb13 : b 1 3 = (3 / lambda) * m := by simpa [b] using hd1
  have hb40 : b 4 0 = lambda * m := by simpa [b] using hd4
  have hb51 : b 5 1 = (3 / lambda) * m := by simpa [b] using hd5
  have hb03 : b 0 3 = m := by simpa [b] using hc0
  have hb14 : b 1 4 = -m := by simpa [b] using hc1
  have h01 : sig (v 0) (v 1) (v 6) = m := by
    simpa [b, h6PointBracket] using hb01
  let T : PosAffine :=
    h6TightPointNormalizer m (v 0) (v 1) (v 6) hm h01
  have hmap (i : Fin 6) :
      T.map (v i.castSucc) = (-b 1 i / m, b 0 i) := by
    have h := h6TightPointNormalizer_map
      m (v 0) (v 1) (v 6) (v i.castSucc) hm h01
    convert h using 1 <;> norm_num [T, b, h6PointBracket]
  have hlambda : 0 < lambda :=
    lt_of_lt_of_le (by norm_num) hlower
  refine ⟨T, {
    m_pos := hm
    lambda_lower := hlower
    lambda_upper := hupper
    p0 := ?_
    p1 := ?_
    p2 := ?_
    p3 := ?_
    p4 := ?_
    p5 := ?_
    p6 := ?_ }⟩
  · have h := hmap 0
    rw [hdiag 0, hskew 1 0, hb01] at h
    simpa [T, ne_of_gt hm] using h
  · have h := hmap 1
    rw [hdiag 1, hb01] at h
    simpa [T] using h
  · have h := hmap 2
    rw [hb12, hb02] at h
    have hval : (-(2 * m)) / m = (-2 : ℝ) := by
      field_simp [ne_of_gt hm]
    rw [hval] at h
    simpa [T] using h
  · have h := hmap 3
    rw [hb13, hb03] at h
    have hval : -((3 / lambda) * m) / m = -3 / lambda := by
      field_simp [ne_of_gt hm, ne_of_gt hlambda]
      <;> ring
    rw [hval] at h
    simpa [T] using h
  · have h := hmap 4
    rw [hb14, hskew 0 4, hb40] at h
    have hval : -(-m) / m = (1 : ℝ) := by field_simp [ne_of_gt hm]
    rw [hval] at h
    simpa [T] using h
  · have h := hmap 5
    rw [hskew 1 5, hb51, hskew 0 5, hb50] at h
    have hval1 : -(-((3 / lambda) * m)) / m = 3 / lambda := by
      field_simp [ne_of_gt hm, ne_of_gt hlambda]
      <;> ring
    rw [hval1] at h
    simpa [T] using h
  · simpa [T] using
      h6TightPointNormalizer_center m (v 0) (v 1) (v 6) hm h01

/-- Canonical hull-six tight equality configurations are precisely members of
the public optimizer family up to arbitrary nonsingular affine equivalence.
The other alternating sign orientation is obtained by the finite equality
dispatcher before invoking this canonical theorem. -/
theorem hullSix_tight_equality_exists_family
    (v : Configuration7)
    (hccw : HullCCW v 6)
    (hin : ∀ p : Fin 7, 6 ≤ (p : ℕ) → InHullN v 6 p)
    (hm : 0 < minTri v)
    (hchamber : H6TightChamber (h6PointBracket v))
    (heq : fanArea v 6 = 9 * minTri v) :
    ∃ t : ℝ, 1 ≤ t ∧ t ≤ 4 / 3 ∧
      AffineEquivalent (sevenFamilyAt t) v := by
  let b : Fin 6 → Fin 6 → ℝ := h6PointBracket v
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
  have hradial : ∀ i j, i ≠ j → minTri v ≤ |b i j| := by
    intro i j hij
    exact minTri_le_of_distinct v i.castSucc j.castSucc 6
      ((Fin.castSucc_injective 6).ne hij) (hcast6 i) (hcast6 j)
  have hhull : ∀ i j k : Fin 6, i < j → j < k →
      minTri v ≤ b i j + b j k - b i k := by
    intro i j k hij hjk
    have hpos : 0 < sig (v i.castSucc) (v j.castSucc) (v k.castSucc) :=
      hccw i.castSucc j.castSucc k.castSucc
        (by simpa using hij) (by simpa using hjk) (by simpa using k.isLt)
    have hfloor := minTri_le_of_distinct v
      i.castSucc j.castSucc k.castSucc
      ((Fin.castSucc_injective 6).ne (ne_of_lt hij))
      ((Fin.castSucc_injective 6).ne (ne_of_lt (lt_trans hij hjk)))
      ((Fin.castSucc_injective 6).ne (ne_of_lt hjk))
    rw [abs_of_pos hpos] at hfloor
    have hid :
        b i j + b j k - b i k =
          sig (v i.castSucc) (v j.castSucc) (v k.castSucc) := by
      simp only [b, h6PointBracket, sig]
      ring
    rwa [hid]
  have hp6 := hin 6 (by norm_num)
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
        fanArea v 6 := by
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
  have heq' :
      b 0 1 + b 1 2 + b 2 3 + b 3 4 + b 4 5 + b 5 0 =
        9 * minTri v := by rw [hsum, heq]
  obtain ⟨lambda, hlower, hupper, hp⟩ :=
    h6_tight_chamber_equality_normal_form
      (minTri v) b hm hskew hgp hradial hhull hedge
        (by simpa only [b] using hchamber) heq'
  have hp' : H6TightPacket (minTri v) lambda
      (fun i => h6PointBracket v i (i + 1))
      (fun i => h6PointBracket v i (i + 2))
      (fun i => h6PointBracket v i (i + 3)) := by
    simpa only [b] using hp
  obtain ⟨T, hnormal⟩ := h6_tight_packet_point_normal_form
    v (minTri v) lambda hm hlower hupper hp'
  let w : Configuration7 := fun i => T.map (v i)
  have hnormal' : Hull6TightNormalForm w (minTri v) lambda := by
    simpa only [w] using hnormal
  obtain ⟨t, ht1, ht4, hfamily_w⟩ :=
    hnormal'.exists_family_affineEquivalent
  have hvw : GaugeEquivalent v w := by
    refine ⟨Equiv.refl _, T, ?_⟩
    rfl
  have hwv : AffineEquivalent w v :=
    affineEquivalent_symm (affineEquivalent_of_gaugeEquivalent hvw)
  exact ⟨t, ht1, ht4, affineEquivalent_trans hfamily_w hwv⟩

end HeilbronnChallenge.N7Upper
