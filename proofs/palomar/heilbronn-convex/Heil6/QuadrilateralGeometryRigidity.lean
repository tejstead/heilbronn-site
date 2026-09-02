import HullBridge
import Heil6.FiniteHullCases
import Heil6.QuadrilateralScalar

set_option linter.style.header false

/-!
# Equality rigidity for the four-vertex hull packet

`Heil6.hull4_bound` proves the non-strict counting estimate.  This file
separates the equality issue from that estimate.  The opposite-diagonal case
is reduced all the way to `QuadrilateralScalar.opposite_centroids_impossible`.

The same-half argument below extracts the barycentric data consumed by
`QuadrilateralScalar.same_side_barycentric_impossible`: choose either interior
point as a fan centre, locate the other in one of the three fan sectors, and
use equality in the counting bound to force all five small triangles to have
area `m`.
-/

namespace N6Scratch
namespace QuadrilateralGeometryRigidity

open FiniteHullCases

abbrev Point := ℝ × ℝ

/-- The ten triangle floors on five named points.  The cyclic orientations in
the first seven fields agree with a positively oriented containing triangle;
the absolute values make this structure insensitive to the order used by the
global floor. -/
structure FivePointTriangleFloor
    (A B C P Q : Point) (m : ℝ) : Prop where
  hABC : m ≤ |HullBridge.sig A B C|
  hABP : m ≤ |HullBridge.sig A B P|
  hBCP : m ≤ |HullBridge.sig B C P|
  hCAP : m ≤ |HullBridge.sig C A P|
  hABQ : m ≤ |HullBridge.sig A B Q|
  hBCQ : m ≤ |HullBridge.sig B C Q|
  hCAQ : m ≤ |HullBridge.sig C A Q|
  hAPQ : m ≤ |HullBridge.sig A P Q|
  hBPQ : m ≤ |HullBridge.sig B P Q|
  hCPQ : m ≤ |HullBridge.sig C P Q|

/-- Exactly the scalar equality data expected by
`same_side_barycentric_impossible`.  This is an existential proposition so
its real-valued witnesses never have to be eliminated from `Prop` into
computational data. -/
def SameSideBarycentricData (m : ℝ) : Prop :=
  ∃ t pA pB pC qA qB qC CPQ : ℝ,
    t = 5 * m ∧
    pA + pB + pC = t ∧
    qA + qB + qC = t ∧
    pC = m ∧
    qA = m ∧
    qB = m ∧
    t * m = pB * qC - pC * qB ∧
    t * m = pA * qC - pC * qA ∧
    t * CPQ = pA * qB - pB * qA ∧
    m ≤ |CPQ|

theorem SameSideBarycentricData.impossible {m : ℝ}
    (D : SameSideBarycentricData m) (hm : 0 < m) : False := by
  rcases D with
    ⟨t, pA, pB, pC, qA, qB, qC, CPQ, ht, hpSum, hqSum, hpC,
      hqA, hqB, hAPQ, hBPQ, hCPQ, hCPQFloor⟩
  exact QuadrilateralScalar.same_side_barycentric_impossible
    m t pA pB pC qA qB qC CPQ hm ht hpSum hqSum hpC hqA hqB
    hAPQ hBPQ hCPQ hCPQFloor

/-- Equality-extraction interface.

Mathematically, choose one interior point, split `ABC` into its three fan
triangles, and locate the second point in one fan triangle.  Equality at
`5*m` forces the two untouched fan triangles and the three refined triangles
to have area `m`.  A cyclic permutation then produces
`SameSideBarycentricData`.
-/
def SameHalfEqualityExtractor : Prop :=
  ∀ (A B C P Q : Point) (m : ℝ),
    0 < m →
    0 < HullBridge.sig A B C →
    HullBridge.InTri P A B C →
    HullBridge.InTri Q A B C →
    HullBridge.sig A B C = 5 * m →
    FivePointTriangleFloor A B C P Q m →
    SameSideBarycentricData m

private theorem signed_floor (m x : ℝ) (hx : 0 ≤ x)
    (hfloor : m ≤ |x|) : m ≤ x := by
  rw [abs_of_nonneg hx] at hfloor
  exact hfloor

private theorem three_mul_le_of_inTri
    (A B C P : Point) (m : ℝ)
    (hABC : 0 < HullBridge.sig A B C)
    (hP : HullBridge.InTri P A B C)
    (hABP : m ≤ |HullBridge.sig A B P|)
    (hBCP : m ≤ |HullBridge.sig B C P|)
    (hCAP : m ≤ |HullBridge.sig C A P|) :
    3 * m ≤ HullBridge.sig A B C := by
  have hmem :=
    (HullBridge.inTri_iff_mem_convexHull P A B C).mp hP
  obtain ⟨hnABP, hnBCP, hnCAP⟩ :=
    (HullBridge.mem_triangle_iff_orientations P A B C hABC).mp hmem
  have hfABP := signed_floor m (HullBridge.sig A B P) hnABP hABP
  have hfBCP := signed_floor m (HullBridge.sig B C P) hnBCP hBCP
  have hfCAP := signed_floor m (HullBridge.sig C A P) hnCAP hCAP
  have hsum :
      HullBridge.sig A B P + HullBridge.sig B C P + HullBridge.sig C A P =
        HullBridge.sig A B C := by
    simp only [HullBridge.sig]
    ring
  linarith

private theorem eq_centroid_of_three_mul
    (A B C P : Point) (m : ℝ)
    (hABC : 0 < HullBridge.sig A B C)
    (hP : HullBridge.InTri P A B C)
    (hABCeq : HullBridge.sig A B C = 3 * m)
    (hABP : m ≤ |HullBridge.sig A B P|)
    (hBCP : m ≤ |HullBridge.sig B C P|)
    (hCAP : m ≤ |HullBridge.sig C A P|) :
    P = QuadrilateralScalar.centroid A B C := by
  have hmem :=
    (HullBridge.inTri_iff_mem_convexHull P A B C).mp hP
  obtain ⟨hnABP, hnBCP, hnCAP⟩ :=
    (HullBridge.mem_triangle_iff_orientations P A B C hABC).mp hmem
  have hfABP := signed_floor m (HullBridge.sig A B P) hnABP hABP
  have hfBCP := signed_floor m (HullBridge.sig B C P) hnBCP hBCP
  have hfCAP := signed_floor m (HullBridge.sig C A P) hnCAP hCAP
  have hsum :
      HullBridge.sig A B P + HullBridge.sig B C P + HullBridge.sig C A P =
        HullBridge.sig A B C := by
    simp only [HullBridge.sig]
    ring
  have eABP : HullBridge.sig A B P = m := by linarith
  have eCAP : HullBridge.sig C A P = m := by linarith
  have cAB :
      3 * HullBridge.sig A B (QuadrilateralScalar.centroid A B C) =
        HullBridge.sig A B C := by
    simp only [HullBridge.sig, QuadrilateralScalar.centroid]
    ring
  have cAC :
      3 * HullBridge.sig A (QuadrilateralScalar.centroid A B C) C =
        HullBridge.sig A B C := by
    simp only [HullBridge.sig, QuadrilateralScalar.centroid]
    ring
  apply HullBridge.point_unique_of_sigs A B C P
    (QuadrilateralScalar.centroid A B C) (ne_of_gt hABC)
  · nlinarith
  · have eAPC : HullBridge.sig A P C = m := by
      rw [← HullBridge.sig_rotate C A P]
      exact eCAP
    nlinarith

private theorem inTri_rotate (P A B C : Point)
    (h : HullBridge.InTri P A B C) : HullBridge.InTri P B C A := by
  rcases h with ⟨x, y, z, hx, hy, hz, hsum, hP⟩
  refine ⟨y, z, x, hy, hz, hx, by linarith, ?_⟩
  rw [hP]
  module

private theorem FivePointTriangleFloor.rotate
    {A B C P Q : Point} {m : ℝ}
    (F : FivePointTriangleFloor A B C P Q m) :
    FivePointTriangleFloor B C A P Q m := {
  hABC := by
    rw [← HullBridge.sig_rotate A B C]
    exact F.hABC
  hABP := F.hBCP
  hBCP := F.hCAP
  hCAP := F.hABP
  hABQ := F.hBCQ
  hBCQ := F.hCAQ
  hCAQ := F.hABQ
  hAPQ := F.hBPQ
  hBPQ := F.hCPQ
  hCPQ := F.hAPQ
}

/-- A point of `ABC` lies in one of the three triangles of the fan based at
another strictly interior point.  Positivity of the five-point floors rules
out all boundary cases. -/
private theorem inTri_fan_partition
    (A B C P Q : Point) (m : ℝ)
    (hm : 0 < m)
    (hABC : 0 < HullBridge.sig A B C)
    (hP : HullBridge.InTri P A B C)
    (hQ : HullBridge.InTri Q A B C)
    (F : FivePointTriangleFloor A B C P Q m) :
    HullBridge.InTri Q P A B ∨
      HullBridge.InTri Q P B C ∨ HullBridge.InTri Q P C A := by
  have hPmem := (HullBridge.inTri_iff_mem_convexHull P A B C).mp hP
  obtain ⟨hnABP, hnBCP, hnCAP⟩ :=
    (HullBridge.mem_triangle_iff_orientations P A B C hABC).mp hPmem
  have hfABP := signed_floor m (HullBridge.sig A B P) hnABP F.hABP
  have hfBCP := signed_floor m (HullBridge.sig B C P) hnBCP F.hBCP
  have hfCAP := signed_floor m (HullBridge.sig C A P) hnCAP F.hCAP
  have hPAB : 0 < HullBridge.sig P A B := by
    rw [HullBridge.sig_rotate P A B]
    linarith
  have hPBC : 0 < HullBridge.sig P B C := by
    rw [HullBridge.sig_rotate P B C]
    linarith
  have hPCA : 0 < HullBridge.sig P C A := by
    rw [HullBridge.sig_rotate P C A]
    linarith
  have hQmem := (HullBridge.inTri_iff_mem_convexHull Q A B C).mp hQ
  obtain ⟨hnABQ, hnBCQ, hnCAQ⟩ :=
    (HullBridge.mem_triangle_iff_orientations Q A B C hABC).mp hQmem
  rcases hP with ⟨px, py, pz, hpx, hpy, hpz, hpsum, hPeq⟩
  have px_coeff : HullBridge.sig B C P = px * HullBridge.sig A B C := by
    calc
      HullBridge.sig B C P = HullBridge.sig B C
          (px • A + py • B + pz • C) := by rw [← hPeq]
      _ = px * HullBridge.sig A B C := by
        rw [HullBridge.sig_affine_third B C A B C px py pz hpsum]
        simp only [HullBridge.sig]
        ring
  have py_coeff : HullBridge.sig C A P = py * HullBridge.sig A B C := by
    calc
      HullBridge.sig C A P = HullBridge.sig C A
          (px • A + py • B + pz • C) := by rw [← hPeq]
      _ = py * HullBridge.sig A B C := by
        rw [HullBridge.sig_affine_third C A A B C px py pz hpsum]
        simp only [HullBridge.sig]
        ring
  have pz_coeff : HullBridge.sig A B P = pz * HullBridge.sig A B C := by
    calc
      HullBridge.sig A B P = HullBridge.sig A B
          (px • A + py • B + pz • C) := by rw [← hPeq]
      _ = pz * HullBridge.sig A B C := by
        rw [HullBridge.sig_affine_third A B A B C px py pz hpsum]
        simp only [HullBridge.sig]
        ring
  have hpx' : 0 < px := by nlinarith
  have hpy' : 0 < py := by nlinarith
  have hpz' : 0 < pz := by nlinarith
  let sA := HullBridge.sig P A Q
  let sB := HullBridge.sig P B Q
  let sC := HullBridge.sig P C Q
  have hsA : sA ≠ 0 := by
    intro hs
    have hf := F.hAPQ
    have he : HullBridge.sig A P Q = -sA := by
      dsimp only [sA]
      simp only [HullBridge.sig]
      ring
    rw [he, hs, neg_zero, abs_zero] at hf
    linarith
  have hsB : sB ≠ 0 := by
    intro hs
    have hf := F.hBPQ
    have he : HullBridge.sig B P Q = -sB := by
      dsimp only [sB]
      simp only [HullBridge.sig]
      ring
    rw [he, hs, neg_zero, abs_zero] at hf
    linarith
  have hsC : sC ≠ 0 := by
    intro hs
    have hf := F.hCPQ
    have he : HullBridge.sig C P Q = -sC := by
      dsimp only [sC]
      simp only [HullBridge.sig]
      ring
    rw [he, hs, neg_zero, abs_zero] at hf
    linarith
  have hweighted : px * sA + py * sB + pz * sC = 0 := by
    calc
      px * sA + py * sB + pz * sC =
          px * HullBridge.sig A Q P + py * HullBridge.sig B Q P +
            pz * HullBridge.sig C Q P := by
        dsimp only [sA, sB, sC]
        rw [HullBridge.sig_rotate P A Q, HullBridge.sig_rotate P B Q,
          HullBridge.sig_rotate P C Q]
      _ = HullBridge.sig (px • A + py • B + pz • C) Q P := by
        rw [HullBridge.sig_affine_fst A B C Q P px py pz hpsum]
      _ = 0 := by
        rw [← hPeq]
        simp only [HullBridge.sig]
        ring
  have inPAB (ha : 0 < sA) (hb : sB < 0) : HullBridge.InTri Q P A B := by
    apply HullBridge.inTri_of_sig Q P A B hPAB
    · rw [HullBridge.sig_rotate Q A B]
      exact hnABQ
    · rw [HullBridge.sig_swap P Q B]
      linarith
    · exact ha.le
  have inPBC (hb : 0 < sB) (hc : sC < 0) : HullBridge.InTri Q P B C := by
    apply HullBridge.inTri_of_sig Q P B C hPBC
    · rw [HullBridge.sig_rotate Q B C]
      exact hnBCQ
    · rw [HullBridge.sig_swap P Q C]
      linarith
    · exact hb.le
  have inPCA (hc : 0 < sC) (ha : sA < 0) : HullBridge.InTri Q P C A := by
    apply HullBridge.inTri_of_sig Q P C A hPCA
    · rw [HullBridge.sig_rotate Q C A]
      exact hnCAQ
    · rw [HullBridge.sig_swap P Q A]
      linarith
    · exact hc.le
  rcases lt_or_gt_of_ne hsA with ha | ha
  · rcases lt_or_gt_of_ne hsC with hc | hc
    · have hb : 0 < sB := by
        rcases lt_or_gt_of_ne hsB with hb | hb
        · have h1 : px * sA < 0 := mul_neg_of_pos_of_neg hpx' ha
          have h2 : py * sB < 0 := mul_neg_of_pos_of_neg hpy' hb
          have h3 : pz * sC < 0 := mul_neg_of_pos_of_neg hpz' hc
          nlinarith
        · exact hb
      exact Or.inr (Or.inl (inPBC hb hc))
    · exact Or.inr (Or.inr (inPCA hc ha))
  · rcases lt_or_gt_of_ne hsB with hb | hb
    · exact Or.inl (inPAB ha hb)
    · have hc : sC < 0 := by
        rcases lt_or_gt_of_ne hsC with hc | hc
        · exact hc
        · have h1 := mul_pos hpx' ha
          have h2 := mul_pos hpy' hb
          have h3 := mul_pos hpz' hc
          nlinarith
      exact Or.inr (Or.inl (inPBC hb hc))

private theorem same_side_data_of_first_sector
    (A B C P Q : Point) (m : ℝ)
    (hm : 0 < m)
    (hABC : 0 < HullBridge.sig A B C)
    (hP : HullBridge.InTri P A B C)
    (hQ : HullBridge.InTri Q A B C)
    (hQsector : HullBridge.InTri Q P A B)
    (hABCeq : HullBridge.sig A B C = 5 * m)
    (F : FivePointTriangleFloor A B C P Q m) :
    SameSideBarycentricData m := by
  have hPmem := (HullBridge.inTri_iff_mem_convexHull P A B C).mp hP
  obtain ⟨hnABP, hnBCP, hnCAP⟩ :=
    (HullBridge.mem_triangle_iff_orientations P A B C hABC).mp hPmem
  have fABP := signed_floor m (HullBridge.sig A B P) hnABP F.hABP
  have fBCP := signed_floor m (HullBridge.sig B C P) hnBCP F.hBCP
  have fCAP := signed_floor m (HullBridge.sig C A P) hnCAP F.hCAP
  have hPAB : 0 < HullBridge.sig P A B := by
    rw [HullBridge.sig_rotate P A B]
    linarith
  have hQsectorMem :=
    (HullBridge.inTri_iff_mem_convexHull Q P A B).mp hQsector
  obtain ⟨hnPAQ, hnABQ, hnBPQ⟩ :=
    (HullBridge.mem_triangle_iff_orientations Q P A B hPAB).mp hQsectorMem
  have fPAQabs : m ≤ |HullBridge.sig P A Q| := by
    have he : HullBridge.sig A P Q = -HullBridge.sig P A Q := by
      simp only [HullBridge.sig]
      ring
    have hf := F.hAPQ
    rw [he, abs_neg] at hf
    exact hf
  have fPAQ := signed_floor m (HullBridge.sig P A Q) hnPAQ fPAQabs
  have fABQ := signed_floor m (HullBridge.sig A B Q) hnABQ F.hABQ
  have fBPQ := signed_floor m (HullBridge.sig B P Q) hnBPQ F.hBPQ
  have fanP :
      HullBridge.sig A B P + HullBridge.sig B C P + HullBridge.sig C A P =
        HullBridge.sig A B C := by
    simp only [HullBridge.sig]
    ring
  have fanQ :
      HullBridge.sig P A Q + HullBridge.sig A B Q + HullBridge.sig B P Q =
        HullBridge.sig A B P := by
    simp only [HullBridge.sig]
    ring
  have eABP : HullBridge.sig A B P = 3 * m := by linarith
  have eBCP : HullBridge.sig B C P = m := by linarith
  have eCAP : HullBridge.sig C A P = m := by linarith
  have ePAQ : HullBridge.sig P A Q = m := by linarith
  have eABQ : HullBridge.sig A B Q = m := by linarith
  have eBPQ : HullBridge.sig B P Q = m := by linarith
  refine ⟨HullBridge.sig A B C,
    HullBridge.sig Q B C, HullBridge.sig Q C A, HullBridge.sig Q A B,
    HullBridge.sig P B C, HullBridge.sig P C A, HullBridge.sig P A B,
    HullBridge.sig Q P C, hABCeq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [HullBridge.sig]
    ring
  · simp only [HullBridge.sig]
    ring
  · rw [HullBridge.sig_rotate Q A B]
    exact eABQ
  · rw [HullBridge.sig_rotate P B C]
    exact eBCP
  · rw [HullBridge.sig_rotate P C A]
    exact eCAP
  · have eAQP : HullBridge.sig A Q P = m := by
      rw [← HullBridge.sig_rotate P A Q]
      exact ePAQ
    rw [← eAQP]
    simp only [HullBridge.sig]
    ring
  · have eQBP : HullBridge.sig Q B P = m := by
      calc
        HullBridge.sig Q B P = HullBridge.sig B P Q :=
          HullBridge.sig_rotate Q B P
        _ = m := eBPQ
    rw [← eQBP]
    simp only [HullBridge.sig]
    ring
  · simp only [HullBridge.sig]
    ring
  · have he : HullBridge.sig Q P C = -HullBridge.sig C P Q := by
      simp only [HullBridge.sig]
      ring
    rw [he, abs_neg]
    exact F.hCPQ

/-- Equality extraction for two points in the same containing triangle. -/
theorem sameHalfEqualityExtractor : SameHalfEqualityExtractor := by
  intro A B C P Q m hm hABC hP hQ hABCeq F
  rcases inTri_fan_partition A B C P Q m hm hABC hP hQ F with h | h | h
  · exact same_side_data_of_first_sector A B C P Q m hm hABC hP hQ h
      hABCeq F
  · have hABC' : 0 < HullBridge.sig B C A := by
      rw [← HullBridge.sig_rotate A B C]
      exact hABC
    have hABCeq' : HullBridge.sig B C A = 5 * m := by
      rw [← HullBridge.sig_rotate A B C]
      exact hABCeq
    exact same_side_data_of_first_sector B C A P Q m hm hABC'
      (inTri_rotate P A B C hP) (inTri_rotate Q A B C hQ) h hABCeq' F.rotate
  · have hP' := inTri_rotate P B C A (inTri_rotate P A B C hP)
    have hQ' := inTri_rotate Q B C A (inTri_rotate Q A B C hQ)
    have F' := F.rotate.rotate
    have hABC' : 0 < HullBridge.sig C A B := by
      calc
        0 < HullBridge.sig A B C := hABC
        _ = HullBridge.sig B C A := HullBridge.sig_rotate A B C
        _ = HullBridge.sig C A B := HullBridge.sig_rotate B C A
    have hABCeq' : HullBridge.sig C A B = 5 * m := by
      calc
        HullBridge.sig C A B = HullBridge.sig A B C :=
          HullBridge.sig_rotate C A B
        _ = 5 * m := hABCeq
    exact same_side_data_of_first_sector C A B P Q m hm hABC' hP' hQ' h
      hABCeq' F'

private theorem opposite_halves_impossible
    (A B C D P Q : Point) (m : ℝ)
    (hm : 0 < m)
    (hABC : 0 < HullBridge.sig A B C)
    (hABD : 0 < HullBridge.sig A B D)
    (hACD : 0 < HullBridge.sig A C D)
    (hBCD : 0 < HullBridge.sig B C D)
    (hP : HullBridge.InTri P A B C)
    (hQ : HullBridge.InTri Q A C D)
    (harea : HullBridge.sig A B C + HullBridge.sig A C D = 6 * m)
    (FABC : FivePointTriangleFloor A B C P Q m)
    (FACD : FivePointTriangleFloor A C D P Q m) : False := by
  have hleft := three_mul_le_of_inTri A B C P m hABC hP
    FABC.hABP FABC.hBCP FABC.hCAP
  have hright := three_mul_le_of_inTri A C D Q m hACD hQ
    FACD.hABQ FACD.hBCQ FACD.hCAQ
  have eABC : HullBridge.sig A B C = 3 * m := by linarith
  have eACD : HullBridge.sig A C D = 3 * m := by linarith
  have eP := eq_centroid_of_three_mul A B C P m hABC hP eABC
    FABC.hABP FABC.hBCP FABC.hCAP
  have eQ := eq_centroid_of_three_mul A C D Q m hACD hQ eACD
    FACD.hABQ FACD.hBCQ FACD.hCAQ
  have hcocycle := HullBridge.cocycle A B C D
  have areaA :
      9 * HullBridge.sig A (QuadrilateralScalar.centroid A B C)
          (QuadrilateralScalar.centroid A C D) =
        HullBridge.sig A B C + HullBridge.sig A B D + HullBridge.sig A C D := by
    simp only [HullBridge.sig, QuadrilateralScalar.centroid]
    ring
  have areaC :
      9 * HullBridge.sig (QuadrilateralScalar.centroid A B C) C
          (QuadrilateralScalar.centroid A C D) =
        2 * HullBridge.sig A B C + 2 * HullBridge.sig A C D -
          HullBridge.sig A B D := by
    simp only [HullBridge.sig, QuadrilateralScalar.centroid]
    ring
  have hApos : 0 < HullBridge.sig A (QuadrilateralScalar.centroid A B C)
      (QuadrilateralScalar.centroid A C D) := by
    nlinarith
  have hCpos : 0 < HullBridge.sig (QuadrilateralScalar.centroid A B C) C
      (QuadrilateralScalar.centroid A C D) := by
    nlinarith
  have floorA := FABC.hAPQ
  rw [eP, eQ, abs_of_pos hApos] at floorA
  have floorC0 := FABC.hCPQ
  rw [eP, eQ] at floorC0
  have floorC :
      m ≤ |HullBridge.sig (QuadrilateralScalar.centroid A B C) C
        (QuadrilateralScalar.centroid A C D)| := by
    rw [HullBridge.sig_reverse, abs_neg]
    exact floorC0
  rw [abs_of_pos hCpos] at floorC
  have floorB := FABC.hBPQ
  rw [eP, eQ] at floorB
  exact QuadrilateralScalar.opposite_centroids_impossible A B C D m hm
    (by simpa only [QuadrilateralScalar.sig, HullBridge.sig] using eABC)
    (by simpa only [QuadrilateralScalar.sig, HullBridge.sig] using eACD)
    (by simpa only [QuadrilateralScalar.sig, HullBridge.sig] using floorA)
    (by simpa only [QuadrilateralScalar.sig, HullBridge.sig] using floorC)
    (by simpa only [QuadrilateralScalar.sig, HullBridge.sig] using floorB)

private theorem inTri_to_bridge (p A B C : Point)
    (h : FiniteHullCases.InTri p A B C) : HullBridge.InTri p A B C := by
  simpa only [FiniteHullCases.InTri, HullBridge.InTri] using h

/-- Packet-facing strictness theorem, conditional only on the precisely stated
same-half equality extractor.  The opposite-half branches are fully proved in
this module. -/
theorem hull4Packet_six_mul_impossible_of_sameHalfEqualityExtractor
    (extractSame : SameHalfEqualityExtractor)
    (w : Fin 6 → Point) (m : ℝ)
    (hm : 0 < m)
    (hmin : DistinctTriangleFloor w m)
    (packet : Hull4Packet w)
    (harea :
      PlanarDet.sig (w 0) (w 1) (w 2) +
        PlanarDet.sig (w 0) (w 2) (w 3) = 6 * m) : False := by
  have hmin' : ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k →
      m ≤ |HullBridge.sig (w i) (w j) (w k)| := by
    intro i j k hij hik hjk
    change m ≤ |PlanarDet.sig (w i) (w j) (w k)|
    exact hmin i j k hij hik hjk
  have harea' :
      HullBridge.sig (w 0) (w 1) (w 2) +
        HullBridge.sig (w 0) (w 2) (w 3) = 6 * m := by
    change PlanarDet.sig (w 0) (w 1) (w 2) +
      PlanarDet.sig (w 0) (w 2) (w 3) = 6 * m
    exact harea
  have F012 : FivePointTriangleFloor (w 0) (w 1) (w 2) (w 4) (w 5) m := {
    hABC := hmin' 0 1 2 (by decide) (by decide) (by decide)
    hABP := hmin' 0 1 4 (by decide) (by decide) (by decide)
    hBCP := hmin' 1 2 4 (by decide) (by decide) (by decide)
    hCAP := hmin' 2 0 4 (by decide) (by decide) (by decide)
    hABQ := hmin' 0 1 5 (by decide) (by decide) (by decide)
    hBCQ := hmin' 1 2 5 (by decide) (by decide) (by decide)
    hCAQ := hmin' 2 0 5 (by decide) (by decide) (by decide)
    hAPQ := hmin' 0 4 5 (by decide) (by decide) (by decide)
    hBPQ := hmin' 1 4 5 (by decide) (by decide) (by decide)
    hCPQ := hmin' 2 4 5 (by decide) (by decide) (by decide) }
  have F023 : FivePointTriangleFloor (w 0) (w 2) (w 3) (w 4) (w 5) m := {
    hABC := hmin' 0 2 3 (by decide) (by decide) (by decide)
    hABP := hmin' 0 2 4 (by decide) (by decide) (by decide)
    hBCP := hmin' 2 3 4 (by decide) (by decide) (by decide)
    hCAP := hmin' 3 0 4 (by decide) (by decide) (by decide)
    hABQ := hmin' 0 2 5 (by decide) (by decide) (by decide)
    hBCQ := hmin' 2 3 5 (by decide) (by decide) (by decide)
    hCAQ := hmin' 3 0 5 (by decide) (by decide) (by decide)
    hAPQ := hmin' 0 4 5 (by decide) (by decide) (by decide)
    hBPQ := hmin' 2 4 5 (by decide) (by decide) (by decide)
    hCPQ := hmin' 3 4 5 (by decide) (by decide) (by decide) }
  rcases packet.h4 with h4left | h4right <;>
    rcases packet.h5 with h5left | h5right
  · have hcount := HullBridge.interior_count_bound w m hm hmin'
        ({4, 5} : Finset (Fin 6)) 0 1 2
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) packet.h012 (by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact inTri_to_bridge _ _ _ _ h4left
          · exact inTri_to_bridge _ _ _ _ h5left)
    have hcard : ({4, 5} : Finset (Fin 6)).card = 2 := by decide
    rw [hcard] at hcount
    norm_num at hcount
    have hother := hmin' 0 2 3 (by decide) (by decide) (by decide)
    have h023' : 0 < HullBridge.sig (w 0) (w 2) (w 3) := by
      simpa only [HullBridge.sig, PlanarDet.sig] using packet.h023
    rw [abs_of_pos h023'] at hother
    have heq : HullBridge.sig (w 0) (w 1) (w 2) = 5 * m := by
      linarith only [harea', hcount, hother]
    exact (extractSame (w 0) (w 1) (w 2) (w 4) (w 5) m hm packet.h012
      (inTri_to_bridge _ _ _ _ h4left) (inTri_to_bridge _ _ _ _ h5left)
      heq F012).impossible hm
  · exact opposite_halves_impossible
      (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) m hm
      packet.h012 packet.h013 packet.h023 packet.h123
      (inTri_to_bridge _ _ _ _ h4left)
      (inTri_to_bridge _ _ _ _ h5right) harea' F012 F023
  · exact opposite_halves_impossible
      (w 0) (w 1) (w 2) (w 3) (w 5) (w 4) m hm
      packet.h012 packet.h013 packet.h023 packet.h123
      (inTri_to_bridge _ _ _ _ h5left)
      (inTri_to_bridge _ _ _ _ h4right) harea'
      {
        hABC := F012.hABC, hABP := F012.hABQ, hBCP := F012.hBCQ,
        hCAP := F012.hCAQ, hABQ := F012.hABP, hBCQ := F012.hBCP,
        hCAQ := F012.hCAP,
        hAPQ := by
          rw [HullBridge.sig_swap (w 0) (w 5) (w 4), abs_neg]
          exact F012.hAPQ
        hBPQ := by
          rw [HullBridge.sig_swap (w 1) (w 5) (w 4), abs_neg]
          exact F012.hBPQ
        hCPQ := by
          rw [HullBridge.sig_swap (w 2) (w 5) (w 4), abs_neg]
          exact F012.hCPQ
      }
      {
        hABC := F023.hABC, hABP := F023.hABQ, hBCP := F023.hBCQ,
        hCAP := F023.hCAQ, hABQ := F023.hABP, hBCQ := F023.hBCP,
        hCAQ := F023.hCAP,
        hAPQ := by
          rw [HullBridge.sig_swap (w 0) (w 5) (w 4), abs_neg]
          exact F023.hAPQ
        hBPQ := by
          rw [HullBridge.sig_swap (w 2) (w 5) (w 4), abs_neg]
          exact F023.hBPQ
        hCPQ := by
          rw [HullBridge.sig_swap (w 3) (w 5) (w 4), abs_neg]
          exact F023.hCPQ
      }
  · have hcount := HullBridge.interior_count_bound w m hm hmin'
        ({4, 5} : Finset (Fin 6)) 0 2 3
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) packet.h023 (by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact inTri_to_bridge _ _ _ _ h4right
          · exact inTri_to_bridge _ _ _ _ h5right)
    have hcard : ({4, 5} : Finset (Fin 6)).card = 2 := by decide
    rw [hcard] at hcount
    norm_num at hcount
    have hother := hmin' 0 1 2 (by decide) (by decide) (by decide)
    have h012' : 0 < HullBridge.sig (w 0) (w 1) (w 2) := by
      simpa only [HullBridge.sig, PlanarDet.sig] using packet.h012
    rw [abs_of_pos h012'] at hother
    have heq : HullBridge.sig (w 0) (w 2) (w 3) = 5 * m := by
      linarith only [harea', hcount, hother]
    exact (extractSame (w 0) (w 2) (w 3) (w 4) (w 5) m hm packet.h023
      (inTri_to_bridge _ _ _ _ h4right) (inTri_to_bridge _ _ _ _ h5right)
      heq F023).impossible hm

/-- Equality in the four-hull counting bound is impossible under the global
distinct-triangle floor. -/
theorem hull4Packet_six_mul_impossible
    (w : Fin 6 → Point) (m : ℝ)
    (hm : 0 < m)
    (hmin : DistinctTriangleFloor w m)
    (packet : Hull4Packet w)
    (harea :
      PlanarDet.sig (w 0) (w 1) (w 2) +
        PlanarDet.sig (w 0) (w 2) (w 3) = 6 * m) : False :=
  hull4Packet_six_mul_impossible_of_sameHalfEqualityExtractor
    sameHalfEqualityExtractor w m hm hmin packet harea

end QuadrilateralGeometryRigidity
end N6Scratch
