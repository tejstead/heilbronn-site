import Heilbronn8.WitnessMinimum

namespace Heilbronn8

lemma hull_sig_w_012_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 1))
      (w (hullCycle 2)) := by
  change 0 < sig (w 7) (w 4) (w 2)
  have horient :
      sig (w 7) (w 4) (w 2) =
        -sig (w 2) (w 4) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_247_pos

lemma hull_sig_w_013_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 1))
      (w (hullCycle 3)) := by
  change 0 < sig (w 7) (w 4) (w 0)
  have horient :
      sig (w 7) (w 4) (w 0) =
        -sig (w 0) (w 4) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_047_pos

lemma hull_sig_w_014_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 1))
      (w (hullCycle 4)) := by
  change 0 < sig (w 7) (w 4) (w 1)
  have horient :
      sig (w 7) (w 4) (w 1) =
        -sig (w 1) (w 4) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_147_pos

lemma hull_sig_w_015_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 1))
      (w (hullCycle 5)) := by
  change 0 < sig (w 7) (w 4) (w 3)
  have horient :
      sig (w 7) (w 4) (w 3) =
        -sig (w 3) (w 4) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_347_pos

lemma hull_sig_w_016_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 1))
      (w (hullCycle 6)) := by
  change 0 < sig (w 7) (w 4) (w 6)
  have horient :
      sig (w 7) (w 4) (w 6) =
        sig (w 4) (w 6) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_467_pos

lemma hull_sig_w_023_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 2))
      (w (hullCycle 3)) := by
  change 0 < sig (w 7) (w 2) (w 0)
  have horient :
      sig (w 7) (w 2) (w 0) =
        -sig (w 0) (w 2) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_027_pos

lemma hull_sig_w_024_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 2))
      (w (hullCycle 4)) := by
  change 0 < sig (w 7) (w 2) (w 1)
  have horient :
      sig (w 7) (w 2) (w 1) =
        -sig (w 1) (w 2) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_127_pos

lemma hull_sig_w_025_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 2))
      (w (hullCycle 5)) := by
  change 0 < sig (w 7) (w 2) (w 3)
  have horient :
      sig (w 7) (w 2) (w 3) =
        sig (w 2) (w 3) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_237_pos

lemma hull_sig_w_026_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 2))
      (w (hullCycle 6)) := by
  change 0 < sig (w 7) (w 2) (w 6)
  have horient :
      sig (w 7) (w 2) (w 6) =
        sig (w 2) (w 6) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_267_pos

lemma hull_sig_w_034_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 3))
      (w (hullCycle 4)) := by
  change 0 < sig (w 7) (w 0) (w 1)
  have horient :
      sig (w 7) (w 0) (w 1) =
        sig (w 0) (w 1) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_017_pos

lemma hull_sig_w_035_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 3))
      (w (hullCycle 5)) := by
  change 0 < sig (w 7) (w 0) (w 3)
  have horient :
      sig (w 7) (w 0) (w 3) =
        sig (w 0) (w 3) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_037_pos

lemma hull_sig_w_036_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 3))
      (w (hullCycle 6)) := by
  change 0 < sig (w 7) (w 0) (w 6)
  have horient :
      sig (w 7) (w 0) (w 6) =
        sig (w 0) (w 6) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_067_pos

lemma hull_sig_w_045_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 4))
      (w (hullCycle 5)) := by
  change 0 < sig (w 7) (w 1) (w 3)
  have horient :
      sig (w 7) (w 1) (w 3) =
        sig (w 1) (w 3) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_137_pos

lemma hull_sig_w_046_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 4))
      (w (hullCycle 6)) := by
  change 0 < sig (w 7) (w 1) (w 6)
  have horient :
      sig (w 7) (w 1) (w 6) =
        sig (w 1) (w 6) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_167_pos

lemma hull_sig_w_056_pos :
    0 < sig (w (hullCycle 0)) (w (hullCycle 5))
      (w (hullCycle 6)) := by
  change 0 < sig (w 7) (w 3) (w 6)
  have horient :
      sig (w 7) (w 3) (w 6) =
        sig (w 3) (w 6) (w 7) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_367_pos

lemma hull_sig_w_123_pos :
    0 < sig (w (hullCycle 1)) (w (hullCycle 2))
      (w (hullCycle 3)) := by
  change 0 < sig (w 4) (w 2) (w 0)
  have horient :
      sig (w 4) (w 2) (w 0) =
        -sig (w 0) (w 2) (w 4) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_024_pos

lemma hull_sig_w_124_pos :
    0 < sig (w (hullCycle 1)) (w (hullCycle 2))
      (w (hullCycle 4)) := by
  change 0 < sig (w 4) (w 2) (w 1)
  have horient :
      sig (w 4) (w 2) (w 1) =
        -sig (w 1) (w 2) (w 4) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_124_pos

lemma hull_sig_w_125_pos :
    0 < sig (w (hullCycle 1)) (w (hullCycle 2))
      (w (hullCycle 5)) := by
  change 0 < sig (w 4) (w 2) (w 3)
  have horient :
      sig (w 4) (w 2) (w 3) =
        sig (w 2) (w 3) (w 4) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_234_pos

lemma hull_sig_w_126_pos :
    0 < sig (w (hullCycle 1)) (w (hullCycle 2))
      (w (hullCycle 6)) := by
  change 0 < sig (w 4) (w 2) (w 6)
  have horient :
      sig (w 4) (w 2) (w 6) =
        -sig (w 2) (w 4) (w 6) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_246_pos

lemma hull_sig_w_134_pos :
    0 < sig (w (hullCycle 1)) (w (hullCycle 3))
      (w (hullCycle 4)) := by
  change 0 < sig (w 4) (w 0) (w 1)
  have horient :
      sig (w 4) (w 0) (w 1) =
        sig (w 0) (w 1) (w 4) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_014_pos

lemma hull_sig_w_135_pos :
    0 < sig (w (hullCycle 1)) (w (hullCycle 3))
      (w (hullCycle 5)) := by
  change 0 < sig (w 4) (w 0) (w 3)
  have horient :
      sig (w 4) (w 0) (w 3) =
        sig (w 0) (w 3) (w 4) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_034_pos

lemma hull_sig_w_136_pos :
    0 < sig (w (hullCycle 1)) (w (hullCycle 3))
      (w (hullCycle 6)) := by
  change 0 < sig (w 4) (w 0) (w 6)
  have horient :
      sig (w 4) (w 0) (w 6) =
        -sig (w 0) (w 4) (w 6) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_046_pos

lemma hull_sig_w_145_pos :
    0 < sig (w (hullCycle 1)) (w (hullCycle 4))
      (w (hullCycle 5)) := by
  change 0 < sig (w 4) (w 1) (w 3)
  have horient :
      sig (w 4) (w 1) (w 3) =
        sig (w 1) (w 3) (w 4) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_134_pos

lemma hull_sig_w_146_pos :
    0 < sig (w (hullCycle 1)) (w (hullCycle 4))
      (w (hullCycle 6)) := by
  change 0 < sig (w 4) (w 1) (w 6)
  have horient :
      sig (w 4) (w 1) (w 6) =
        -sig (w 1) (w 4) (w 6) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_146_pos

lemma hull_sig_w_156_pos :
    0 < sig (w (hullCycle 1)) (w (hullCycle 5))
      (w (hullCycle 6)) := by
  change 0 < sig (w 4) (w 3) (w 6)
  have horient :
      sig (w 4) (w 3) (w 6) =
        -sig (w 3) (w 4) (w 6) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_346_pos

lemma hull_sig_w_234_pos :
    0 < sig (w (hullCycle 2)) (w (hullCycle 3))
      (w (hullCycle 4)) := by
  change 0 < sig (w 2) (w 0) (w 1)
  have horient :
      sig (w 2) (w 0) (w 1) =
        sig (w 0) (w 1) (w 2) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_012_pos

lemma hull_sig_w_235_pos :
    0 < sig (w (hullCycle 2)) (w (hullCycle 3))
      (w (hullCycle 5)) := by
  change 0 < sig (w 2) (w 0) (w 3)
  have horient :
      sig (w 2) (w 0) (w 3) =
        -sig (w 0) (w 2) (w 3) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_023_pos

lemma hull_sig_w_236_pos :
    0 < sig (w (hullCycle 2)) (w (hullCycle 3))
      (w (hullCycle 6)) := by
  change 0 < sig (w 2) (w 0) (w 6)
  have horient :
      sig (w 2) (w 0) (w 6) =
        -sig (w 0) (w 2) (w 6) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_026_pos

lemma hull_sig_w_245_pos :
    0 < sig (w (hullCycle 2)) (w (hullCycle 4))
      (w (hullCycle 5)) := by
  change 0 < sig (w 2) (w 1) (w 3)
  have horient :
      sig (w 2) (w 1) (w 3) =
        -sig (w 1) (w 2) (w 3) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_123_pos

lemma hull_sig_w_246_pos :
    0 < sig (w (hullCycle 2)) (w (hullCycle 4))
      (w (hullCycle 6)) := by
  change 0 < sig (w 2) (w 1) (w 6)
  have horient :
      sig (w 2) (w 1) (w 6) =
        -sig (w 1) (w 2) (w 6) := by
    simp only [sig]
    ring1
  exact horient.symm ▸ signed_sig_w_126_pos

lemma hull_sig_w_256_pos :
    0 < sig (w (hullCycle 2)) (w (hullCycle 5))
      (w (hullCycle 6)) := by
  change 0 < sig (w 2) (w 3) (w 6)
  exact signed_sig_w_236_pos

lemma hull_sig_w_345_pos :
    0 < sig (w (hullCycle 3)) (w (hullCycle 4))
      (w (hullCycle 5)) := by
  change 0 < sig (w 0) (w 1) (w 3)
  exact signed_sig_w_013_pos

lemma hull_sig_w_346_pos :
    0 < sig (w (hullCycle 3)) (w (hullCycle 4))
      (w (hullCycle 6)) := by
  change 0 < sig (w 0) (w 1) (w 6)
  exact signed_sig_w_016_pos

lemma hull_sig_w_356_pos :
    0 < sig (w (hullCycle 3)) (w (hullCycle 5))
      (w (hullCycle 6)) := by
  change 0 < sig (w 0) (w 3) (w 6)
  exact signed_sig_w_036_pos

lemma hull_sig_w_456_pos :
    0 < sig (w (hullCycle 4)) (w (hullCycle 5))
      (w (hullCycle 6)) := by
  change 0 < sig (w 1) (w 3) (w 6)
  exact signed_sig_w_136_pos

noncomputable def baryDen : ℝ :=
  ((-922 / 47) + (20636 / 47) * v8 + (-95124 / 47) * v8 ^ 2 + (91152 / 47) * v8 ^ 3 + (183340 / 47) * v8 ^ 4 : ℝ)

noncomputable def bary7Num : ℝ :=
  ((1202 / 47) + (-28736 / 47) * v8 + (240364 / 47) * v8 ^ 2 + (-843316 / 47) * v8 ^ 3 + (1097980 / 47) * v8 ^ 4 : ℝ)

noncomputable def bary2Num : ℝ :=
  ((-3520 / 47) + (78436 / 47) * v8 + (-534086 / 47) * v8 ^ 2 + (1517852 / 47) * v8 ^ 3 + (-1557360 / 47) * v8 ^ 4 : ℝ)

noncomputable def bary3Num : ℝ :=
  ((1396 / 47) + (-29064 / 47) * v8 + (198598 / 47) * v8 ^ 2 + (-583384 / 47) * v8 ^ 3 + (642720 / 47) * v8 ^ 4 : ℝ)

lemma baryDen_eq : sig (w 7) (w 2) (w 3) = baryDen := by
  simp [w, sig, baryDen, cw, dw, ew, fw, gw]
  linear_combination ((-4663738 / 2209) + (72311161 / 2209) * v8 + (-312027552 / 2209) * v8 ^ 2 + (392184860 / 2209) * v8 ^ 3 : ℝ) * vP

lemma bary7Num_eq : sig (w 5) (w 2) (w 3) = bary7Num := by
  simp [w, sig, bary7Num, cw, dw, ew, fw, gw]
  linear_combination ((-1063662 / 2209) + (18232359 / 2209) * v8 + (-84729738 / 2209) * v8 ^ 2 + (113663590 / 2209) * v8 ^ 3 : ℝ) * vP

lemma bary2Num_eq : sig (w 7) (w 5) (w 3) = bary2Num := by
  simp [w, sig, bary2Num, cw, dw, ew, fw, gw]
  linear_combination ((-2935236 / 2209) + (43407609 / 2209) * v8 + (-177962482 / 2209) * v8 ^ 2 + (210714310 / 2209) * v8 ^ 3 : ℝ) * vP

lemma bary3Num_eq : sig (w 7) (w 2) (w 5) = bary3Num := by
  simp [w, sig, bary3Num, cw, dw, ew, fw, gw]
  linear_combination ((-664840 / 2209) + (10671193 / 2209) * v8 + (-49335332 / 2209) * v8 ^ 2 + (67806960 / 2209) * v8 ^ 3 : ℝ) * vP

lemma baryDen_pos_raw : 0 < ((-922 / 47) + (20636 / 47) * v8 + (-95124 / 47) * v8 ^ 2 + (91152 / 47) * v8 ^ 3 + (183340 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4l]

lemma baryDen_pos : 0 < baryDen := by
  unfold baryDen
  exact baryDen_pos_raw

lemma bary7Num_pos_raw : 0 < ((1202 / 47) + (-28736 / 47) * v8 + (240364 / 47) * v8 ^ 2 + (-843316 / 47) * v8 ^ 3 + (1097980 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma bary7Num_pos : 0 < bary7Num := by
  unfold bary7Num
  exact bary7Num_pos_raw

lemma bary2Num_pos_raw : 0 < ((-3520 / 47) + (78436 / 47) * v8 + (-534086 / 47) * v8 ^ 2 + (1517852 / 47) * v8 ^ 3 + (-1557360 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1l, h2u, h3l, h4u]

lemma bary2Num_pos : 0 < bary2Num := by
  unfold bary2Num
  exact bary2Num_pos_raw

lemma bary3Num_pos_raw : 0 < ((1396 / 47) + (-29064 / 47) * v8 + (198598 / 47) * v8 ^ 2 + (-583384 / 47) * v8 ^ 3 + (642720 / 47) * v8 ^ 4 : ℝ) := by
  rcases v8_pow_bounds with
    ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
  linarith [h1u, h2l, h3u, h4l]

lemma bary3Num_pos : 0 < bary3Num := by
  unfold bary3Num
  exact bary3Num_pos_raw

lemma w5_inTri_723_cert :
    InTri (w 5) (w 7) (w 2) (w 3) := by
  refine
    ⟨bary7Num / baryDen, bary2Num / baryDen,
      bary3Num / baryDen, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg bary7Num_pos.le baryDen_pos.le
  · exact div_nonneg bary2Num_pos.le baryDen_pos.le
  · exact div_nonneg bary3Num_pos.le baryDen_pos.le
  · field_simp [ne_of_gt baryDen_pos]
    unfold bary7Num bary2Num bary3Num baryDen
    ring1
  · apply Prod.ext
    · simp [w]
      field_simp [ne_of_gt baryDen_pos]
      unfold bary7Num bary2Num bary3Num baryDen fw dw
      linear_combination -(((1724772 / 2209) + (-19905364 / 2209) * v8 + (49440080 / 2209) * v8 ^ 2 + (6427200 / 2209) * v8 ^ 3 : ℝ)) * vP
    · simp [w]
      field_simp [ne_of_gt baryDen_pos]
      unfold bary7Num bary2Num bary3Num baryDen gw cw ew
      linear_combination -(((3208084 / 2209) + (-55384026 / 2209) * v8 + (267164468 / 2209) * v8 ^ 2 + (-380402690 / 2209) * v8 ^ 3 : ℝ)) * vP


end Heilbronn8
