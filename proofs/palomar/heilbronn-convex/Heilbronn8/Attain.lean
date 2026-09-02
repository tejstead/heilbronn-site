/-
Hand-written attainment glue for the generated n = 8 witness.
-/
import Heilbronn8.Witness

namespace Heilbronn8

set_option maxHeartbeats 800000 in
theorem minTri_w : minTri w = v8 * H2w := by
  apply le_antisymm
  · calc
      minTri w ≤ |sig (w 0) (w 1) (w 2)| :=
        minTri_le w (by decide) (by decide)
      _ = v8 * H2w := by
        rw [sig_w_012, abs_of_pos v8H2w_pos]
  · apply le_minTri
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals simp only [Fin.mk_lt_mk] at hij hjk
    all_goals try omega
    · show v8 * H2w ≤ |sig (w 0) (w 1) (w 2)|
      exact abs_sig_w_012_ge
    · show v8 * H2w ≤ |sig (w 0) (w 1) (w 3)|
      exact abs_sig_w_013_ge
    · show v8 * H2w ≤ |sig (w 0) (w 1) (w 4)|
      exact abs_sig_w_014_ge
    · show v8 * H2w ≤ |sig (w 0) (w 1) (w 5)|
      exact abs_sig_w_015_ge
    · show v8 * H2w ≤ |sig (w 0) (w 1) (w 6)|
      exact abs_sig_w_016_ge
    · show v8 * H2w ≤ |sig (w 0) (w 1) (w 7)|
      exact abs_sig_w_017_ge
    · show v8 * H2w ≤ |sig (w 0) (w 2) (w 3)|
      exact abs_sig_w_023_ge
    · show v8 * H2w ≤ |sig (w 0) (w 2) (w 4)|
      exact abs_sig_w_024_ge
    · show v8 * H2w ≤ |sig (w 0) (w 2) (w 5)|
      exact abs_sig_w_025_ge
    · show v8 * H2w ≤ |sig (w 0) (w 2) (w 6)|
      exact abs_sig_w_026_ge
    · show v8 * H2w ≤ |sig (w 0) (w 2) (w 7)|
      exact abs_sig_w_027_ge
    · show v8 * H2w ≤ |sig (w 0) (w 3) (w 4)|
      exact abs_sig_w_034_ge
    · show v8 * H2w ≤ |sig (w 0) (w 3) (w 5)|
      exact abs_sig_w_035_ge
    · show v8 * H2w ≤ |sig (w 0) (w 3) (w 6)|
      exact abs_sig_w_036_ge
    · show v8 * H2w ≤ |sig (w 0) (w 3) (w 7)|
      exact abs_sig_w_037_ge
    · show v8 * H2w ≤ |sig (w 0) (w 4) (w 5)|
      exact abs_sig_w_045_ge
    · show v8 * H2w ≤ |sig (w 0) (w 4) (w 6)|
      exact abs_sig_w_046_ge
    · show v8 * H2w ≤ |sig (w 0) (w 4) (w 7)|
      exact abs_sig_w_047_ge
    · show v8 * H2w ≤ |sig (w 0) (w 5) (w 6)|
      exact abs_sig_w_056_ge
    · show v8 * H2w ≤ |sig (w 0) (w 5) (w 7)|
      exact abs_sig_w_057_ge
    · show v8 * H2w ≤ |sig (w 0) (w 6) (w 7)|
      exact abs_sig_w_067_ge
    · show v8 * H2w ≤ |sig (w 1) (w 2) (w 3)|
      exact abs_sig_w_123_ge
    · show v8 * H2w ≤ |sig (w 1) (w 2) (w 4)|
      exact abs_sig_w_124_ge
    · show v8 * H2w ≤ |sig (w 1) (w 2) (w 5)|
      exact abs_sig_w_125_ge
    · show v8 * H2w ≤ |sig (w 1) (w 2) (w 6)|
      exact abs_sig_w_126_ge
    · show v8 * H2w ≤ |sig (w 1) (w 2) (w 7)|
      exact abs_sig_w_127_ge
    · show v8 * H2w ≤ |sig (w 1) (w 3) (w 4)|
      exact abs_sig_w_134_ge
    · show v8 * H2w ≤ |sig (w 1) (w 3) (w 5)|
      exact abs_sig_w_135_ge
    · show v8 * H2w ≤ |sig (w 1) (w 3) (w 6)|
      exact abs_sig_w_136_ge
    · show v8 * H2w ≤ |sig (w 1) (w 3) (w 7)|
      exact abs_sig_w_137_ge
    · show v8 * H2w ≤ |sig (w 1) (w 4) (w 5)|
      exact abs_sig_w_145_ge
    · show v8 * H2w ≤ |sig (w 1) (w 4) (w 6)|
      exact abs_sig_w_146_ge
    · show v8 * H2w ≤ |sig (w 1) (w 4) (w 7)|
      exact abs_sig_w_147_ge
    · show v8 * H2w ≤ |sig (w 1) (w 5) (w 6)|
      exact abs_sig_w_156_ge
    · show v8 * H2w ≤ |sig (w 1) (w 5) (w 7)|
      exact abs_sig_w_157_ge
    · show v8 * H2w ≤ |sig (w 1) (w 6) (w 7)|
      exact abs_sig_w_167_ge
    · show v8 * H2w ≤ |sig (w 2) (w 3) (w 4)|
      exact abs_sig_w_234_ge
    · show v8 * H2w ≤ |sig (w 2) (w 3) (w 5)|
      exact abs_sig_w_235_ge
    · show v8 * H2w ≤ |sig (w 2) (w 3) (w 6)|
      exact abs_sig_w_236_ge
    · show v8 * H2w ≤ |sig (w 2) (w 3) (w 7)|
      exact abs_sig_w_237_ge
    · show v8 * H2w ≤ |sig (w 2) (w 4) (w 5)|
      exact abs_sig_w_245_ge
    · show v8 * H2w ≤ |sig (w 2) (w 4) (w 6)|
      exact abs_sig_w_246_ge
    · show v8 * H2w ≤ |sig (w 2) (w 4) (w 7)|
      exact abs_sig_w_247_ge
    · show v8 * H2w ≤ |sig (w 2) (w 5) (w 6)|
      exact abs_sig_w_256_ge
    · show v8 * H2w ≤ |sig (w 2) (w 5) (w 7)|
      exact abs_sig_w_257_ge
    · show v8 * H2w ≤ |sig (w 2) (w 6) (w 7)|
      exact abs_sig_w_267_ge
    · show v8 * H2w ≤ |sig (w 3) (w 4) (w 5)|
      exact abs_sig_w_345_ge
    · show v8 * H2w ≤ |sig (w 3) (w 4) (w 6)|
      exact abs_sig_w_346_ge
    · show v8 * H2w ≤ |sig (w 3) (w 4) (w 7)|
      exact abs_sig_w_347_ge
    · show v8 * H2w ≤ |sig (w 3) (w 5) (w 6)|
      exact abs_sig_w_356_ge
    · show v8 * H2w ≤ |sig (w 3) (w 5) (w 7)|
      exact abs_sig_w_357_ge
    · show v8 * H2w ≤ |sig (w 3) (w 6) (w 7)|
      exact abs_sig_w_367_ge
    · show v8 * H2w ≤ |sig (w 4) (w 5) (w 6)|
      exact abs_sig_w_456_ge
    · show v8 * H2w ≤ |sig (w 4) (w 5) (w 7)|
      exact abs_sig_w_457_ge
    · show v8 * H2w ≤ |sig (w 4) (w 6) (w 7)|
      exact abs_sig_w_467_ge
    · show v8 * H2w ≤ |sig (w 5) (w 6) (w 7)|
      exact abs_sig_w_567_ge

set_option maxHeartbeats 500000 in
theorem w_hullCyclePos : HullCyclePos w := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals simp only [Fin.mk_lt_mk] at hij hjk
  all_goals try omega
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 1))
      (w (hullCycle 2))
    exact hull_sig_w_012_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 1))
      (w (hullCycle 3))
    exact hull_sig_w_013_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 1))
      (w (hullCycle 4))
    exact hull_sig_w_014_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 1))
      (w (hullCycle 5))
    exact hull_sig_w_015_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 1))
      (w (hullCycle 6))
    exact hull_sig_w_016_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 2))
      (w (hullCycle 3))
    exact hull_sig_w_023_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 2))
      (w (hullCycle 4))
    exact hull_sig_w_024_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 2))
      (w (hullCycle 5))
    exact hull_sig_w_025_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 2))
      (w (hullCycle 6))
    exact hull_sig_w_026_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 3))
      (w (hullCycle 4))
    exact hull_sig_w_034_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 3))
      (w (hullCycle 5))
    exact hull_sig_w_035_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 3))
      (w (hullCycle 6))
    exact hull_sig_w_036_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 4))
      (w (hullCycle 5))
    exact hull_sig_w_045_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 4))
      (w (hullCycle 6))
    exact hull_sig_w_046_pos.le
  · show 0 ≤ sig (w (hullCycle 0)) (w (hullCycle 5))
      (w (hullCycle 6))
    exact hull_sig_w_056_pos.le
  · show 0 ≤ sig (w (hullCycle 1)) (w (hullCycle 2))
      (w (hullCycle 3))
    exact hull_sig_w_123_pos.le
  · show 0 ≤ sig (w (hullCycle 1)) (w (hullCycle 2))
      (w (hullCycle 4))
    exact hull_sig_w_124_pos.le
  · show 0 ≤ sig (w (hullCycle 1)) (w (hullCycle 2))
      (w (hullCycle 5))
    exact hull_sig_w_125_pos.le
  · show 0 ≤ sig (w (hullCycle 1)) (w (hullCycle 2))
      (w (hullCycle 6))
    exact hull_sig_w_126_pos.le
  · show 0 ≤ sig (w (hullCycle 1)) (w (hullCycle 3))
      (w (hullCycle 4))
    exact hull_sig_w_134_pos.le
  · show 0 ≤ sig (w (hullCycle 1)) (w (hullCycle 3))
      (w (hullCycle 5))
    exact hull_sig_w_135_pos.le
  · show 0 ≤ sig (w (hullCycle 1)) (w (hullCycle 3))
      (w (hullCycle 6))
    exact hull_sig_w_136_pos.le
  · show 0 ≤ sig (w (hullCycle 1)) (w (hullCycle 4))
      (w (hullCycle 5))
    exact hull_sig_w_145_pos.le
  · show 0 ≤ sig (w (hullCycle 1)) (w (hullCycle 4))
      (w (hullCycle 6))
    exact hull_sig_w_146_pos.le
  · show 0 ≤ sig (w (hullCycle 1)) (w (hullCycle 5))
      (w (hullCycle 6))
    exact hull_sig_w_156_pos.le
  · show 0 ≤ sig (w (hullCycle 2)) (w (hullCycle 3))
      (w (hullCycle 4))
    exact hull_sig_w_234_pos.le
  · show 0 ≤ sig (w (hullCycle 2)) (w (hullCycle 3))
      (w (hullCycle 5))
    exact hull_sig_w_235_pos.le
  · show 0 ≤ sig (w (hullCycle 2)) (w (hullCycle 3))
      (w (hullCycle 6))
    exact hull_sig_w_236_pos.le
  · show 0 ≤ sig (w (hullCycle 2)) (w (hullCycle 4))
      (w (hullCycle 5))
    exact hull_sig_w_245_pos.le
  · show 0 ≤ sig (w (hullCycle 2)) (w (hullCycle 4))
      (w (hullCycle 6))
    exact hull_sig_w_246_pos.le
  · show 0 ≤ sig (w (hullCycle 2)) (w (hullCycle 5))
      (w (hullCycle 6))
    exact hull_sig_w_256_pos.le
  · show 0 ≤ sig (w (hullCycle 3)) (w (hullCycle 4))
      (w (hullCycle 5))
    exact hull_sig_w_345_pos.le
  · show 0 ≤ sig (w (hullCycle 3)) (w (hullCycle 4))
      (w (hullCycle 6))
    exact hull_sig_w_346_pos.le
  · show 0 ≤ sig (w (hullCycle 3)) (w (hullCycle 5))
      (w (hullCycle 6))
    exact hull_sig_w_356_pos.le
  · show 0 ≤ sig (w (hullCycle 4)) (w (hullCycle 5))
      (w (hullCycle 6))
    exact hull_sig_w_456_pos.le

theorem w_interior :
    InTri (w 5) (w 7) (w 2) (w 3) :=
  w5_inTri_723_cert

theorem witness_attains :
    minTri w = v8 * H2w ∧
    HullCyclePos w ∧
    InTri (w 5) (w 7) (w 2) (w 3) ∧
    0 < H2w :=
  ⟨minTri_w, w_hullCyclePos, w_interior, H2w_pos⟩

end Heilbronn8
