import Heilbronn8.WitnessCore

namespace Heilbronn8

lemma signed_sig_w_012_pos : 0 < sig (w 0) (w 1) (w 2) := by
  rw [sig_w_012]
  simpa using v8H2w_pos

lemma abs_sig_w_012_ge :
    v8 * H2w ≤ |sig (w 0) (w 1) (w 2)| := by
  rw [abs_of_pos signed_sig_w_012_pos]
  nlinarith [sig_w_012]

lemma signed_sig_w_013_pos : 0 < sig (w 0) (w 1) (w 3) := by
  rw [sig_w_013]
  simpa using v8H2w_pos

lemma abs_sig_w_013_ge :
    v8 * H2w ≤ |sig (w 0) (w 1) (w 3)| := by
  rw [abs_of_pos signed_sig_w_013_pos]
  nlinarith [sig_w_013]

lemma signed_sig_w_014_pos : 0 < sig (w 0) (w 1) (w 4) := by
  have hgap := gap_w_014
  have hpoly := gap_w_014_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_014_ge :
    v8 * H2w ≤ |sig (w 0) (w 1) (w 4)| := by
  rw [abs_of_pos signed_sig_w_014_pos]
  nlinarith [gap_w_014, gap_w_014_poly_pos]

lemma signed_sig_w_015_pos : 0 < sig (w 0) (w 1) (w 5) := by
  have hgap := gap_w_015
  have hpoly := gap_w_015_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_015_ge :
    v8 * H2w ≤ |sig (w 0) (w 1) (w 5)| := by
  rw [abs_of_pos signed_sig_w_015_pos]
  nlinarith [gap_w_015, gap_w_015_poly_pos]

lemma signed_sig_w_016_pos : 0 < sig (w 0) (w 1) (w 6) := by
  have hgap := gap_w_016
  have hpoly := gap_w_016_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_016_ge :
    v8 * H2w ≤ |sig (w 0) (w 1) (w 6)| := by
  rw [abs_of_pos signed_sig_w_016_pos]
  nlinarith [gap_w_016, gap_w_016_poly_pos]

lemma signed_sig_w_017_pos : 0 < sig (w 0) (w 1) (w 7) := by
  have hgap := gap_w_017
  have hpoly := gap_w_017_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_017_ge :
    v8 * H2w ≤ |sig (w 0) (w 1) (w 7)| := by
  rw [abs_of_pos signed_sig_w_017_pos]
  nlinarith [gap_w_017, gap_w_017_poly_pos]

lemma signed_sig_w_023_pos : 0 < -sig (w 0) (w 2) (w 3) := by
  have hgap := gap_w_023
  have hpoly := gap_w_023_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_023_ge :
    v8 * H2w ≤ |sig (w 0) (w 2) (w 3)| := by
  have hs : sig (w 0) (w 2) (w 3) < 0 := by
    nlinarith [signed_sig_w_023_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_023, gap_w_023_poly_pos]

lemma signed_sig_w_024_pos : 0 < -sig (w 0) (w 2) (w 4) := by
  rw [sig_w_024]
  simpa using v8H2w_pos

lemma abs_sig_w_024_ge :
    v8 * H2w ≤ |sig (w 0) (w 2) (w 4)| := by
  have hs : sig (w 0) (w 2) (w 4) < 0 := by
    nlinarith [signed_sig_w_024_pos]
  rw [abs_of_neg hs]
  nlinarith [sig_w_024]

lemma signed_sig_w_025_pos : 0 < -sig (w 0) (w 2) (w 5) := by
  have hgap := gap_w_025
  have hpoly := gap_w_025_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_025_ge :
    v8 * H2w ≤ |sig (w 0) (w 2) (w 5)| := by
  have hs : sig (w 0) (w 2) (w 5) < 0 := by
    nlinarith [signed_sig_w_025_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_025, gap_w_025_poly_pos]

lemma signed_sig_w_026_pos : 0 < -sig (w 0) (w 2) (w 6) := by
  have hgap := gap_w_026
  have hpoly := gap_w_026_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_026_ge :
    v8 * H2w ≤ |sig (w 0) (w 2) (w 6)| := by
  have hs : sig (w 0) (w 2) (w 6) < 0 := by
    nlinarith [signed_sig_w_026_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_026, gap_w_026_poly_pos]

lemma signed_sig_w_027_pos : 0 < -sig (w 0) (w 2) (w 7) := by
  have hgap := gap_w_027
  have hpoly := gap_w_027_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_027_ge :
    v8 * H2w ≤ |sig (w 0) (w 2) (w 7)| := by
  have hs : sig (w 0) (w 2) (w 7) < 0 := by
    nlinarith [signed_sig_w_027_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_027, gap_w_027_poly_pos]

lemma signed_sig_w_034_pos : 0 < sig (w 0) (w 3) (w 4) := by
  have hgap := gap_w_034
  have hpoly := gap_w_034_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_034_ge :
    v8 * H2w ≤ |sig (w 0) (w 3) (w 4)| := by
  rw [abs_of_pos signed_sig_w_034_pos]
  nlinarith [gap_w_034, gap_w_034_poly_pos]

lemma signed_sig_w_035_pos : 0 < sig (w 0) (w 3) (w 5) := by
  have hgap := gap_w_035
  have hpoly := gap_w_035_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_035_ge :
    v8 * H2w ≤ |sig (w 0) (w 3) (w 5)| := by
  rw [abs_of_pos signed_sig_w_035_pos]
  nlinarith [gap_w_035, gap_w_035_poly_pos]

lemma signed_sig_w_036_pos : 0 < sig (w 0) (w 3) (w 6) := by
  have hgap := gap_w_036
  have hpoly := gap_w_036_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_036_ge :
    v8 * H2w ≤ |sig (w 0) (w 3) (w 6)| := by
  rw [abs_of_pos signed_sig_w_036_pos]
  nlinarith [gap_w_036, gap_w_036_poly_pos]

lemma signed_sig_w_037_pos : 0 < sig (w 0) (w 3) (w 7) := by
  have hgap := gap_w_037
  have hpoly := gap_w_037_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_037_ge :
    v8 * H2w ≤ |sig (w 0) (w 3) (w 7)| := by
  rw [abs_of_pos signed_sig_w_037_pos]
  nlinarith [gap_w_037, gap_w_037_poly_pos]

lemma signed_sig_w_045_pos : 0 < -sig (w 0) (w 4) (w 5) := by
  have hgap := gap_w_045
  have hpoly := gap_w_045_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_045_ge :
    v8 * H2w ≤ |sig (w 0) (w 4) (w 5)| := by
  have hs : sig (w 0) (w 4) (w 5) < 0 := by
    nlinarith [signed_sig_w_045_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_045, gap_w_045_poly_pos]

lemma signed_sig_w_046_pos : 0 < -sig (w 0) (w 4) (w 6) := by
  have hgap := gap_w_046
  have hpoly := gap_w_046_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_046_ge :
    v8 * H2w ≤ |sig (w 0) (w 4) (w 6)| := by
  have hs : sig (w 0) (w 4) (w 6) < 0 := by
    nlinarith [signed_sig_w_046_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_046, gap_w_046_poly_pos]

lemma signed_sig_w_047_pos : 0 < -sig (w 0) (w 4) (w 7) := by
  have hgap := gap_w_047
  have hpoly := gap_w_047_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_047_ge :
    v8 * H2w ≤ |sig (w 0) (w 4) (w 7)| := by
  have hs : sig (w 0) (w 4) (w 7) < 0 := by
    nlinarith [signed_sig_w_047_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_047, gap_w_047_poly_pos]

lemma signed_sig_w_056_pos : 0 < -sig (w 0) (w 5) (w 6) := by
  have hgap := gap_w_056
  have hpoly := gap_w_056_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_056_ge :
    v8 * H2w ≤ |sig (w 0) (w 5) (w 6)| := by
  have hs : sig (w 0) (w 5) (w 6) < 0 := by
    nlinarith [signed_sig_w_056_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_056, gap_w_056_poly_pos]

lemma signed_sig_w_057_pos : 0 < sig (w 0) (w 5) (w 7) := by
  have hgap := gap_w_057
  have hpoly := gap_w_057_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_057_ge :
    v8 * H2w ≤ |sig (w 0) (w 5) (w 7)| := by
  rw [abs_of_pos signed_sig_w_057_pos]
  nlinarith [gap_w_057, gap_w_057_poly_pos]

lemma signed_sig_w_067_pos : 0 < sig (w 0) (w 6) (w 7) := by
  have hgap := gap_w_067
  have hpoly := gap_w_067_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_067_ge :
    v8 * H2w ≤ |sig (w 0) (w 6) (w 7)| := by
  rw [abs_of_pos signed_sig_w_067_pos]
  nlinarith [gap_w_067, gap_w_067_poly_pos]

lemma signed_sig_w_123_pos : 0 < -sig (w 1) (w 2) (w 3) := by
  have hgap := gap_w_123
  have hpoly := gap_w_123_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_123_ge :
    v8 * H2w ≤ |sig (w 1) (w 2) (w 3)| := by
  have hs : sig (w 1) (w 2) (w 3) < 0 := by
    nlinarith [signed_sig_w_123_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_123, gap_w_123_poly_pos]

lemma signed_sig_w_124_pos : 0 < -sig (w 1) (w 2) (w 4) := by
  have hgap := gap_w_124
  have hpoly := gap_w_124_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_124_ge :
    v8 * H2w ≤ |sig (w 1) (w 2) (w 4)| := by
  have hs : sig (w 1) (w 2) (w 4) < 0 := by
    nlinarith [signed_sig_w_124_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_124, gap_w_124_poly_pos]

lemma signed_sig_w_125_pos : 0 < -sig (w 1) (w 2) (w 5) := by
  have hgap := gap_w_125
  have hpoly := gap_w_125_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_125_ge :
    v8 * H2w ≤ |sig (w 1) (w 2) (w 5)| := by
  have hs : sig (w 1) (w 2) (w 5) < 0 := by
    nlinarith [signed_sig_w_125_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_125, gap_w_125_poly_pos]

lemma signed_sig_w_126_pos : 0 < -sig (w 1) (w 2) (w 6) := by
  have hgap := gap_w_126
  have hpoly := gap_w_126_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_126_ge :
    v8 * H2w ≤ |sig (w 1) (w 2) (w 6)| := by
  have hs : sig (w 1) (w 2) (w 6) < 0 := by
    nlinarith [signed_sig_w_126_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_126, gap_w_126_poly_pos]

lemma signed_sig_w_127_pos : 0 < -sig (w 1) (w 2) (w 7) := by
  have hgap := gap_w_127
  have hpoly := gap_w_127_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_127_ge :
    v8 * H2w ≤ |sig (w 1) (w 2) (w 7)| := by
  have hs : sig (w 1) (w 2) (w 7) < 0 := by
    nlinarith [signed_sig_w_127_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_127, gap_w_127_poly_pos]

lemma signed_sig_w_134_pos : 0 < sig (w 1) (w 3) (w 4) := by
  have hgap := gap_w_134
  have hpoly := gap_w_134_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_134_ge :
    v8 * H2w ≤ |sig (w 1) (w 3) (w 4)| := by
  rw [abs_of_pos signed_sig_w_134_pos]
  nlinarith [gap_w_134, gap_w_134_poly_pos]

lemma signed_sig_w_135_pos : 0 < sig (w 1) (w 3) (w 5) := by
  have hgap := gap_w_135
  have hpoly := gap_w_135_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_135_ge :
    v8 * H2w ≤ |sig (w 1) (w 3) (w 5)| := by
  rw [abs_of_pos signed_sig_w_135_pos]
  nlinarith [gap_w_135, gap_w_135_poly_pos]

lemma signed_sig_w_136_pos : 0 < sig (w 1) (w 3) (w 6) := by
  rw [sig_w_136]
  simpa using v8H2w_pos

lemma abs_sig_w_136_ge :
    v8 * H2w ≤ |sig (w 1) (w 3) (w 6)| := by
  rw [abs_of_pos signed_sig_w_136_pos]
  nlinarith [sig_w_136]

lemma signed_sig_w_137_pos : 0 < sig (w 1) (w 3) (w 7) := by
  have hgap := gap_w_137
  have hpoly := gap_w_137_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_137_ge :
    v8 * H2w ≤ |sig (w 1) (w 3) (w 7)| := by
  rw [abs_of_pos signed_sig_w_137_pos]
  nlinarith [gap_w_137, gap_w_137_poly_pos]

lemma signed_sig_w_145_pos : 0 < -sig (w 1) (w 4) (w 5) := by
  have hgap := gap_w_145
  have hpoly := gap_w_145_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_145_ge :
    v8 * H2w ≤ |sig (w 1) (w 4) (w 5)| := by
  have hs : sig (w 1) (w 4) (w 5) < 0 := by
    nlinarith [signed_sig_w_145_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_145, gap_w_145_poly_pos]

lemma signed_sig_w_146_pos : 0 < -sig (w 1) (w 4) (w 6) := by
  have hgap := gap_w_146
  have hpoly := gap_w_146_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_146_ge :
    v8 * H2w ≤ |sig (w 1) (w 4) (w 6)| := by
  have hs : sig (w 1) (w 4) (w 6) < 0 := by
    nlinarith [signed_sig_w_146_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_146, gap_w_146_poly_pos]

lemma signed_sig_w_147_pos : 0 < -sig (w 1) (w 4) (w 7) := by
  have hgap := gap_w_147
  have hpoly := gap_w_147_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_147_ge :
    v8 * H2w ≤ |sig (w 1) (w 4) (w 7)| := by
  have hs : sig (w 1) (w 4) (w 7) < 0 := by
    nlinarith [signed_sig_w_147_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_147, gap_w_147_poly_pos]

lemma signed_sig_w_156_pos : 0 < -sig (w 1) (w 5) (w 6) := by
  have hgap := gap_w_156
  have hpoly := gap_w_156_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_156_ge :
    v8 * H2w ≤ |sig (w 1) (w 5) (w 6)| := by
  have hs : sig (w 1) (w 5) (w 6) < 0 := by
    nlinarith [signed_sig_w_156_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_156, gap_w_156_poly_pos]

lemma signed_sig_w_157_pos : 0 < sig (w 1) (w 5) (w 7) := by
  rw [sig_w_157]
  simpa using v8H2w_pos

lemma abs_sig_w_157_ge :
    v8 * H2w ≤ |sig (w 1) (w 5) (w 7)| := by
  rw [abs_of_pos signed_sig_w_157_pos]
  nlinarith [sig_w_157]

lemma signed_sig_w_167_pos : 0 < sig (w 1) (w 6) (w 7) := by
  have hgap := gap_w_167
  have hpoly := gap_w_167_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_167_ge :
    v8 * H2w ≤ |sig (w 1) (w 6) (w 7)| := by
  rw [abs_of_pos signed_sig_w_167_pos]
  nlinarith [gap_w_167, gap_w_167_poly_pos]

lemma signed_sig_w_234_pos : 0 < sig (w 2) (w 3) (w 4) := by
  have hgap := gap_w_234
  have hpoly := gap_w_234_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_234_ge :
    v8 * H2w ≤ |sig (w 2) (w 3) (w 4)| := by
  rw [abs_of_pos signed_sig_w_234_pos]
  nlinarith [gap_w_234, gap_w_234_poly_pos]

lemma signed_sig_w_235_pos : 0 < sig (w 2) (w 3) (w 5) := by
  have hgap := gap_w_235
  have hpoly := gap_w_235_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_235_ge :
    v8 * H2w ≤ |sig (w 2) (w 3) (w 5)| := by
  rw [abs_of_pos signed_sig_w_235_pos]
  nlinarith [gap_w_235, gap_w_235_poly_pos]

lemma signed_sig_w_236_pos : 0 < sig (w 2) (w 3) (w 6) := by
  have hgap := gap_w_236
  have hpoly := gap_w_236_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_236_ge :
    v8 * H2w ≤ |sig (w 2) (w 3) (w 6)| := by
  rw [abs_of_pos signed_sig_w_236_pos]
  nlinarith [gap_w_236, gap_w_236_poly_pos]

lemma signed_sig_w_237_pos : 0 < sig (w 2) (w 3) (w 7) := by
  have hgap := gap_w_237
  have hpoly := gap_w_237_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_237_ge :
    v8 * H2w ≤ |sig (w 2) (w 3) (w 7)| := by
  rw [abs_of_pos signed_sig_w_237_pos]
  nlinarith [gap_w_237, gap_w_237_poly_pos]

lemma signed_sig_w_245_pos : 0 < -sig (w 2) (w 4) (w 5) := by
  have hgap := gap_w_245
  have hpoly := gap_w_245_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_245_ge :
    v8 * H2w ≤ |sig (w 2) (w 4) (w 5)| := by
  have hs : sig (w 2) (w 4) (w 5) < 0 := by
    nlinarith [signed_sig_w_245_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_245, gap_w_245_poly_pos]

lemma signed_sig_w_246_pos : 0 < -sig (w 2) (w 4) (w 6) := by
  have hgap := gap_w_246
  have hpoly := gap_w_246_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_246_ge :
    v8 * H2w ≤ |sig (w 2) (w 4) (w 6)| := by
  have hs : sig (w 2) (w 4) (w 6) < 0 := by
    nlinarith [signed_sig_w_246_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_246, gap_w_246_poly_pos]

lemma signed_sig_w_247_pos : 0 < -sig (w 2) (w 4) (w 7) := by
  rw [sig_w_247]
  simpa using v8H2w_pos

lemma abs_sig_w_247_ge :
    v8 * H2w ≤ |sig (w 2) (w 4) (w 7)| := by
  have hs : sig (w 2) (w 4) (w 7) < 0 := by
    nlinarith [signed_sig_w_247_pos]
  rw [abs_of_neg hs]
  nlinarith [sig_w_247]

lemma signed_sig_w_256_pos : 0 < -sig (w 2) (w 5) (w 6) := by
  rw [sig_w_256]
  simpa using v8H2w_pos

lemma abs_sig_w_256_ge :
    v8 * H2w ≤ |sig (w 2) (w 5) (w 6)| := by
  have hs : sig (w 2) (w 5) (w 6) < 0 := by
    nlinarith [signed_sig_w_256_pos]
  rw [abs_of_neg hs]
  nlinarith [sig_w_256]

lemma signed_sig_w_257_pos : 0 < sig (w 2) (w 5) (w 7) := by
  have hgap := gap_w_257
  have hpoly := gap_w_257_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_257_ge :
    v8 * H2w ≤ |sig (w 2) (w 5) (w 7)| := by
  rw [abs_of_pos signed_sig_w_257_pos]
  nlinarith [gap_w_257, gap_w_257_poly_pos]

lemma signed_sig_w_267_pos : 0 < sig (w 2) (w 6) (w 7) := by
  have hgap := gap_w_267
  have hpoly := gap_w_267_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_267_ge :
    v8 * H2w ≤ |sig (w 2) (w 6) (w 7)| := by
  rw [abs_of_pos signed_sig_w_267_pos]
  nlinarith [gap_w_267, gap_w_267_poly_pos]

lemma signed_sig_w_345_pos : 0 < sig (w 3) (w 4) (w 5) := by
  rw [sig_w_345]
  simpa using v8H2w_pos

lemma abs_sig_w_345_ge :
    v8 * H2w ≤ |sig (w 3) (w 4) (w 5)| := by
  rw [abs_of_pos signed_sig_w_345_pos]
  nlinarith [sig_w_345]

lemma signed_sig_w_346_pos : 0 < -sig (w 3) (w 4) (w 6) := by
  have hgap := gap_w_346
  have hpoly := gap_w_346_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_346_ge :
    v8 * H2w ≤ |sig (w 3) (w 4) (w 6)| := by
  have hs : sig (w 3) (w 4) (w 6) < 0 := by
    nlinarith [signed_sig_w_346_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_346, gap_w_346_poly_pos]

lemma signed_sig_w_347_pos : 0 < -sig (w 3) (w 4) (w 7) := by
  have hgap := gap_w_347
  have hpoly := gap_w_347_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_347_ge :
    v8 * H2w ≤ |sig (w 3) (w 4) (w 7)| := by
  have hs : sig (w 3) (w 4) (w 7) < 0 := by
    nlinarith [signed_sig_w_347_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_347, gap_w_347_poly_pos]

lemma signed_sig_w_356_pos : 0 < -sig (w 3) (w 5) (w 6) := by
  rw [sig_w_356]
  simpa using v8H2w_pos

lemma abs_sig_w_356_ge :
    v8 * H2w ≤ |sig (w 3) (w 5) (w 6)| := by
  have hs : sig (w 3) (w 5) (w 6) < 0 := by
    nlinarith [signed_sig_w_356_pos]
  rw [abs_of_neg hs]
  nlinarith [sig_w_356]

lemma signed_sig_w_357_pos : 0 < -sig (w 3) (w 5) (w 7) := by
  have hgap := gap_w_357
  have hpoly := gap_w_357_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_357_ge :
    v8 * H2w ≤ |sig (w 3) (w 5) (w 7)| := by
  have hs : sig (w 3) (w 5) (w 7) < 0 := by
    nlinarith [signed_sig_w_357_pos]
  rw [abs_of_neg hs]
  nlinarith [gap_w_357, gap_w_357_poly_pos]

lemma signed_sig_w_367_pos : 0 < sig (w 3) (w 6) (w 7) := by
  have hgap := gap_w_367
  have hpoly := gap_w_367_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_367_ge :
    v8 * H2w ≤ |sig (w 3) (w 6) (w 7)| := by
  rw [abs_of_pos signed_sig_w_367_pos]
  nlinarith [gap_w_367, gap_w_367_poly_pos]

lemma signed_sig_w_456_pos : 0 < sig (w 4) (w 5) (w 6) := by
  have hgap := gap_w_456
  have hpoly := gap_w_456_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_456_ge :
    v8 * H2w ≤ |sig (w 4) (w 5) (w 6)| := by
  rw [abs_of_pos signed_sig_w_456_pos]
  nlinarith [gap_w_456, gap_w_456_poly_pos]

lemma signed_sig_w_457_pos : 0 < sig (w 4) (w 5) (w 7) := by
  rw [sig_w_457]
  simpa using v8H2w_pos

lemma abs_sig_w_457_ge :
    v8 * H2w ≤ |sig (w 4) (w 5) (w 7)| := by
  rw [abs_of_pos signed_sig_w_457_pos]
  nlinarith [sig_w_457]

lemma signed_sig_w_467_pos : 0 < sig (w 4) (w 6) (w 7) := by
  have hgap := gap_w_467
  have hpoly := gap_w_467_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_467_ge :
    v8 * H2w ≤ |sig (w 4) (w 6) (w 7)| := by
  rw [abs_of_pos signed_sig_w_467_pos]
  nlinarith [gap_w_467, gap_w_467_poly_pos]

lemma signed_sig_w_567_pos : 0 < sig (w 5) (w 6) (w 7) := by
  have hgap := gap_w_567
  have hpoly := gap_w_567_poly_pos
  nlinarith [v8H2w_pos]

lemma abs_sig_w_567_ge :
    v8 * H2w ≤ |sig (w 5) (w 6) (w 7)| := by
  rw [abs_of_pos signed_sig_w_567_pos]
  nlinarith [gap_w_567, gap_w_567_poly_pos]


end Heilbronn8
