/-
Polynomial identities of doubled signed areas, together with reusable
affine-expansion and repeated-point identities.
-/
import Heilbronn8.Defs

namespace Heilbronn8

lemma sig_eq12 (p q : ℝ × ℝ) : sig p p q = 0 := by
  simp only [sig]
  ring

lemma sig_eq13 (p q : ℝ × ℝ) : sig p q p = 0 := by
  simp only [sig]
  ring

lemma sig_eq23 (p q : ℝ × ℝ) : sig p q q = 0 := by
  simp only [sig]
  ring

lemma sig_affine_thd (p q a b c : ℝ × ℝ) (x y z : ℝ)
    (hxyz : x + y + z = 1) :
    sig p q (x • a + y • b + z • c)
      = x * sig p q a + y * sig p q b + z * sig p q c := by
  have hz : z = 1 - x - y := by
    linarith
  subst hz
  simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, smul_eq_mul]
  ring

lemma sig_affine_fst4 (a b c d q r : ℝ × ℝ) (x y z t : ℝ)
    (h : x + y + z + t = 1) :
    sig (x • a + y • b + z • c + t • d) q r
      = x * sig a q r + y * sig b q r + z * sig c q r + t * sig d q r := by
  have ht : t = 1 - x - y - z := by
    linarith
  subst ht
  simp only [sig, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, smul_eq_mul]
  ring

/-- Grassmann-Pluecker three-term relation with pivot `a`. -/
lemma gp (a b c d e : ℝ × ℝ) :
    sig a b c * sig a d e - sig a b d * sig a c e
      + sig a b e * sig a c d = 0 := by
  simp only [sig]
  ring

/-- Cocycle identity for four points. -/
lemma cocycle (a b c d : ℝ × ℝ) :
    sig a b c - sig a b d + sig a c d - sig b c d = 0 := by
  simp only [sig]
  ring

/-- Fan split of a triangle by an arbitrary point. -/
lemma split3 (p a b c : ℝ × ℝ) :
    sig p a b + sig p b c + sig p c a = sig a b c := by
  simp only [sig]
  ring

/-- Fan split of a quadrilateral by an arbitrary point. -/
lemma split4 (p a b c d : ℝ × ℝ) :
    sig p a b + sig p b c + sig p c d + sig p d a
      = sig a b c + sig a c d := by
  simp only [sig]
  ring

/-- Ear domination under the seven indicated orientation hypotheses. -/
lemma mid_ge (a b c d e : ℝ × ℝ)
    (habc : 0 < sig a b c) (habd : 0 < sig a b d)
    (habe : 0 < sig a b e) (hacd : 0 < sig a c d)
    (hace : 0 < sig a c e) (hade : 0 < sig a d e)
    (hcde : 0 < sig c d e) :
    min (sig a b c) (sig a b e) ≤ sig a b d := by
  by_contra hlt
  push_neg at hlt
  have h1 : sig a b d < sig a b c :=
    lt_of_lt_of_le hlt (min_le_left _ _)
  have h2 : sig a b d < sig a b e :=
    lt_of_lt_of_le hlt (min_le_right _ _)
  have hgp := gp a b c d e
  have hcc := cocycle a c d e
  nlinarith [mul_pos habd hcde,
    mul_lt_mul_of_pos_right h1 hade,
    mul_lt_mul_of_pos_right h2 hacd]

end Heilbronn8
