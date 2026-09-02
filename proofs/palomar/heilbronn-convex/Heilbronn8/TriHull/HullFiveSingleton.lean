import Heilbronn8.TriHull.Main
import Heilbronn8.TriHull.HullFiveSingletonAlgebra

/-!
# Geometry identities for the hull-five singleton sectors

Fix the quadrilateral `A-B-X-C` and a selected point `R` in its central
diagonal sector.  Write

* `A₀ = sig R A B`, `Z = sig R B C`, `D = sig R C A`,
* `G = sig R X C`, `N = sig R A X`,
* `T = sig A B C`, `E = sig B X C`,
* `U = sig A B X`, `V = sig A X C`.

The lemmas below are universal polynomial identities: they do not assume an
orientation or an incidence relation.  Positivity, minimum-area floors, and
fan membership are deliberately left to the thin topology layer which calls
the scalar adapters in `HullFiveSingletonAlgebra`.
-/

namespace Heilbronn8.TriHull

/-- The two triangulations of a quadrilateral have the same signed sum. -/
lemma hullFive_singleton_quadrilateral_sum (A B X C : Point) :
    sig A B C + sig B X C = sig A B X + sig A X C := by
  simp only [sig]
  ring

/-- The Plücker identity consumed by `singleton_of_fan_rows`. -/
lemma hullFive_singleton_plucker (A B X C R : Point) :
    (sig A B C + sig B X C) * sig R C A =
      (sig R A B + sig R C A) * (sig R X C + sig R C A) -
        sig R B C * sig R A X := by
  simp only [sig]
  ring

/-- Fixed product row for a point in the outer `A` fan cell. -/
lemma hullFive_singleton_A_fixed_identity (A B X R P : Point) :
    sig R A B * sig A X P =
      sig P A B * sig R A X - sig R A P * sig A B X := by
  simp only [sig]
  ring

/-- Intrinsic sign row for a point in the outer `A` fan cell. -/
lemma hullFive_singleton_A_sign_identity (A B C R P : Point) :
    sig R A B * sig C P R =
      sig R P B * sig R C A - sig R A P * sig R B C := by
  simp only [sig]
  ring

/-- Strong product row for a point in the inner `Z` fan cell. -/
lemma hullFive_singleton_Z_strong_identity (A B X C R P : Point) :
    sig R B C * (-sig A X P) =
      sig R P C * sig A B X - sig P B C * sig R A X -
        sig R B P * sig A X C := by
  simp only [sig]
  ring

/-- Auxiliary inner-`Z` identity used to bound its variable coefficient. -/
lemma hullFive_singleton_Z_coefficient_identity (A B C R P : Point) :
    sig R B C * sig A P R =
      sig R P C * sig R A B - sig R B P * sig R C A := by
  simp only [sig]
  ring

/-- Fixed product row for a point in the outer `G` fan cell. -/
lemma hullFive_singleton_G_fixed_identity (B X C R Q : Point) :
    sig R X C * (-sig B C Q) =
      sig R Q C * sig B X C - sig Q X C * sig R B C := by
  simp only [sig]
  ring

/-- Intrinsic sign row for a point in the outer `G` fan cell. -/
lemma hullFive_singleton_G_sign_identity (A X C R Q : Point) :
    sig R X C * sig A Q R =
      sig R Q C * sig R A X - sig R X Q * sig R C A := by
  simp only [sig]
  ring

/-- Strong product row for a point in the inner `N` fan cell. -/
lemma hullFive_singleton_N_strong_identity (A B X C R Q : Point) :
    sig R A X * (-sig B C Q) =
      sig R A Q * sig B X C - sig Q A X * sig R B C -
        sig R Q X * sig A B C := by
  simp only [sig]
  ring

/-! ## Point-level fan-row packages -/

/-- Three selected subtriangle floors give the doubled one-point bound `6`.
This is the local, unnormalized form needed by the singleton argument. -/
lemma singleton_one_point_six
    {P A B C : Point}
    (hABC : 0 < sig A B C) (hP : InTriStrict P A B C)
    (hPBCmin : 2 ≤ |sig P B C|)
    (hPCAmin : 2 ≤ |sig P C A|)
    (hPABmin : 2 ≤ |sig P A B|) :
    6 ≤ sig A B C := by
  obtain ⟨hPBC, hPCA, hPAB⟩ := inTriStrict_fan_pos hABC hP
  rw [abs_of_pos hPBC] at hPBCmin
  rw [abs_of_pos hPCA] at hPCAmin
  rw [abs_of_pos hPAB] at hPABmin
  nlinarith [fan_sum P A B C]

/-- The complete outer-`A` package: its fixed row and both possible signs of
the intrinsic `CPR` determinant. -/
lemma hullFive_singleton_A_rows
    {A B X C R P : Point}
    (hRAB : 0 < sig R A B)
    (hRBC : 0 ≤ sig R B C) (hRCA : 0 ≤ sig R C A)
    (hRAX : 0 ≤ sig R A X) (hABX : 0 ≤ sig A B X)
    (hP : InTriStrict P R A B) (hAXP : sig A X P < 0)
    (hPABmin : 2 ≤ |sig P A B|)
    (hPBRmin : 2 ≤ |sig P B R|)
    (hPRAmin : 2 ≤ |sig P R A|)
    (hAXPmin : 2 ≤ |sig A X P|)
    (hCPRmin : 2 ≤ |sig C P R|) :
    6 ≤ sig R A B ∧
      2 * (sig R A X + 4) ≤ (sig R A B - 4) * (sig A B X - 2) ∧
      (2 * (sig R C A + 4) ≤
          (sig R A B - 4) * (sig R B C - 2) ∨
        2 * (sig R B C + 4) ≤
          (sig R A B - 4) * (sig R C A - 2)) := by
  obtain ⟨hPAB, hPBR, hPRA⟩ := inTriStrict_fan_pos hRAB hP
  rw [abs_of_pos hPAB] at hPABmin
  rw [abs_of_pos hPBR] at hPBRmin
  rw [abs_of_pos hPRA] at hPRAmin
  have hfan := fan_sum P R A B
  have hlarge : 6 ≤ sig R A B := by nlinarith
  have hPRAhi : sig P R A ≤ sig R A B - 4 := by nlinarith
  have hPBRhi : sig P B R ≤ sig R A B - 4 := by nlinarith
  have hnegAXP : 2 ≤ -sig A X P := by
    rwa [abs_of_neg hAXP] at hAXPmin
  have hfixedId :
      sig R A B * (-sig A X P) =
        sig P R A * sig A B X - sig P A B * sig R A X := by
    simp only [sig]
    ring
  have hfixed := singleton_fan_fixed_row
    hRAB.le hABX hRAX hPRAhi hPABmin hnegAXP hfixedId
  have hsignId :
      sig R A B * sig C P R =
        sig P B R * sig R C A - sig P R A * sig R B C := by
    simp only [sig]
    ring
  have hsign := singleton_fan_sign_rows
    hRAB.le hRBC hRCA hPRAmin hPBRmin hPRAhi hPBRhi hCPRmin hsignId
  exact ⟨hlarge, hfixed, hsign⟩

/-- The complete inner-`Z` package. -/
lemma hullFive_singleton_Z_rows
    {A B X C R P : Point}
    (hRBC : 0 < sig R B C)
    (hRAX : 0 ≤ sig R A X) (hABX : 0 ≤ sig A B X)
    (hAXC : 0 ≤ sig A X C)
    (hP : InTriStrict P R B C) (hAXP : sig A X P < 0)
    (hPBCmin : 2 ≤ |sig P B C|)
    (hPCRmin : 2 ≤ |sig P C R|)
    (hPRBmin : 2 ≤ |sig P R B|)
    (hAXPmin : 2 ≤ |sig A X P|) :
    6 ≤ sig R B C ∧
      2 * (sig R A X + sig A X C + 4) ≤
        (sig R B C - 4) * (sig A B X - 2) := by
  obtain ⟨hPBC, hPCR, hPRB⟩ := inTriStrict_fan_pos hRBC hP
  rw [abs_of_pos hPBC] at hPBCmin
  rw [abs_of_pos hPCR] at hPCRmin
  rw [abs_of_pos hPRB] at hPRBmin
  have hfan := fan_sum P R B C
  have hlarge : 6 ≤ sig R B C := by nlinarith
  have hPCRhi : sig P C R ≤ sig R B C - 4 := by nlinarith
  have hnegAXP : 2 ≤ -sig A X P := by
    rwa [abs_of_neg hAXP] at hAXPmin
  have hid :
      sig R B C * (-sig A X P) =
        sig P C R * sig A B X - sig P B C * sig R A X -
          sig P R B * sig A X C := by
    simp only [sig]
    ring
  have hrow := singleton_fan_strong_row
    hRBC.le hABX hRAX hAXC hPRBmin hPBCmin hPCRhi hnegAXP hid
  exact ⟨hlarge, hrow⟩

/-- The complete outer-`G` package: its fixed row and both signs of `AQR`. -/
lemma hullFive_singleton_G_rows
    {A B X C R Q : Point}
    (hRXC : 0 < sig R X C)
    (hRBC : 0 ≤ sig R B C) (hRCA : 0 ≤ sig R C A)
    (hRAX : 0 ≤ sig R A X) (hBXC : 0 ≤ sig B X C)
    (hQ : InTriStrict Q R X C) (hBCQ : sig B C Q < 0)
    (hQXCmin : 2 ≤ |sig Q X C|)
    (hQCRmin : 2 ≤ |sig Q C R|)
    (hQRXmin : 2 ≤ |sig Q R X|)
    (hBCQmin : 2 ≤ |sig B C Q|)
    (hAQRmin : 2 ≤ |sig A Q R|) :
    6 ≤ sig R X C ∧
      2 * (sig R B C + 4) ≤ (sig R X C - 4) * (sig B X C - 2) ∧
      (2 * (sig R C A + 4) ≤
          (sig R X C - 4) * (sig R A X - 2) ∨
        2 * (sig R A X + 4) ≤
          (sig R X C - 4) * (sig R C A - 2)) := by
  obtain ⟨hQXC, hQCR, hQRX⟩ := inTriStrict_fan_pos hRXC hQ
  rw [abs_of_pos hQXC] at hQXCmin
  rw [abs_of_pos hQCR] at hQCRmin
  rw [abs_of_pos hQRX] at hQRXmin
  have hfan := fan_sum Q R X C
  have hlarge : 6 ≤ sig R X C := by nlinarith
  have hQCRhi : sig Q C R ≤ sig R X C - 4 := by nlinarith
  have hQRXhi : sig Q R X ≤ sig R X C - 4 := by nlinarith
  have hnegBCQ : 2 ≤ -sig B C Q := by
    rwa [abs_of_neg hBCQ] at hBCQmin
  have hfixedId :
      sig R X C * (-sig B C Q) =
        sig Q C R * sig B X C - sig Q X C * sig R B C := by
    simp only [sig]
    ring
  have hfixed := singleton_fan_fixed_row
    hRXC.le hBXC hRBC hQCRhi hQXCmin hnegBCQ hfixedId
  have hnegAQRmin : 2 ≤ |-sig A Q R| := by
    simpa only [abs_neg] using hAQRmin
  have hsignId :
      sig R X C * (-sig A Q R) =
        sig Q R X * sig R C A - sig Q C R * sig R A X := by
    simp only [sig]
    ring
  have hsign := singleton_fan_sign_rows
    hRXC.le hRAX hRCA hQCRmin hQRXmin hQCRhi hQRXhi
      hnegAQRmin hsignId
  exact ⟨hlarge, hfixed, hsign⟩

/-- The complete inner-`N` package. -/
lemma hullFive_singleton_N_rows
    {A B X C R Q : Point}
    (hRAX : 0 < sig R A X)
    (hRBC : 0 ≤ sig R B C) (hBXC : 0 ≤ sig B X C)
    (hABC : 0 ≤ sig A B C)
    (hQ : InTriStrict Q R A X) (hBCQ : sig B C Q < 0)
    (hQAXmin : 2 ≤ |sig Q A X|)
    (hQXRmin : 2 ≤ |sig Q X R|)
    (hQRAmin : 2 ≤ |sig Q R A|)
    (hBCQmin : 2 ≤ |sig B C Q|) :
    6 ≤ sig R A X ∧
      2 * (sig R B C + sig A B C + 4) ≤
        (sig R A X - 4) * (sig B X C - 2) := by
  obtain ⟨hQAX, hQXR, hQRA⟩ := inTriStrict_fan_pos hRAX hQ
  rw [abs_of_pos hQAX] at hQAXmin
  rw [abs_of_pos hQXR] at hQXRmin
  rw [abs_of_pos hQRA] at hQRAmin
  have hfan := fan_sum Q R A X
  have hlarge : 6 ≤ sig R A X := by nlinarith
  have hQRAhi : sig Q R A ≤ sig R A X - 4 := by nlinarith
  have hnegBCQ : 2 ≤ -sig B C Q := by
    rwa [abs_of_neg hBCQ] at hBCQmin
  have hid :
      sig R A X * (-sig B C Q) =
        sig Q R A * sig B X C - sig Q A X * sig R B C -
          sig Q X R * sig A B C := by
    simp only [sig]
    ring
  have hrow := singleton_fan_strong_row
    hRAX.le hBXC hRBC hABC hQXRmin hQAXmin hQRAhi hnegBCQ hid
  exact ⟨hlarge, hrow⟩

/-! ## Seven-point fan-cell theorem -/

set_option maxHeartbeats 1000000 in
/--
The complete singleton-sector estimate after the two strict fan partitions
have been performed.  Labels are `A,B,X,C,P,Q,R = 0,1,2,3,4,5,6`.

The point `P` lies in `ABX`, the point `Q` lies in `BXC`, and `R` lies in
both `ABC` and `AXC`.  The final two hypotheses are precisely the two
surviving outcomes of partitioning about `R`; the common `RCA` outcome has
already been excluded by diagonal-sector separation.
-/
theorem hullFive_singleton_fan_cells_210
    (v : Fin 7 → Point)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v 0) (v 1) (v 3))
    (hBXC : 0 < sig (v 1) (v 2) (v 3))
    (hABX : 0 < sig (v 0) (v 1) (v 2))
    (hAXC : 0 < sig (v 0) (v 2) (v 3))
    (hRABC : InTriStrict (v 6) (v 0) (v 1) (v 3))
    (hRAXC : InTriStrict (v 6) (v 0) (v 2) (v 3))
    (hPABX : InTriStrict (v 4) (v 0) (v 1) (v 2))
    (hQBXC : InTriStrict (v 5) (v 1) (v 2) (v 3))
    (hPfan :
      InTriStrict (v 4) (v 6) (v 0) (v 1) ∨
        InTriStrict (v 4) (v 6) (v 1) (v 3))
    (hQfan :
      InTriStrict (v 5) (v 6) (v 2) (v 3) ∨
        InTriStrict (v 5) (v 6) (v 0) (v 2)) :
    23 ≤ sig (v 0) (v 1) (v 3) + sig (v 1) (v 2) (v 3) := by
  obtain ⟨hZpos, hDpos, hApos⟩ := inTriStrict_fan_pos hABC hRABC
  obtain ⟨hGpos, _hDpos', hNpos⟩ := inTriStrict_fan_pos hAXC hRAXC

  have hAmin := hmin (i := 6) (j := 0) (k := 1)
    (by decide) (by decide) (by decide)
  have hZmin := hmin (i := 6) (j := 1) (k := 3)
    (by decide) (by decide) (by decide)
  have hDmin := hmin (i := 6) (j := 3) (k := 0)
    (by decide) (by decide) (by decide)
  have hGmin := hmin (i := 6) (j := 2) (k := 3)
    (by decide) (by decide) (by decide)
  have hNmin := hmin (i := 6) (j := 0) (k := 2)
    (by decide) (by decide) (by decide)
  rw [abs_of_pos hApos] at hAmin
  rw [abs_of_pos hZpos] at hZmin
  rw [abs_of_pos hDpos] at hDmin
  rw [abs_of_pos hGpos] at hGmin
  rw [abs_of_pos hNpos] at hNmin

  have hPABmin := hmin (i := 4) (j := 0) (k := 1)
    (by decide) (by decide) (by decide)
  have hPBRmin := hmin (i := 4) (j := 1) (k := 6)
    (by decide) (by decide) (by decide)
  have hPRAmin := hmin (i := 4) (j := 6) (k := 0)
    (by decide) (by decide) (by decide)
  have hPBCmin := hmin (i := 4) (j := 1) (k := 3)
    (by decide) (by decide) (by decide)
  have hPCRmin := hmin (i := 4) (j := 3) (k := 6)
    (by decide) (by decide) (by decide)
  have hPRBmin := hmin (i := 4) (j := 6) (k := 1)
    (by decide) (by decide) (by decide)
  have hAXPmin := hmin (i := 0) (j := 2) (k := 4)
    (by decide) (by decide) (by decide)
  have hCPRmin := hmin (i := 3) (j := 4) (k := 6)
    (by decide) (by decide) (by decide)

  have hQXCmin := hmin (i := 5) (j := 2) (k := 3)
    (by decide) (by decide) (by decide)
  have hQCRmin := hmin (i := 5) (j := 3) (k := 6)
    (by decide) (by decide) (by decide)
  have hQRXmin := hmin (i := 5) (j := 6) (k := 2)
    (by decide) (by decide) (by decide)
  have hQAXmin := hmin (i := 5) (j := 0) (k := 2)
    (by decide) (by decide) (by decide)
  have hQXRmin := hmin (i := 5) (j := 2) (k := 6)
    (by decide) (by decide) (by decide)
  have hQRAmin := hmin (i := 5) (j := 6) (k := 0)
    (by decide) (by decide) (by decide)
  have hBCQmin := hmin (i := 1) (j := 3) (k := 5)
    (by decide) (by decide) (by decide)
  have hAQRmin := hmin (i := 0) (j := 5) (k := 6)
    (by decide) (by decide) (by decide)

  obtain ⟨hPBXpos, hPXApos, _hPABpos⟩ :=
    inTriStrict_fan_pos hABX hPABX
  have hAXPneg : sig (v 0) (v 2) (v 4) < 0 := by
    have hid : sig (v 0) (v 2) (v 4) = -sig (v 4) (v 2) (v 0) := by
      simp only [sig]
      ring
    rw [hid]
    linarith
  obtain ⟨_hQXCpos, hQCBpos, hQBXpos⟩ :=
    inTriStrict_fan_pos hBXC hQBXC
  have hBCQneg : sig (v 1) (v 3) (v 5) < 0 := by
    have hid : sig (v 1) (v 3) (v 5) = -sig (v 5) (v 3) (v 1) := by
      simp only [sig]
      ring
    rw [hid]
    linarith

  have hPBXmin := hmin (i := 4) (j := 1) (k := 2)
    (by decide) (by decide) (by decide)
  have hPXAmin := hmin (i := 4) (j := 2) (k := 0)
    (by decide) (by decide) (by decide)
  have hU6 : 6 ≤ sig (v 0) (v 1) (v 2) :=
    singleton_one_point_six hABX hPABX hPBXmin hPXAmin hPABmin
  have hQCBmin := hmin (i := 5) (j := 3) (k := 1)
    (by decide) (by decide) (by decide)
  have hQBXmin := hmin (i := 5) (j := 1) (k := 2)
    (by decide) (by decide) (by decide)
  have hE6 : 6 ≤ sig (v 1) (v 2) (v 3) :=
    singleton_one_point_six hBXC hQBXC hQXCmin hQCBmin hQBXmin

  have hfanABC := fan_sum (v 6) (v 0) (v 1) (v 3)
  have hfanAXC := fan_sum (v 6) (v 0) (v 2) (v 3)

  have hProws :
      (6 ≤ sig (v 6) (v 0) (v 1) ∧
        2 * (sig (v 6) (v 0) (v 2) + 4) ≤
          (sig (v 6) (v 0) (v 1) - 4) *
            (sig (v 0) (v 1) (v 2) - 2) ∧
        (2 * (sig (v 6) (v 3) (v 0) + 4) ≤
            (sig (v 6) (v 0) (v 1) - 4) *
              (sig (v 6) (v 1) (v 3) - 2) ∨
          2 * (sig (v 6) (v 1) (v 3) + 4) ≤
            (sig (v 6) (v 0) (v 1) - 4) *
              (sig (v 6) (v 3) (v 0) - 2))) ∨
      (6 ≤ sig (v 6) (v 1) (v 3) ∧
        2 * (sig (v 6) (v 0) (v 2) +
            (sig (v 6) (v 2) (v 3) + sig (v 6) (v 0) (v 2) +
              sig (v 6) (v 3) (v 0)) + 4) ≤
          (sig (v 6) (v 1) (v 3) - 4) *
            (sig (v 0) (v 1) (v 2) - 2)) := by
    rcases hPfan with hPA | hPZ
    · exact Or.inl (hullFive_singleton_A_rows
        hApos hZpos.le hDpos.le hNpos.le hABX.le hPA hAXPneg
        hPABmin hPBRmin hPRAmin hAXPmin hCPRmin)
    · right
      obtain ⟨hlarge, hrow⟩ := hullFive_singleton_Z_rows
        hZpos hNpos.le hABX.le hAXC.le hPZ hAXPneg
        hPBCmin hPCRmin hPRBmin hAXPmin
      exact ⟨hlarge, by nlinarith [hrow, hfanAXC]⟩

  have hQrows :
      (6 ≤ sig (v 6) (v 2) (v 3) ∧
        2 * (sig (v 6) (v 1) (v 3) + 4) ≤
          (sig (v 6) (v 2) (v 3) - 4) *
            (sig (v 1) (v 2) (v 3) - 2) ∧
        (2 * (sig (v 6) (v 3) (v 0) + 4) ≤
            (sig (v 6) (v 2) (v 3) - 4) *
              (sig (v 6) (v 0) (v 2) - 2) ∨
          2 * (sig (v 6) (v 0) (v 2) + 4) ≤
            (sig (v 6) (v 2) (v 3) - 4) *
              (sig (v 6) (v 3) (v 0) - 2))) ∨
      (6 ≤ sig (v 6) (v 0) (v 2) ∧
        2 * (sig (v 6) (v 1) (v 3) +
            (sig (v 6) (v 0) (v 1) + sig (v 6) (v 1) (v 3) +
              sig (v 6) (v 3) (v 0)) + 4) ≤
          (sig (v 6) (v 0) (v 2) - 4) *
            (sig (v 1) (v 2) (v 3) - 2)) := by
    rcases hQfan with hQG | hQN
    · exact Or.inl (hullFive_singleton_G_rows
        hGpos hZpos.le hDpos.le hNpos.le hBXC.le hQG hBCQneg
        hQXCmin hQCRmin hQRXmin hBCQmin hAQRmin)
    · right
      obtain ⟨hlarge, hrow⟩ := hullFive_singleton_N_rows
        hNpos hZpos.le hBXC.le hABC.le hQN hBCQneg
        hQAXmin hQXRmin hQRAmin hBCQmin
      exact ⟨hlarge, by nlinarith [hrow, hfanABC]⟩

  apply singleton_of_fan_rows
    (A := sig (v 6) (v 0) (v 1))
    (Z := sig (v 6) (v 1) (v 3))
    (D := sig (v 6) (v 3) (v 0))
    (G := sig (v 6) (v 2) (v 3))
    (N := sig (v 6) (v 0) (v 2))
    (E := sig (v 1) (v 2) (v 3))
    (U := sig (v 0) (v 1) (v 2))
    (K := sig (v 0) (v 1) (v 3) + sig (v 1) (v 2) (v 3))
  · exact hAmin
  · exact hZmin
  · exact hDmin
  · exact hGmin
  · exact hNmin
  · exact hE6
  · exact hU6
  · nlinarith [hfanABC]
  · nlinarith [hfanAXC,
      hullFive_singleton_quadrilateral_sum (v 0) (v 1) (v 2) (v 3)]
  · exact hullFive_singleton_plucker (v 0) (v 1) (v 2) (v 3) (v 6)
  · exact hProws
  · exact hQrows

end Heilbronn8.TriHull
