import Heilbronn8.Cover

namespace Heilbronn8.QuadHull

namespace SectorCensus

/-- The four open sectors `ABO`, `BCO`, `CDO`, `DAO`, in cyclic order. -/
abbrev Sector := Fin 4

/-- Abstract labels for the four points inside the quadrilateral. -/
abbrev Inner := Fin 4

abbrev Assignment := Inner → Sector
abbrev Census := Sector → ℕ

/--
The eight symmetries of the cyclic sector square.  `(k, false)` acts by
`i ↦ k + i`, while `(k, true)` acts by `i ↦ k - i`, modulo four.
-/
abbrev QuadSym := Sector × Bool

def sectorAct (g : QuadSym) (i : Sector) : Sector :=
  let j : ℕ :=
    match g.2 with
    | false => i.val
    | true => 4 - i.val
  ⟨(g.1.val + j) % 4, Nat.mod_lt _ (by decide)⟩

def census (a : Assignment) (s : Sector) : ℕ :=
  ((Finset.univ : Finset Inner).filter (fun x => a x = s)).card

/-- Equality of census vectors up to cyclic rotation or reflection. -/
def SameOrbit (n p : Census) : Prop :=
  ∃ g : QuadSym, ∀ s : Sector, n (sectorAct g s) = p s

/-- One of the two diagonals has two points on each side. -/
def Balanced (n : Census) : Prop :=
  (n 0 + n 1 = 2 ∧ n 2 + n 3 = 2) ∨
  (n 1 + n 2 = 2 ∧ n 3 + n 0 = 2)

def p4000 : Census := ![4, 0, 0, 0]
def p3100 : Census := ![3, 1, 0, 0]
def p3010 : Census := ![3, 0, 1, 0]
def p2101 : Census := ![2, 1, 0, 1]

def Classified (n : Census) : Prop :=
  Balanced n ∨
  SameOrbit n p4000 ∨
  SameOrbit n p3100 ∨
  SameOrbit n p3010 ∨
  SameOrbit n p2101

private instance (n p : Census) : Decidable (SameOrbit n p) := by
  unfold SameOrbit
  infer_instance

private instance (n : Census) : Decidable (Balanced n) := by
  unfold Balanced
  infer_instance

private instance (n : Census) : Decidable (Classified n) := by
  unfold Classified
  infer_instance

private theorem classifyFourSectors_vector
    (a0 a1 a2 a3 : Sector) :
    Classified (census ![a0, a1, a2, a3]) := by
  fin_cases a0 <;> fin_cases a1 <;> fin_cases a2 <;> fin_cases a3 <;> decide

/--
Every assignment of four labels to four cyclic sectors is either split `2+2`
by a diagonal or belongs to one of the four exceptional dihedral orbits.
-/
theorem classifyFourSectors (a : Assignment) : Classified (census a) := by
  have ha : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [ha]
  exact classifyFourSectors_vector _ _ _ _

end SectorCensus

/-- A nonzero `minTri` makes every determinant on three distinct labels nonzero. -/
lemma sig_ne_zero_of_minTri_ne_zero
    {v : Fin 8 → ℝ × ℝ} {i j k : Fin 8}
    (hm : minTri v ≠ 0)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    sig (v i) (v j) (v k) ≠ 0 := by
  intro hzero
  apply hm
  have hmin := minTri_le_abs_sig_of_pairwise_ne v hij hik hjk
  rw [hzero, abs_zero] at hmin
  exact le_antisymm hmin (minTri_nonneg v)

end Heilbronn8.QuadHull
