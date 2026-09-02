import Heilbronn8.TriHull.Main

set_option maxHeartbeats 0

/-!
# A three-point fan-sector dichotomy

Let `P`, `Q`, and `R` be strict interior points of the same oriented triangle
`ABC`.  Relative to any one of the three points, each of the other two lies
strictly in one of the three fan cells

* `0`: `PBC`,
* `1`: `PCA`,
* `2`: `PAB`.

If no two partition lines are collinear, then either some anchor sees the
other two points in the same fan cell, or some anchor sees them in the two
cells `0` and `1`.  The proof is division-free.  Its finite core says that,
after excluding those alternatives, the three half-edges of color `2` form a
directed cycle.  But membership in fan cell `2` strictly decreases the
opposite signed subarea `sig _ A B`, so such a cycle is impossible.
-/

namespace Heilbronn8.TriHull

/-- The three partition lines through `X` and the vertices of `ABC` miss `Y`.
This is precisely the genericity needed by `strict_fan_partition`. -/
def FanPairGeneric (X Y A B C : Point) : Prop :=
  sig X A Y ≠ 0 ∧ sig X B Y ≠ 0 ∧ sig X C Y ≠ 0

/-- At anchor `X`, the points `Y` and `Z` occupy the same strict fan cell. -/
def SameFanSectorAt (X Y Z A B C : Point) : Prop :=
  ∃ i : Fin 3,
    InFanCell Y X A B C i ∧ InFanCell Z X A B C i

/-- At anchor `X`, the points `Y` and `Z` occupy the distinguished adjacent
fan cells `XBC` and `XCA`, in either order. -/
def AdjacentABFanSectorsAt (X Y Z A B C : Point) : Prop :=
  (InFanCell Y X A B C 0 ∧ InFanCell Z X A B C 1) ∨
    (InFanCell Y X A B C 1 ∧ InFanCell Z X A B C 0)

/-- The signed area opposite a fan cell. -/
def fanOppositeArea (X A B C : Point) : Fin 3 → ℝ :=
  ![sig X B C, sig X C A, sig X A B]

private lemma sig_reverse_middle_ne {X Y V : Point}
    (h : sig X V Y ≠ 0) : sig Y V X ≠ 0 := by
  intro hrev
  apply h
  calc
    sig X V Y = -sig Y V X := by
      simp only [sig]
      ring
    _ = 0 := by rw [hrev]; ring

lemma FanPairGeneric.reverse {X Y A B C : Point}
    (h : FanPairGeneric X Y A B C) : FanPairGeneric Y X A B C := by
  rcases h with ⟨hA, hB, hC⟩
  exact ⟨sig_reverse_middle_ne hA, sig_reverse_middle_ne hB,
    sig_reverse_middle_ne hC⟩

/-- A generic ordered pair of strict interior points has a fan-cell color. -/
lemma fanCell_exists_of_generic {A B C X Y : Point}
    (hX : InTriStrict X A B C) (hY : InTriStrict Y A B C)
    (hgen : FanPairGeneric X Y A B C) :
    ∃ i : Fin 3, InFanCell Y X A B C i := by
  rcases hgen with ⟨hXA, hXB, hXC⟩
  rcases strict_fan_partition hX hY hXA hXB hXC with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

private lemma strict_opposite_subarea {X Y U V : Point}
    (hXUV : 0 < sig X U V) (hY : InTriStrict Y X U V) :
    sig Y U V < sig X U V := by
  obtain ⟨hYUV, hYVX, hYXU⟩ := inTriStrict_fan_pos hXUV hY
  nlinarith [fan_sum Y X U V]

/-- Moving strictly into fan cell `i` strictly decreases its opposite signed
subarea. -/
lemma inFanCell_oppositeArea_lt {A B C X Y : Point} {i : Fin 3}
    (hABC : 0 < sig A B C) (hX : InTriStrict X A B C)
    (hcell : InFanCell Y X A B C i) :
    fanOppositeArea Y A B C i < fanOppositeArea X A B C i := by
  obtain ⟨hXBC, hXCA, hXAB⟩ := inTriStrict_fan_pos hABC hX
  fin_cases i
  · simpa [fanOppositeArea] using
      strict_opposite_subarea hXBC (by simpa [InFanCell] using hcell)
  · simpa [fanOppositeArea] using
      strict_opposite_subarea hXCA (by simpa [InFanCell] using hcell)
  · simpa [fanOppositeArea] using
      strict_opposite_subarea hXAB (by simpa [InFanCell] using hcell)

/-- Opposite directions along an unordered pair cannot have the same strict
fan-cell color. -/
lemma reverse_fanCell_ne {A B C X Y : Point} {i j : Fin 3}
    (hABC : 0 < sig A B C)
    (hX : InTriStrict X A B C) (hY : InTriStrict Y A B C)
    (hXY : InFanCell Y X A B C i)
    (hYX : InFanCell X Y A B C j) : i ≠ j := by
  intro hij
  subst j
  have hdown := inFanCell_oppositeArea_lt hABC hX hXY
  have hup := inFanCell_oppositeArea_lt hABC hY hYX
  linarith

private def IsABColorPair (i j : Fin 3) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)

/-- Finite directed-edge core.  If reverse half-edges have different colors,
then, after excluding a repeated outgoing color and an outgoing `{0,1}` pair,
the color-`2` half-edges form one of the two directed three-cycles. -/
private theorem six_color_dichotomy :
    ∀ pq pr qp qr rp rq : Fin 3,
      pq ≠ qp → pr ≠ rp → qr ≠ rq →
      (pq = pr ∨ qp = qr ∨ rp = rq) ∨
      (IsABColorPair pq pr ∨ IsABColorPair qp qr ∨
        IsABColorPair rp rq) ∨
      ((pq = 2 ∧ qr = 2 ∧ rp = 2) ∨
        (pr = 2 ∧ rq = 2 ∧ qp = 2)) := by
  intro pq pr qp qr rp rq
  fin_cases pq <;> fin_cases pr <;> fin_cases qp <;>
    fin_cases qr <;> fin_cases rp <;> fin_cases rq <;>
    simp [IsABColorPair]

/-- Three generic strict interior points satisfy the fixed-anchor fan-sector
dichotomy: at some anchor the other two are either in one common fan cell or
in the distinguished adjacent cells `PBC` and `PCA`.

The statement is coordinate-free and division-free. -/
theorem three_point_fan_sector_dichotomy
    {A B C P Q R : Point}
    (hABC : 0 < sig A B C)
    (hP : InTriStrict P A B C)
    (hQ : InTriStrict Q A B C)
    (hR : InTriStrict R A B C)
    (hPQ : FanPairGeneric P Q A B C)
    (hPR : FanPairGeneric P R A B C)
    (hQR : FanPairGeneric Q R A B C) :
    (SameFanSectorAt P Q R A B C ∨
      SameFanSectorAt Q P R A B C ∨
      SameFanSectorAt R P Q A B C) ∨
    (AdjacentABFanSectorsAt P Q R A B C ∨
      AdjacentABFanSectorsAt Q P R A B C ∨
      AdjacentABFanSectorsAt R P Q A B C) := by
  have hQP := hPQ.reverse
  have hRP := hPR.reverse
  have hRQ := hQR.reverse
  obtain ⟨pq, hpq⟩ := fanCell_exists_of_generic hP hQ hPQ
  obtain ⟨pr, hpr⟩ := fanCell_exists_of_generic hP hR hPR
  obtain ⟨qp, hqp⟩ := fanCell_exists_of_generic hQ hP hQP
  obtain ⟨qr, hqr⟩ := fanCell_exists_of_generic hQ hR hQR
  obtain ⟨rp, hrp⟩ := fanCell_exists_of_generic hR hP hRP
  obtain ⟨rq, hrq⟩ := fanCell_exists_of_generic hR hQ hRQ
  have hpq_ne : pq ≠ qp := reverse_fanCell_ne hABC hP hQ hpq hqp
  have hpr_ne : pr ≠ rp := reverse_fanCell_ne hABC hP hR hpr hrp
  have hqr_ne : qr ≠ rq := reverse_fanCell_ne hABC hQ hR hqr hrq
  rcases six_color_dichotomy pq pr qp qr rp rq hpq_ne hpr_ne hqr_ne with
      hsame | hab | hcycle
  · left
    rcases hsame with h | h | h
    · exact Or.inl ⟨pq, hpq, by simpa [h] using hpr⟩
    · exact Or.inr (Or.inl ⟨qp, hqp, by simpa [h] using hqr⟩)
    · exact Or.inr (Or.inr ⟨rp, hrp, by simpa [h] using hrq⟩)
  · right
    rcases hab with hab | hab | hab
    · rcases hab with ⟨hpq0, hpr1⟩ | ⟨hpq1, hpr0⟩
      · exact Or.inl (Or.inl ⟨by simpa [hpq0] using hpq,
          by simpa [hpr1] using hpr⟩)
      · exact Or.inl (Or.inr ⟨by simpa [hpq1] using hpq,
          by simpa [hpr0] using hpr⟩)
    · rcases hab with ⟨hqp0, hqr1⟩ | ⟨hqp1, hqr0⟩
      · exact Or.inr (Or.inl (Or.inl ⟨by simpa [hqp0] using hqp,
          by simpa [hqr1] using hqr⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨by simpa [hqp1] using hqp,
          by simpa [hqr0] using hqr⟩))
    · rcases hab with ⟨hrp0, hrq1⟩ | ⟨hrp1, hrq0⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by simpa [hrp0] using hrp,
          by simpa [hrq1] using hrq⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by simpa [hrp1] using hrp,
          by simpa [hrq0] using hrq⟩))
  · exfalso
    rcases hcycle with ⟨hpq2, hqr2, hrp2⟩ | ⟨hpr2, hrq2, hqp2⟩
    · have h1 := inFanCell_oppositeArea_lt hABC hP hpq
      have h2 := inFanCell_oppositeArea_lt hABC hQ hqr
      have h3 := inFanCell_oppositeArea_lt hABC hR hrp
      rw [hpq2] at h1
      rw [hqr2] at h2
      rw [hrp2] at h3
      simp only [fanOppositeArea] at h1 h2 h3
      linarith
    · have h1 := inFanCell_oppositeArea_lt hABC hP hpr
      have h2 := inFanCell_oppositeArea_lt hABC hR hrq
      have h3 := inFanCell_oppositeArea_lt hABC hQ hqp
      rw [hpr2] at h1
      rw [hrq2] at h2
      rw [hqp2] at h3
      simp only [fanOppositeArea] at h1 h2 h3
      linarith

end Heilbronn8.TriHull
