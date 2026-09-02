import Heilbronn8.TriHull.HullFive210Dispatch

/-!
# Maximality-free hull-five `2 + 1` redispatch

For a strictly oriented quadrilateral `A-B-X-C`, put

* `S = ABC`, `E = BXC`,
* `U = ABX`, `V = AXC`.

The identity `S + E = U + V` implies that one of the four cyclic
quadrilateral charts has its distinguished triangle at least as large as
both adjacent cells.  In the two quarter-turn cases the three selected
points are first repartitioned across the other diagonal.  Homogeneous
repartitions are exactly the original `HullFive300Cell`s; mixed
repartitions call the existing maximal dispatcher, and its `300` residual
is impossible because the original input contains points in both `U` and
`V`.

The fifth hull label is deliberately not used here.  Consequently this is a
local quadrilateral theorem and is valid for either end-zero fan chart.  A
caller adds the remaining positive fan triangle, or forwards the returned
`300` cell to the hull-five `300` handler.
-/

namespace Heilbronn8.TriHull

private lemma inTriStrict_rotate_maxFree {P A B C : Point}
    (h : InTriStrict P A B C) : InTriStrict P B C A := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, rfl⟩ := h
  exact ⟨y, z, x, hy, hz, hx, by linarith, by module⟩

private lemma inTriStrict_rotate2_maxFree {P A B C : Point}
    (h : InTriStrict P A B C) : InTriStrict P C A B :=
  inTriStrict_rotate_maxFree (inTriStrict_rotate_maxFree h)

private lemma cellABO_in_ABC_maxFree
    {P A B C O : Point}
    (hP : InTriStrict P A B O) (hO : InSegStrict O B C) :
    InTriStrict P A B C := by
  have h := inTriStrict_replace_third_segment
    (R := P) (X := A) (C := B) (B := C)
    hP (inSegStrict_symm hO)
  exact inTriStrict_rotate_maxFree h

private lemma cellBXO_in_BXC_maxFree
    {P B X C O : Point}
    (hP : InTriStrict P B X O) (hO : InSegStrict O B C) :
    InTriStrict P B X C :=
  inTriStrict_replace_third_segment_reflected hP hO

private lemma cellXCO_in_BXC_maxFree
    {P B X C O : Point}
    (hP : InTriStrict P X C O) (hO : InSegStrict O B C) :
    InTriStrict P B X C :=
  inTriStrict_replace_third_segment hP hO

private lemma cellCAO_in_ABC_maxFree
    {P A B C O : Point}
    (hP : InTriStrict P C A O) (hO : InSegStrict O B C) :
    InTriStrict P A B C := by
  have h := inTriStrict_replace_third_segment_reflected
    (R := P) (B := C) (X := A) (C := B)
    hP (inSegStrict_symm hO)
  exact inTriStrict_rotate_maxFree h

/-- A strict point in either `AX`-diagonal cell lies in exactly one of the
two `BC`-diagonal cells.  Only the inclusive direction is needed here; the
nonzero `BCP` determinant removes the separating diagonal. -/
lemma inTriStrict_quad_otherDiagonal
    {P A B X C : Point}
    (hABC : 0 < sig A B C) (hBXC : 0 < sig B X C)
    (hABX : 0 < sig A B X) (hAXC : 0 < sig A X C)
    (hBCP : sig B C P ≠ 0)
    (hP : InTriStrict P A B X ∨ InTriStrict P A X C) :
    InTriStrict P A B C ∨ InTriStrict P B X C := by
  obtain ⟨O, hOAX, hOBC⟩ :=
    strictQuad_diagonal_intersection hABC hBXC hABX hAXC
  rcases hP with hPABX | hPAXC
  · have hsplit := inTriStrict_split_through_edge hPABX hOAX
      (inSegStrict_left_sig_ne hOBC hBCP)
    rcases hsplit with hPABO | hPBXO
    · exact Or.inl (cellABO_in_ABC_maxFree hPABO hOBC)
    · exact Or.inr (cellBXO_in_BXC_maxFree hPBXO hOBC)
  · have hCBP : sig C B P ≠ 0 := by
      have hrotate : sig C P B = sig B C P := by
        calc
          sig C P B = sig P B C := sig_rotate C P B
          _ = sig B C P := sig_rotate P B C
      rw [sig_swap]
      rw [hrotate]
      exact neg_ne_zero.mpr hBCP
    have hsplit := inTriStrict_split_through_edge
      (inTriStrict_rotate_maxFree hPAXC) (inSegStrict_symm hOAX)
      (inSegStrict_left_sig_ne (inSegStrict_symm hOBC) hCBP)
    rcases hsplit with hPXCO | hPCAO
    · exact Or.inr (cellXCO_in_BXC_maxFree hPXCO hOBC)
    · exact Or.inl (cellCAO_in_ABC_maxFree hPCAO hOBC)

private lemma central_right_strict_disjoint
    {P A B X C : Point}
    (hABC : 0 < sig A B C) (hBXC : 0 < sig B X C)
    (hcentral : InTriStrict P A B C)
    (hright : InTriStrict P B X C) : False := by
  obtain ⟨hPBC, _, _⟩ := inTriStrict_fan_pos hABC hcentral
  obtain ⟨_, hPCB, _⟩ := inTriStrict_fan_pos hBXC hright
  have hswap : sig P C B = -sig P B C := by
    simp only [sig]
    ring
  rw [hswap] at hPCB
  linarith

/-- Run the `ABX`-major dispatcher when both output `300` cells are known to
be non-homogeneous. -/
private theorem ax_dispatch_bound_of_cross_occupied
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)))
    (hABXmax :
      sig (v (e 0)) (v (e 1)) (v (e 2)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hAXCmax :
      sig (v (e 0)) (v (e 2)) (v (e 3)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hPABX : InTriStrict (v (e 5))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hQABX : InTriStrict (v (e 6))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hRAXC : InTriStrict (v (e 7))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hright :
      InTriStrict (v (e 5)) (v (e 1)) (v (e 2)) (v (e 3)) ∨
      InTriStrict (v (e 6)) (v (e 1)) (v (e 2)) (v (e 3)) ∨
      InTriStrict (v (e 7)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hcentral :
      InTriStrict (v (e 5)) (v (e 0)) (v (e 1)) (v (e 3)) ∨
      InTriStrict (v (e 6)) (v (e 0)) (v (e 1)) (v (e 3)) ∨
      InTriStrict (v (e 7)) (v (e 0)) (v (e 1)) (v (e 3))) :
    23 ≤ sig (v (e 0)) (v (e 1)) (v (e 3)) +
      sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  rcases hullFive_ax_major_membership_dispatch_210_of_orientations
      v e he hmin hABC hBXC hABX hAXC hABXmax hAXCmax
        hPABX hQABX hRAXC with hcell | hbound
  · cases hcell with
    | central hP hQ hR =>
        rcases hright with hright | hright | hright
        · exact False.elim
            (central_right_strict_disjoint hABC hBXC hP hright)
        · exact False.elim
            (central_right_strict_disjoint hABC hBXC hQ hright)
        · exact False.elim
            (central_right_strict_disjoint hABC hBXC hR hright)
    | right hP hQ hR =>
        rcases hcentral with hcentral | hcentral | hcentral
        · exact False.elim
            (central_right_strict_disjoint hABC hBXC hcentral hP)
        · exact False.elim
            (central_right_strict_disjoint hABC hBXC hcentral hQ)
        · exact False.elim
            (central_right_strict_disjoint hABC hBXC hcentral hR)
  · exact hbound

/-- The `AXC`-major counterpart of
`ax_dispatch_bound_of_cross_occupied`. -/
private theorem axc_dispatch_bound_of_cross_occupied
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)))
    (hABXmax :
      sig (v (e 0)) (v (e 1)) (v (e 2)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hAXCmax :
      sig (v (e 0)) (v (e 2)) (v (e 3)) ≤
        sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hPAXC : InTriStrict (v (e 5))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hQAXC : InTriStrict (v (e 6))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hRABX : InTriStrict (v (e 7))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hright :
      InTriStrict (v (e 5)) (v (e 1)) (v (e 2)) (v (e 3)) ∨
      InTriStrict (v (e 6)) (v (e 1)) (v (e 2)) (v (e 3)) ∨
      InTriStrict (v (e 7)) (v (e 1)) (v (e 2)) (v (e 3)))
    (hcentral :
      InTriStrict (v (e 5)) (v (e 0)) (v (e 1)) (v (e 3)) ∨
      InTriStrict (v (e 6)) (v (e 0)) (v (e 1)) (v (e 3)) ∨
      InTriStrict (v (e 7)) (v (e 0)) (v (e 1)) (v (e 3))) :
    23 ≤ sig (v (e 0)) (v (e 1)) (v (e 3)) +
      sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  rcases hullFive_axc_major_membership_dispatch_210_of_orientations
      v e he hmin hABC hBXC hABX hAXC hABXmax hAXCmax
        hPAXC hQAXC hRABX with hcell | hbound
  · cases hcell with
    | central hP hQ hR =>
        rcases hright with hright | hright | hright
        · exact False.elim
            (central_right_strict_disjoint hABC hBXC hP hright)
        · exact False.elim
            (central_right_strict_disjoint hABC hBXC hQ hright)
        · exact False.elim
            (central_right_strict_disjoint hABC hBXC hR hright)
    | right hP hQ hR =>
        rcases hcentral with hcentral | hcentral | hcentral
        · exact False.elim
            (central_right_strict_disjoint hABC hBXC hcentral hP)
        · exact False.elim
            (central_right_strict_disjoint hABC hBXC hcentral hQ)
        · exact False.elim
            (central_right_strict_disjoint hABC hBXC hcentral hR)
  · exact hbound

/-! ## The maximality-free outer dispatch -/

/-- The `ABX,ABX,AXC` dispatcher with no metric maximality hypotheses. -/
theorem hullFive_ax_major_membership_dispatch_210_maxFree
    (w : Fin 8 → Point)
    (hmin : AllTrianglesMinAreaOne w)
    (hABC : 0 < sig (w 0) (w 1) (w 3))
    (hBXC : 0 < sig (w 1) (w 2) (w 3))
    (hABX : 0 < sig (w 0) (w 1) (w 2))
    (hAXC : 0 < sig (w 0) (w 2) (w 3))
    (hPABX : InTriStrict (w 5) (w 0) (w 1) (w 2))
    (hQABX : InTriStrict (w 6) (w 0) (w 1) (w 2))
    (hRAXC : InTriStrict (w 7) (w 0) (w 2) (w 3)) :
    HullFive300Cell w id ∨
      23 ≤ sig (w 0) (w 1) (w 3) + sig (w 1) (w 2) (w 3) := by
  let S : ℝ := sig (w 0) (w 1) (w 3)
  let E : ℝ := sig (w 1) (w 2) (w 3)
  let U : ℝ := sig (w 0) (w 1) (w 2)
  let V : ℝ := sig (w 0) (w 2) (w 3)
  have hsum : S + E = U + V := by
    simpa [S, E, U, V] using
      hullFive_singleton_quadrilateral_sum (w 0) (w 1) (w 2) (w 3)
  have hPSE :
      InTriStrict (w 5) (w 0) (w 1) (w 3) ∨
        InTriStrict (w 5) (w 1) (w 2) (w 3) :=
    inTriStrict_quad_otherDiagonal hABC hBXC hABX hAXC
      (hmin.sig_ne_zero (i := 1) (j := 3) (k := 5)
        (by decide) (by decide) (by decide)) (Or.inl hPABX)
  have hQSE :
      InTriStrict (w 6) (w 0) (w 1) (w 3) ∨
        InTriStrict (w 6) (w 1) (w 2) (w 3) :=
    inTriStrict_quad_otherDiagonal hABC hBXC hABX hAXC
      (hmin.sig_ne_zero (i := 1) (j := 3) (k := 6)
        (by decide) (by decide) (by decide)) (Or.inl hQABX)
  have hRSE :
      InTriStrict (w 7) (w 0) (w 1) (w 3) ∨
        InTriStrict (w 7) (w 1) (w 2) (w 3) :=
    inTriStrict_quad_otherDiagonal hABC hBXC hABX hAXC
      (hmin.sig_ne_zero (i := 1) (j := 3) (k := 7)
        (by decide) (by decide) (by decide)) (Or.inr hRAXC)

  by_cases hlow : E ≤ U ∧ E ≤ V
  · have hUS : U ≤ S := by linarith [hsum, hlow.2]
    have hVS : V ≤ S := by linarith [hsum, hlow.1]
    simpa [S, E, U, V] using
      hullFive_ax_major_membership_dispatch_210_of_orientations
        w id (by intro i j hij; simpa using hij) hmin
        hABC hBXC hABX hAXC
        (by simpa [S, U] using hUS) (by simpa [S, V] using hVS)
        hPABX hQABX hRAXC
  · by_cases hhigh : U ≤ E ∧ V ≤ E
    · let q2 : Fin 8 → Fin 8 := ![2, 3, 0, 1, 4, 5, 6, 7]
      have hE' : 0 < sig (w 2) (w 3) (w 1) := by
        rw [sig_rotate (w 2) (w 3) (w 1),
          sig_rotate (w 3) (w 1) (w 2)]
        exact hBXC
      have hS' : 0 < sig (w 3) (w 0) (w 1) := by
        rw [sig_rotate (w 3) (w 0) (w 1)]
        exact hABC
      have hV' : 0 < sig (w 2) (w 3) (w 0) := by
        rw [sig_rotate (w 2) (w 3) (w 0),
          sig_rotate (w 3) (w 0) (w 2)]
        exact hAXC
      have hU' : 0 < sig (w 2) (w 0) (w 1) := by
        rw [sig_rotate (w 2) (w 0) (w 1)]
        exact hABX
      have hVE' : sig (w 2) (w 3) (w 0) ≤
          sig (w 2) (w 3) (w 1) := by
        rw [sig_rotate (w 2) (w 3) (w 0),
          sig_rotate (w 3) (w 0) (w 2),
          sig_rotate (w 2) (w 3) (w 1),
          sig_rotate (w 3) (w 1) (w 2)]
        simpa [V, E] using hhigh.2
      have hUE' : sig (w 2) (w 0) (w 1) ≤
          sig (w 2) (w 3) (w 1) := by
        rw [sig_rotate (w 2) (w 0) (w 1),
          sig_rotate (w 2) (w 3) (w 1),
          sig_rotate (w 3) (w 1) (w 2)]
        simpa [U, E] using hhigh.1
      have hd := hullFive_axc_major_membership_dispatch_210_of_orientations
        w q2 (by decide) hmin
          (by simpa [q2] using hE') (by simpa [q2] using hS')
          (by simpa [q2] using hV') (by simpa [q2] using hU')
          (by simpa [q2] using hVE')
          (by simpa [q2] using hUE')
          (by simpa [q2] using inTriStrict_rotate2_maxFree hPABX)
          (by simpa [q2] using inTriStrict_rotate2_maxFree hQABX)
          (by simpa [q2] using inTriStrict_rotate_maxFree hRAXC)
      rcases hd with hcell | hbound
      · left
        cases hcell with
        | central hP hQ hR =>
            exact .right
              (by simpa [q2] using inTriStrict_rotate2_maxFree hP)
              (by simpa [q2] using inTriStrict_rotate2_maxFree hQ)
              (by simpa [q2] using inTriStrict_rotate2_maxFree hR)
        | right hP hQ hR =>
            exact .central
              (by simpa [q2] using inTriStrict_rotate_maxFree hP)
              (by simpa [q2] using inTriStrict_rotate_maxFree hQ)
              (by simpa [q2] using inTriStrict_rotate_maxFree hR)
      · right
        change 23 ≤ S + E
        have hbound' : 23 ≤ E + S := by
          simpa [q2, E, S, sig_rotate (w 2) (w 3) (w 1),
            sig_rotate (w 3) (w 1) (w 2),
            sig_rotate (w 3) (w 0) (w 1)] using hbound
        linarith
    · have hbetween :
          (U < E ∧ E < V) ∨ (V < E ∧ E < U) := by
        by_cases hUE : U < E
        · have hEV : E < V := by
            by_contra hn
            have hVE : V ≤ E := le_of_not_gt hn
            exact hhigh ⟨hUE.le, hVE⟩
          exact Or.inl ⟨hUE, hEV⟩
        · have hEU : E ≤ U := le_of_not_gt hUE
          have hVE : V < E := by
            by_contra hn
            have hEV : E ≤ V := le_of_not_gt hn
            exact hlow ⟨hEU, hEV⟩
          have hEU' : E < U := by
            by_contra hn
            have hUE' : U ≤ E := le_of_not_gt hn
            exact hhigh ⟨hUE', hVE.le⟩
          exact Or.inr ⟨hVE, hEU'⟩
      rcases hbetween with hVEmax | hUEmax
      · have hSV : S ≤ V := by linarith [hsum, hVEmax.1]
        have hEV : E ≤ V := hVEmax.2.le
        have hV' : 0 < sig (w 3) (w 0) (w 2) := by
          rw [sig_rotate (w 3) (w 0) (w 2)]
          exact hAXC
        have hS' : 0 < sig (w 3) (w 0) (w 1) := by
          rw [sig_rotate (w 3) (w 0) (w 1)]
          exact hABC
        have hE' : 0 < sig (w 3) (w 1) (w 2) := by
          rw [sig_rotate (w 3) (w 1) (w 2)]
          exact hBXC
        have hSV' : sig (w 3) (w 0) (w 1) ≤
            sig (w 3) (w 0) (w 2) := by
          rw [sig_rotate (w 3) (w 0) (w 1),
            sig_rotate (w 3) (w 0) (w 2)]
          simpa [S, V] using hSV
        have hEV' : sig (w 3) (w 1) (w 2) ≤
            sig (w 3) (w 0) (w 2) := by
          rw [sig_rotate (w 3) (w 1) (w 2),
            sig_rotate (w 3) (w 0) (w 2)]
          simpa [E, V] using hEV
        rcases hPSE with hPS | hPE <;>
          rcases hQSE with hQS | hQE <;>
          rcases hRSE with hRS | hRE
        · exact Or.inl (.central hPS hQS hRS)
        · let r : Fin 8 → Fin 8 := ![3, 0, 1, 2, 4, 5, 6, 7]
          right
          have hb := ax_dispatch_bound_of_cross_occupied w r (by decide)
            hmin (by simpa [r] using hV') (by simpa [r] using hABX)
            (by simpa [r] using hS') (by simpa [r] using hE')
            (by simpa [r] using hSV') (by simpa [r] using hEV')
            (by simpa [r] using inTriStrict_rotate2_maxFree hPS)
            (by simpa [r] using inTriStrict_rotate2_maxFree hQS)
            (by simpa [r] using inTriStrict_rotate2_maxFree hRE)
            (Or.inl (by simpa [r] using hPABX))
            (Or.inr (Or.inr
              (by simpa [r] using inTriStrict_rotate2_maxFree hRAXC)))
          have hb' : 23 ≤ V + U := by
            simpa [r, V, U, sig_rotate (w 3) (w 0) (w 2)] using hb
          change 23 ≤ S + E
          linarith [hsum, hb']
        · let r : Fin 8 → Fin 8 := ![3, 0, 1, 2, 4, 5, 7, 6]
          right
          have hb := ax_dispatch_bound_of_cross_occupied w r (by decide)
            hmin (by simpa [r] using hV') (by simpa [r] using hABX)
            (by simpa [r] using hS') (by simpa [r] using hE')
            (by simpa [r] using hSV') (by simpa [r] using hEV')
            (by simpa [r] using inTriStrict_rotate2_maxFree hPS)
            (by simpa [r] using inTriStrict_rotate2_maxFree hRS)
            (by simpa [r] using inTriStrict_rotate2_maxFree hQE)
            (Or.inl (by simpa [r] using hPABX))
            (Or.inr (Or.inl
              (by simpa [r] using inTriStrict_rotate2_maxFree hRAXC)))
          have hb' : 23 ≤ V + U := by
            simpa [r, V, U, sig_rotate (w 3) (w 0) (w 2)] using hb
          change 23 ≤ S + E
          linarith [hsum, hb']
        · let r : Fin 8 → Fin 8 := ![3, 0, 1, 2, 4, 6, 7, 5]
          right
          have hb := axc_dispatch_bound_of_cross_occupied w r (by decide)
            hmin (by simpa [r] using hV') (by simpa [r] using hABX)
            (by simpa [r] using hS') (by simpa [r] using hE')
            (by simpa [r] using hSV') (by simpa [r] using hEV')
            (by simpa [r] using inTriStrict_rotate2_maxFree hQE)
            (by simpa [r] using inTriStrict_rotate2_maxFree hRE)
            (by simpa [r] using inTriStrict_rotate2_maxFree hPS)
            (Or.inl (by simpa [r] using hQABX))
            (Or.inr (Or.inl
              (by simpa [r] using inTriStrict_rotate2_maxFree hRAXC)))
          have hb' : 23 ≤ V + U := by
            simpa [r, V, U, sig_rotate (w 3) (w 0) (w 2)] using hb
          change 23 ≤ S + E
          linarith [hsum, hb']
        · let r : Fin 8 → Fin 8 := ![3, 0, 1, 2, 4, 6, 7, 5]
          right
          have hb := ax_dispatch_bound_of_cross_occupied w r (by decide)
            hmin (by simpa [r] using hV') (by simpa [r] using hABX)
            (by simpa [r] using hS') (by simpa [r] using hE')
            (by simpa [r] using hSV') (by simpa [r] using hEV')
            (by simpa [r] using inTriStrict_rotate2_maxFree hQS)
            (by simpa [r] using inTriStrict_rotate2_maxFree hRS)
            (by simpa [r] using inTriStrict_rotate2_maxFree hPE)
            (Or.inl (by simpa [r] using hQABX))
            (Or.inr (Or.inl
              (by simpa [r] using inTriStrict_rotate2_maxFree hRAXC)))
          have hb' : 23 ≤ V + U := by
            simpa [r, V, U, sig_rotate (w 3) (w 0) (w 2)] using hb
          change 23 ≤ S + E
          linarith [hsum, hb']
        · let r : Fin 8 → Fin 8 := ![3, 0, 1, 2, 4, 5, 7, 6]
          right
          have hb := axc_dispatch_bound_of_cross_occupied w r (by decide)
            hmin (by simpa [r] using hV') (by simpa [r] using hABX)
            (by simpa [r] using hS') (by simpa [r] using hE')
            (by simpa [r] using hSV') (by simpa [r] using hEV')
            (by simpa [r] using inTriStrict_rotate2_maxFree hPE)
            (by simpa [r] using inTriStrict_rotate2_maxFree hRE)
            (by simpa [r] using inTriStrict_rotate2_maxFree hQS)
            (Or.inl (by simpa [r] using hPABX))
            (Or.inr (Or.inl
              (by simpa [r] using inTriStrict_rotate2_maxFree hRAXC)))
          have hb' : 23 ≤ V + U := by
            simpa [r, V, U, sig_rotate (w 3) (w 0) (w 2)] using hb
          change 23 ≤ S + E
          linarith [hsum, hb']
        · let r : Fin 8 → Fin 8 := ![3, 0, 1, 2, 4, 5, 6, 7]
          right
          have hb := axc_dispatch_bound_of_cross_occupied w r (by decide)
            hmin (by simpa [r] using hV') (by simpa [r] using hABX)
            (by simpa [r] using hS') (by simpa [r] using hE')
            (by simpa [r] using hSV') (by simpa [r] using hEV')
            (by simpa [r] using inTriStrict_rotate2_maxFree hPE)
            (by simpa [r] using inTriStrict_rotate2_maxFree hQE)
            (by simpa [r] using inTriStrict_rotate2_maxFree hRS)
            (Or.inl (by simpa [r] using hPABX))
            (Or.inr (Or.inr
              (by simpa [r] using inTriStrict_rotate2_maxFree hRAXC)))
          have hb' : 23 ≤ V + U := by
            simpa [r, V, U, sig_rotate (w 3) (w 0) (w 2)] using hb
          change 23 ≤ S + E
          linarith [hsum, hb']
        · exact Or.inl (.right hPE hQE hRE)
      · have hSU : S ≤ U := by linarith [hsum, hUEmax.1]
        have hEU : E ≤ U := hUEmax.2.le
        have hU' : 0 < sig (w 1) (w 2) (w 0) := by
          rw [sig_rotate (w 1) (w 2) (w 0),
            sig_rotate (w 2) (w 0) (w 1)]
          exact hABX
        have hE' : 0 < sig (w 1) (w 2) (w 3) := hBXC
        have hS' : 0 < sig (w 1) (w 3) (w 0) := by
          rw [sig_rotate (w 1) (w 3) (w 0),
            sig_rotate (w 3) (w 0) (w 1)]
          exact hABC
        have hV' : 0 < sig (w 2) (w 3) (w 0) := by
          rw [sig_rotate (w 2) (w 3) (w 0),
            sig_rotate (w 3) (w 0) (w 2)]
          exact hAXC
        have hEU' : sig (w 1) (w 2) (w 3) ≤
            sig (w 1) (w 2) (w 0) := by
          rw [sig_rotate (w 1) (w 2) (w 0),
            sig_rotate (w 2) (w 0) (w 1)]
          simpa [E, U] using hEU
        have hSU' : sig (w 1) (w 3) (w 0) ≤
            sig (w 1) (w 2) (w 0) := by
          rw [sig_rotate (w 1) (w 3) (w 0),
            sig_rotate (w 3) (w 0) (w 1),
            sig_rotate (w 1) (w 2) (w 0),
            sig_rotate (w 2) (w 0) (w 1)]
          simpa [S, U] using hSU
        rcases hPSE with hPS | hPE <;>
          rcases hQSE with hQS | hQE <;>
          rcases hRSE with hRS | hRE
        · exact Or.inl (.central hPS hQS hRS)
        · let r : Fin 8 → Fin 8 := ![1, 2, 3, 0, 4, 5, 6, 7]
          right
          have hb := axc_dispatch_bound_of_cross_occupied w r (by decide)
            hmin (by simpa [r] using hU') (by simpa [r] using hV')
            (by simpa [r] using hE') (by simpa [r] using hS')
            (by simpa [r] using hEU') (by simpa [r] using hSU')
            (by simpa [r] using inTriStrict_rotate_maxFree hPS)
            (by simpa [r] using inTriStrict_rotate_maxFree hQS)
            (by simpa [r] using hRE)
            (Or.inr (Or.inr
              (by simpa [r] using inTriStrict_rotate_maxFree hRAXC)))
            (Or.inl
              (by simpa [r] using inTriStrict_rotate_maxFree hPABX))
          have hb' : 23 ≤ U + V := by
            simpa [r, U, V, sig_rotate (w 1) (w 2) (w 0),
              sig_rotate (w 2) (w 0) (w 1),
              sig_rotate (w 2) (w 3) (w 0),
              sig_rotate (w 3) (w 0) (w 2)] using hb
          change 23 ≤ S + E
          linarith [hsum, hb']
        · let r : Fin 8 → Fin 8 := ![1, 2, 3, 0, 4, 5, 7, 6]
          right
          have hb := axc_dispatch_bound_of_cross_occupied w r (by decide)
            hmin (by simpa [r] using hU') (by simpa [r] using hV')
            (by simpa [r] using hE') (by simpa [r] using hS')
            (by simpa [r] using hEU') (by simpa [r] using hSU')
            (by simpa [r] using inTriStrict_rotate_maxFree hPS)
            (by simpa [r] using inTriStrict_rotate_maxFree hRS)
            (by simpa [r] using hQE)
            (Or.inr (Or.inl
              (by simpa [r] using inTriStrict_rotate_maxFree hRAXC)))
            (Or.inl
              (by simpa [r] using inTriStrict_rotate_maxFree hPABX))
          have hb' : 23 ≤ U + V := by
            simpa [r, U, V, sig_rotate (w 1) (w 2) (w 0),
              sig_rotate (w 2) (w 0) (w 1),
              sig_rotate (w 2) (w 3) (w 0),
              sig_rotate (w 3) (w 0) (w 2)] using hb
          change 23 ≤ S + E
          linarith [hsum, hb']
        · let r : Fin 8 → Fin 8 := ![1, 2, 3, 0, 4, 6, 7, 5]
          right
          have hb := ax_dispatch_bound_of_cross_occupied w r (by decide)
            hmin (by simpa [r] using hU') (by simpa [r] using hV')
            (by simpa [r] using hE') (by simpa [r] using hS')
            (by simpa [r] using hEU') (by simpa [r] using hSU')
            (by simpa [r] using hQE) (by simpa [r] using hRE)
            (by simpa [r] using inTriStrict_rotate_maxFree hPS)
            (Or.inr (Or.inl
              (by simpa [r] using inTriStrict_rotate_maxFree hRAXC)))
            (Or.inr (Or.inr
              (by simpa [r] using inTriStrict_rotate_maxFree hPABX)))
          have hb' : 23 ≤ U + V := by
            simpa [r, U, V, sig_rotate (w 1) (w 2) (w 0),
              sig_rotate (w 2) (w 0) (w 1),
              sig_rotate (w 2) (w 3) (w 0),
              sig_rotate (w 3) (w 0) (w 2)] using hb
          change 23 ≤ S + E
          linarith [hsum, hb']
        · let r : Fin 8 → Fin 8 := ![1, 2, 3, 0, 4, 6, 7, 5]
          right
          have hb := axc_dispatch_bound_of_cross_occupied w r (by decide)
            hmin (by simpa [r] using hU') (by simpa [r] using hV')
            (by simpa [r] using hE') (by simpa [r] using hS')
            (by simpa [r] using hEU') (by simpa [r] using hSU')
            (by simpa [r] using inTriStrict_rotate_maxFree hQS)
            (by simpa [r] using inTriStrict_rotate_maxFree hRS)
            (by simpa [r] using hPE)
            (Or.inr (Or.inl
              (by simpa [r] using inTriStrict_rotate_maxFree hRAXC)))
            (Or.inl
              (by simpa [r] using inTriStrict_rotate_maxFree hQABX))
          have hb' : 23 ≤ U + V := by
            simpa [r, U, V, sig_rotate (w 1) (w 2) (w 0),
              sig_rotate (w 2) (w 0) (w 1),
              sig_rotate (w 2) (w 3) (w 0),
              sig_rotate (w 3) (w 0) (w 2)] using hb
          change 23 ≤ S + E
          linarith [hsum, hb']
        · let r : Fin 8 → Fin 8 := ![1, 2, 3, 0, 4, 5, 7, 6]
          right
          have hb := ax_dispatch_bound_of_cross_occupied w r (by decide)
            hmin (by simpa [r] using hU') (by simpa [r] using hV')
            (by simpa [r] using hE') (by simpa [r] using hS')
            (by simpa [r] using hEU') (by simpa [r] using hSU')
            (by simpa [r] using hPE) (by simpa [r] using hRE)
            (by simpa [r] using inTriStrict_rotate_maxFree hQS)
            (Or.inr (Or.inl
              (by simpa [r] using inTriStrict_rotate_maxFree hRAXC)))
            (Or.inl
              (by simpa [r] using inTriStrict_rotate_maxFree hPABX))
          have hb' : 23 ≤ U + V := by
            simpa [r, U, V, sig_rotate (w 1) (w 2) (w 0),
              sig_rotate (w 2) (w 0) (w 1),
              sig_rotate (w 2) (w 3) (w 0),
              sig_rotate (w 3) (w 0) (w 2)] using hb
          change 23 ≤ S + E
          linarith [hsum, hb']
        · let r : Fin 8 → Fin 8 := ![1, 2, 3, 0, 4, 5, 6, 7]
          right
          have hb := ax_dispatch_bound_of_cross_occupied w r (by decide)
            hmin (by simpa [r] using hU') (by simpa [r] using hV')
            (by simpa [r] using hE') (by simpa [r] using hS')
            (by simpa [r] using hEU') (by simpa [r] using hSU')
            (by simpa [r] using hPE) (by simpa [r] using hQE)
            (by simpa [r] using inTriStrict_rotate_maxFree hRS)
            (Or.inr (Or.inr
              (by simpa [r] using inTriStrict_rotate_maxFree hRAXC)))
            (Or.inl
              (by simpa [r] using inTriStrict_rotate_maxFree hPABX))
          have hb' : 23 ≤ U + V := by
            simpa [r, U, V, sig_rotate (w 1) (w 2) (w 0),
              sig_rotate (w 2) (w 0) (w 1),
              sig_rotate (w 2) (w 3) (w 0),
              sig_rotate (w 3) (w 0) (w 2)] using hb
          change 23 ≤ S + E
          linarith [hsum, hb']
        · exact Or.inl (.right hPE hQE hRE)

/-- Symmetric `AXC,AXC,ABX` maximality-free dispatcher. -/
theorem hullFive_axc_major_membership_dispatch_210_maxFree
    (w : Fin 8 → Point)
    (hmin : AllTrianglesMinAreaOne w)
    (hABC : 0 < sig (w 0) (w 1) (w 3))
    (hBXC : 0 < sig (w 1) (w 2) (w 3))
    (hABX : 0 < sig (w 0) (w 1) (w 2))
    (hAXC : 0 < sig (w 0) (w 2) (w 3))
    (hPAXC : InTriStrict (w 5) (w 0) (w 2) (w 3))
    (hQAXC : InTriStrict (w 6) (w 0) (w 2) (w 3))
    (hRABX : InTriStrict (w 7) (w 0) (w 1) (w 2)) :
    HullFive300Cell w id ∨
      23 ≤ sig (w 0) (w 1) (w 3) + sig (w 1) (w 2) (w 3) := by
  let q2 : Fin 8 → Fin 8 := ![2, 3, 0, 1, 4, 5, 6, 7]
  let z : Fin 8 → Point := w ∘ q2
  have hzmin : AllTrianglesMinAreaOne z := hmin.comp q2 (by decide)
  have hE' : 0 < sig (w 2) (w 3) (w 1) := by
    rw [sig_rotate (w 2) (w 3) (w 1), sig_rotate (w 3) (w 1) (w 2)]
    exact hBXC
  have hS' : 0 < sig (w 3) (w 0) (w 1) := by
    rw [sig_rotate (w 3) (w 0) (w 1)]
    exact hABC
  have hV' : 0 < sig (w 2) (w 3) (w 0) := by
    rw [sig_rotate (w 2) (w 3) (w 0), sig_rotate (w 3) (w 0) (w 2)]
    exact hAXC
  have hU' : 0 < sig (w 2) (w 0) (w 1) := by
    rw [sig_rotate (w 2) (w 0) (w 1)]
    exact hABX
  have hd := hullFive_ax_major_membership_dispatch_210_maxFree z hzmin
    (by simpa [z, q2] using hE') (by simpa [z, q2] using hS')
    (by simpa [z, q2] using hV') (by simpa [z, q2] using hU')
    (by simpa [z, q2] using inTriStrict_rotate_maxFree hPAXC)
    (by simpa [z, q2] using inTriStrict_rotate_maxFree hQAXC)
    (by simpa [z, q2] using inTriStrict_rotate2_maxFree hRABX)
  rcases hd with hcell | hbound
  · left
    cases hcell with
    | central hP hQ hR =>
        exact .right
          (by simpa [z, q2] using inTriStrict_rotate2_maxFree hP)
          (by simpa [z, q2] using inTriStrict_rotate2_maxFree hQ)
          (by simpa [z, q2] using inTriStrict_rotate2_maxFree hR)
    | right hP hQ hR =>
        exact .central
          (by simpa [z, q2] using inTriStrict_rotate_maxFree hP)
          (by simpa [z, q2] using inTriStrict_rotate_maxFree hQ)
          (by simpa [z, q2] using inTriStrict_rotate_maxFree hR)
  · right
    simpa [z, q2, add_comm, sig_rotate (w 2) (w 3) (w 1),
      sig_rotate (w 3) (w 1) (w 2),
      sig_rotate (w 3) (w 0) (w 1)] using hbound

/-! ## Reindexed APIs for the survivor adapter -/

theorem hullFive_ax_major_membership_dispatch_210_maxFree_reindex
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)))
    (hPABX : InTriStrict (v (e 5))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hQABX : InTriStrict (v (e 6))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hRAXC : InTriStrict (v (e 7))
      (v (e 0)) (v (e 2)) (v (e 3))) :
    HullFive300Cell v e ∨
      23 ≤ sig (v (e 0)) (v (e 1)) (v (e 3)) +
        sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  let w : Fin 8 → Point := v ∘ e
  have hwmin : AllTrianglesMinAreaOne w := hmin.comp e he
  have hd := hullFive_ax_major_membership_dispatch_210_maxFree w hwmin
    (by simpa [w] using hABC) (by simpa [w] using hBXC)
    (by simpa [w] using hABX) (by simpa [w] using hAXC)
    (by simpa [w] using hPABX) (by simpa [w] using hQABX)
    (by simpa [w] using hRAXC)
  rcases hd with hcell | hbound
  · left
    cases hcell with
    | central hP hQ hR =>
        exact .central (by simpa [w] using hP)
          (by simpa [w] using hQ) (by simpa [w] using hR)
    | right hP hQ hR =>
        exact .right (by simpa [w] using hP)
          (by simpa [w] using hQ) (by simpa [w] using hR)
  · exact Or.inr (by simpa [w] using hbound)

theorem hullFive_axc_major_membership_dispatch_210_maxFree_reindex
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)))
    (hPAXC : InTriStrict (v (e 5))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hQAXC : InTriStrict (v (e 6))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hRABX : InTriStrict (v (e 7))
      (v (e 0)) (v (e 1)) (v (e 2))) :
    HullFive300Cell v e ∨
      23 ≤ sig (v (e 0)) (v (e 1)) (v (e 3)) +
        sig (v (e 1)) (v (e 2)) (v (e 3)) := by
  let w : Fin 8 → Point := v ∘ e
  have hwmin : AllTrianglesMinAreaOne w := hmin.comp e he
  have hd := hullFive_axc_major_membership_dispatch_210_maxFree w hwmin
    (by simpa [w] using hABC) (by simpa [w] using hBXC)
    (by simpa [w] using hABX) (by simpa [w] using hAXC)
    (by simpa [w] using hPAXC) (by simpa [w] using hQAXC)
    (by simpa [w] using hRABX)
  rcases hd with hcell | hbound
  · left
    cases hcell with
    | central hP hQ hR =>
        exact .central (by simpa [w] using hP)
          (by simpa [w] using hQ) (by simpa [w] using hR)
    | right hP hQ hR =>
        exact .right (by simpa [w] using hP)
          (by simpa [w] using hQ) (by simpa [w] using hR)
  · exact Or.inr (by simpa [w] using hbound)

/-! ## End-zero pentagon corollaries

For an end-zero fan, `e 4` is the fifth hull vertex beyond the occupied
quadrilateral `e 0,e 1,e 2,e 3`.  Its remaining positive fan triangle has
area at least two, so the quadrilateral bound `23` becomes the desired
pentagon fan bound `25`. -/

/-- End-zero pentagon bound when two selected points occupy the first
quadrilateral fan cell. -/
theorem hullFive_endZero_ax_major_dispatch_210_maxFree_reindex
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)))
    (hACD : 0 < sig (v (e 0)) (v (e 3)) (v (e 4)))
    (hPABX : InTriStrict (v (e 5))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hQABX : InTriStrict (v (e 6))
      (v (e 0)) (v (e 1)) (v (e 2)))
    (hRAXC : InTriStrict (v (e 7))
      (v (e 0)) (v (e 2)) (v (e 3))) :
    HullFive300Cell v e ∨
      25 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) +
        sig (v (e 0)) (v (e 3)) (v (e 4)) := by
  rcases hullFive_ax_major_membership_dispatch_210_maxFree_reindex
      v e he hmin hABC hBXC hABX hAXC hPABX hQABX hRAXC with
    hcell | hbound
  · exact Or.inl hcell
  · right
    have htailAbs : 2 ≤ |sig (v (e 0)) (v (e 3)) (v (e 4))| :=
      hmin (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
    have htail : 2 ≤ sig (v (e 0)) (v (e 3)) (v (e 4)) := by
      simpa [abs_of_pos hACD] using htailAbs
    have hquad := hullFive_singleton_quadrilateral_sum
      (v (e 0)) (v (e 1)) (v (e 2)) (v (e 3))
    linarith

/-- End-zero pentagon bound when two selected points occupy the second
quadrilateral fan cell. -/
theorem hullFive_endZero_axc_major_dispatch_210_maxFree_reindex
    (v : Fin 8 → Point) (e : Fin 8 → Fin 8)
    (he : Function.Injective e)
    (hmin : AllTrianglesMinAreaOne v)
    (hABC : 0 < sig (v (e 0)) (v (e 1)) (v (e 3)))
    (hBXC : 0 < sig (v (e 1)) (v (e 2)) (v (e 3)))
    (hABX : 0 < sig (v (e 0)) (v (e 1)) (v (e 2)))
    (hAXC : 0 < sig (v (e 0)) (v (e 2)) (v (e 3)))
    (hACD : 0 < sig (v (e 0)) (v (e 3)) (v (e 4)))
    (hPAXC : InTriStrict (v (e 5))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hQAXC : InTriStrict (v (e 6))
      (v (e 0)) (v (e 2)) (v (e 3)))
    (hRABX : InTriStrict (v (e 7))
      (v (e 0)) (v (e 1)) (v (e 2))) :
    HullFive300Cell v e ∨
      25 ≤ sig (v (e 0)) (v (e 1)) (v (e 2)) +
        sig (v (e 0)) (v (e 2)) (v (e 3)) +
        sig (v (e 0)) (v (e 3)) (v (e 4)) := by
  rcases hullFive_axc_major_membership_dispatch_210_maxFree_reindex
      v e he hmin hABC hBXC hABX hAXC hPAXC hQAXC hRABX with
    hcell | hbound
  · exact Or.inl hcell
  · right
    have htailAbs : 2 ≤ |sig (v (e 0)) (v (e 3)) (v (e 4))| :=
      hmin (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
    have htail : 2 ≤ sig (v (e 0)) (v (e 3)) (v (e 4)) := by
      simpa [abs_of_pos hACD] using htailAbs
    have hquad := hullFive_singleton_quadrilateral_sum
      (v (e 0)) (v (e 1)) (v (e 2)) (v (e 3))
    linarith

#print axioms hullFive_ax_major_membership_dispatch_210_maxFree_reindex
#print axioms hullFive_axc_major_membership_dispatch_210_maxFree_reindex
#print axioms hullFive_endZero_ax_major_dispatch_210_maxFree_reindex
#print axioms hullFive_endZero_axc_major_dispatch_210_maxFree_reindex

end Heilbronn8.TriHull
