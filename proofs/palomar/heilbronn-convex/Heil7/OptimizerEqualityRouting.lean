import Heil7.CanonicalHullClassification7

/-!
# Equality routing for seven-point optimizers

This module contains the lossless bookkeeping needed to classify equality in
the canonical seven-point upper bound.  The only mathematical inputs are the
strict forms of the four non-six hull cases.  Once those are supplied, exact
area equality forces a relabeling with six hull vertices and one interior
point.  No affine normalization is used by this first reduction.
-/

set_option linter.style.header false

namespace HeilbronnChallenge.N7Upper

/-- Strict versions of precisely the hull cases which cannot contain an
optimizer.  Hull size six is deliberately absent. -/
structure StrictNonSixHullCaseBounds : Prop where
  h3 : ∀ (v : Configuration7), 0 < minTri v → HullCCW v 3 →
    (∀ p : Fin 7, 3 ≤ (p : ℕ) → InHullN v 3 p) →
    9 * minTri v < fanArea v 3
  h4 : ∀ (v : Configuration7), 0 < minTri v → HullCCW v 4 →
    (∀ p : Fin 7, 4 ≤ (p : ℕ) → InHullN v 4 p) →
    9 * minTri v < fanArea v 4
  h5 : ∀ (v : Configuration7), 0 < minTri v → HullCCW v 5 →
    (∀ p : Fin 7, 5 ≤ (p : ℕ) → InHullN v 5 p) →
    9 * minTri v < fanArea v 5
  h7 : ∀ (v : Configuration7), 0 < minTri v → HullCCW v 7 →
    9 * minTri v < fanArea v 7

/-- Dispatch a strict non-six hull bound at a classified hull size. -/
theorem StrictNonSixHullCaseBounds.labelled
    (S : StrictNonSixHullCaseBounds) (v : Configuration7)
    (h : ℕ) (hlo : 3 ≤ h) (hhi : h ≤ 7) (hne : h ≠ 6)
    (hm : 0 < minTri v) (hccw : HullCCW v h)
    (hin : ∀ p : Fin 7, h ≤ (p : ℕ) → InHullN v h p) :
    9 * minTri v < fanArea v h := by
  interval_cases h
  · exact S.h3 v hm hccw hin
  · exact S.h4 v hm hccw hin
  · exact S.h5 v hm hccw hin
  · exact (hne rfl).elim
  · exact S.h7 v hm hccw

/-- The complete geometric and equality packet left after excluding hull
sizes three, four, five, and seven. -/
structure HullSixEqualityData (w : Configuration7) : Prop where
  minTri_pos : 0 < minTri w
  hullCCW : HullCCW w 6
  tail_inHull : ∀ p : Fin 7, 6 ≤ (p : ℕ) → InHullN w 6 p
  area_eq_fan : HullBridge.doubledHullArea w = fanArea w 6
  bound_eq : 9 * minTri w = fanArea w 6

private def identityPosAffine : PosAffine where
  a := 1
  b := 0
  c := 0
  d := 1
  tx := 0
  ty := 0
  det_pos := by norm_num

/-- A pure relabeling is a positive-affine gauge equivalence (with identity
affine map). -/
theorem gaugeEquivalent_relabel (v : Configuration7)
    (σ : Equiv.Perm (Fin 7)) :
    GaugeEquivalent v (v ∘ σ) := by
  refine ⟨σ, identityPosAffine, ?_⟩
  funext i
  simp [identityPosAffine, PosAffine.map, Function.comp_apply]

/-- Exact positive-area equality can occur only in the hull-six case.  The
returned equality is expressed after the classifier's lossless relabeling. -/
theorem areaEquality_relabel_hullSix
    (S : StrictNonSixHullCaseBounds) (v : Configuration7)
    (hm : 0 < minTri v)
    (heq : 9 * minTri v = HullBridge.doubledHullArea v) :
    ∃ σ : Equiv.Perm (Fin 7),
      GaugeEquivalent v (v ∘ σ) ∧
        HullSixEqualityData (v ∘ σ) := by
  rcases hullClassified_all v with
    hzero | ⟨h, σ, hlo, hhi, hccw, hin, harea⟩
  · exact (hm.ne' hzero).elim
  · have hmw : 0 < minTri (v ∘ σ) := by
      rw [minTri_relabel v σ]
      exact hm
    have heqw : 9 * minTri (v ∘ σ) = fanArea (v ∘ σ) h := by
      calc
        9 * minTri (v ∘ σ) = 9 * minTri v := by
          rw [minTri_relabel v σ]
        _ = HullBridge.doubledHullArea v := heq
        _ = fanArea (v ∘ σ) h := harea
    have hh : h = 6 := by
      by_contra hne
      have hlt := S.labelled (v ∘ σ) h hlo hhi hne hmw hccw hin
      exact (ne_of_lt hlt) heqw
    subst h
    have hareaw : HullBridge.doubledHullArea (v ∘ σ) =
        fanArea (v ∘ σ) 6 :=
      (doubledHullArea_relabel v σ).trans harea
    exact ⟨σ, gaugeEquivalent_relabel v σ,
      ⟨hmw, hccw, hin, hareaw, heqw⟩⟩

/-- Generic second-stage seam: any complete classification of the hull-six
equality packet automatically becomes an exhaustive gauge classification of
all positive-area equality configurations. -/
theorem extremizer_gauge_h6Packet
    (S : StrictNonSixHullCaseBounds)
    (Packet : Configuration7 → Prop)
    (complete6 : ∀ w, HullSixEqualityData w →
      ∃ u, GaugeEquivalent w u ∧ Packet u)
    (v : Configuration7)
    (hm : 0 < minTri v)
    (heq : 9 * minTri v = HullBridge.doubledHullArea v) :
    ∃ u, GaugeEquivalent v u ∧ Packet u := by
  rcases areaEquality_relabel_hullSix S v hm heq with
    ⟨σ, _, hdata⟩
  rcases complete6 (v ∘ σ) hdata with
    ⟨u, ⟨τ, T, hu⟩, hpacket⟩
  refine ⟨u, ?_, hpacket⟩
  refine ⟨τ.trans σ, T, ?_⟩
  rw [hu]
  funext i
  rfl

end HeilbronnChallenge.N7Upper
