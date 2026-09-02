import Heil6.HullPacketBounds
import Heil6.QuadrilateralGeometryRigidity
import Heil6.HexagonGauge
import Solution.N6
import Solution.AffineDefs

set_option linter.style.header false

/-!
# Equality routing and pairwise uniqueness at n = 6

The three- and five-hull packets are strict, the four-hull equality case is
ruled out by the proved same-half equality extractor, and the six-hull packet is rigid.
Consequently every unit-area optimizer is gauge-equivalent to `hex6`, and
any two optimizers are gauge-equivalent to each other.
-/

namespace N6Scratch
namespace N6UniqueCore

open HeilbronnChallenge

theorem optimal_gauge_hex6_of_sameHalfEqualityExtractor
    (extractSame : QuadrilateralGeometryRigidity.SameHalfEqualityExtractor)
    (v : Fin 6 → ℝ × ℝ)
    (hvolume : MeasureTheory.volume (convexHull ℝ (Set.range v)) = 1)
    (hscore : minTri v = 2 * v6) :
    GaugeEquivalent hex6 v := by
  let m := minTri v
  have hm : 0 < m := by
    dsimp [m]
    rw [hscore, v6]
    norm_num
  have h6m : 6 * m = 2 := by
    dsimp [m]
    rw [hscore, v6]
    norm_num
  have hmin : FiniteHullCases.DistinctTriangleFloor v m := by
    intro i j k hij hik hjk
    dsimp [m]
    simpa only [PlanarDet.sig, HeilbronnChallenge.sig] using
      minTri_le_of_distinct v i j k hij hik hjk
  have hgp : FiniteHullCases.NoDegenerateTriple6 v := by
    intro i j k hij hik hjk hzero
    have hf := hmin i j k hij hik hjk
    rw [hzero, abs_zero] at hf
    linarith
  obtain ⟨w, hrel, P⟩ :=
    FiniteHullCases.canonicalHullCase6_complete v hgp
  have hwmin := hrel.floor hmin
  have hareaV := HullBridge.doubledHullArea_of_unit_volume hvolume
  have hareaW : HullBridge.doubledHullArea w = 2 := by
    simpa only [HullBridge.doubledHullArea, hrel.range_eq] using hareaV
  rcases P with P | P | P | P
  · have hstrict := HullPacketBounds.hull3Packet_strict w m hm hwmin P
    exfalso
    linarith
  · have hfan :
        PlanarDet.sig (w 0) (w 1) (w 2) +
            PlanarDet.sig (w 0) (w 2) (w 3) = 6 * m := by
      calc
        _ = HullBridge.doubledHullArea w :=
          (HullPacketBounds.hull4Packet_doubledHullArea w P).symm
        _ = 2 := hareaW
        _ = 6 * m := h6m.symm
    exact False.elim
      (QuadrilateralGeometryRigidity.hull4Packet_six_mul_impossible_of_sameHalfEqualityExtractor
        extractSame w m hm hwmin P hfan)
  · have hstrict := HullPacketBounds.hull5Packet_strict w m hm hwmin P
    exfalso
    linarith
  · have hfan : HexagonGeometryRigidity.fanArea w = 6 * m := by
      calc
        _ = HullBridge.doubledHullArea w :=
          (HullPacketBounds.hull6Packet_doubledHullArea w P).symm
        _ = 2 := hareaW
        _ = 6 * m := h6m.symm
    exact HexagonGauge.relabelledHullSixPacket_gauge
      v w m hm hrel P hwmin hfan

theorem optimal_pairwise_gauge_of_sameHalfEqualityExtractor
    (extractSame : QuadrilateralGeometryRigidity.SameHalfEqualityExtractor)
    (u v : Fin 6 → ℝ × ℝ)
    (huVolume : MeasureTheory.volume (convexHull ℝ (Set.range u)) = 1)
    (huScore : minTri u = 2 * v6)
    (hvVolume : MeasureTheory.volume (convexHull ℝ (Set.range v)) = 1)
    (hvScore : minTri v = 2 * v6) :
    GaugeEquivalent u v := by
  apply HexagonGauge.pairwise_gauge
  · exact optimal_gauge_hex6_of_sameHalfEqualityExtractor
      extractSame u huVolume huScore
  · exact optimal_gauge_hex6_of_sameHalfEqualityExtractor
      extractSame v hvVolume hvScore

theorem witness6_unique_of_sameHalfEqualityExtractor
    (extractSame : QuadrilateralGeometryRigidity.SameHalfEqualityExtractor)
    (v : Fin 6 → ℝ × ℝ)
    (hvolume : MeasureTheory.volume (convexHull ℝ (Set.range v)) = 1)
    (hscore : minTri v = 2 * v6) :
    GaugeEquivalent witness6 v := by
  exact optimal_pairwise_gauge_of_sameHalfEqualityExtractor
    extractSame witness6 v witness6_spec.1 witness6_spec.2 hvolume hscore

/-- Every unit-area six-point optimizer is gauge-equivalent to the explicit
affinely regular model `hex6`. -/
theorem optimal_gauge_hex6
    (v : Fin 6 → ℝ × ℝ)
    (hvolume : MeasureTheory.volume (convexHull ℝ (Set.range v)) = 1)
    (hscore : minTri v = 2 * v6) :
    GaugeEquivalent hex6 v :=
  optimal_gauge_hex6_of_sameHalfEqualityExtractor
    QuadrilateralGeometryRigidity.sameHalfEqualityExtractor
    v hvolume hscore

/-- Any two unit-area six-point optimizers differ by a relabelling and a
positive-determinant affine map. -/
theorem optimal_pairwise_gauge
    (u v : Fin 6 → ℝ × ℝ)
    (huVolume : MeasureTheory.volume (convexHull ℝ (Set.range u)) = 1)
    (huScore : minTri u = 2 * v6)
    (hvVolume : MeasureTheory.volume (convexHull ℝ (Set.range v)) = 1)
    (hvScore : minTri v = 2 * v6) :
    GaugeEquivalent u v :=
  optimal_pairwise_gauge_of_sameHalfEqualityExtractor
    QuadrilateralGeometryRigidity.sameHalfEqualityExtractor
    u v huVolume huScore hvVolume hvScore

/-- The retained witness is unique among unit-area optimizers, up to the
challenge's relabelling/positive-affine gauge. -/
theorem witness6_unique
    (v : Fin 6 → ℝ × ℝ)
    (hvolume : MeasureTheory.volume (convexHull ℝ (Set.range v)) = 1)
    (hscore : minTri v = 2 * v6) :
    GaugeEquivalent witness6 v :=
  witness6_unique_of_sameHalfEqualityExtractor
    QuadrilateralGeometryRigidity.sameHalfEqualityExtractor
    v hvolume hscore

end N6UniqueCore
end N6Scratch

namespace HeilbronnChallenge

/-- Witness-specialized form retained as a convenient downstream helper. -/
theorem heilbronn_convex_six_unique_witness
    (v : Fin 6 → ℝ × ℝ)
    (hvolume : MeasureTheory.volume (convexHull ℝ (Set.range v)) = 1)
    (hscore : minTri v = 2 * v6) :
    GaugeEquivalent witness6 v :=
  N6Scratch.N6UniqueCore.witness6_unique v hvolume hscore

/-- Challenge-facing pairwise uniqueness theorem in the exact unified API. -/
theorem heilbronn_convex_six_unique
    (p q : Fin 6 → ℝ × ℝ)
    (hpvol : MeasureTheory.volume (convexHull ℝ (Set.range p)) = 1)
    (hqvol : MeasureTheory.volume (convexHull ℝ (Set.range q)) = 1)
    (hpopt : minTri p = 2 * v6) (hqopt : minTri q = 2 * v6) :
    AffineEquivalent p q :=
  affineEquivalent_of_gaugeEquivalent
    (N6Scratch.N6UniqueCore.optimal_pairwise_gauge
      p q hpvol hpopt hqvol hqopt)

end HeilbronnChallenge
