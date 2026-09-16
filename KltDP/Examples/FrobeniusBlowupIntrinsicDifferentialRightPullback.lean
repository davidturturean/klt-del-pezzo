import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport
import KltDP.Examples.FrobeniusBlowupIntrinsicDifferentialWedge
import KltDP.Examples.FrobeniusBlowupDifferentialRightExceptionalSheaf

/-!
# The actual complementary Rees differential pullback retains its Jacobian

The original blowdown map induces the original intrinsic exterior differential
map. Its actual pullback-unit image of the original plane coordinate wedge
has minus the original exceptional equation as coefficient. The target structure
map is transported only by the proved equality of the original structure
morphisms. No map normalization or canonical-divisor formula is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusBlowupIntrinsicDifferentialRightPullback

open KltDP.Geometry KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.AffineDifferentialExteriorNormalization
open FrobeniusBlowupContact FrobeniusBlowupSmooth
open FrobeniusBlowupDifferentialRightMap FrobeniusBlowupDifferentialRightExceptionalSheaf
open FrobeniusBlowupDifferentialOverlap
open FrobeniusBlowupIntrinsicDifferentialWedge

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The original complementary blowdown chart commutes with its original field map. -/
theorem rightStructure_comp :
    planeRightMap (k := k) ≫ planeStructure (k := k) = rightStructure (k := k) := by
  change Spec.map (CommRingCat.ofHom (rightBaseMap (k := k))) ≫
    Spec.map (CommRingCat.ofHom (planeConstants (k := k))) =
      Spec.map (CommRingCat.ofHom (chartConstants (centerV (k := k))))
  rw [← Spec.map_comp]
  rfl

abbrev planeExterior : (Spec (CommRingCat.of (planeRing k))).Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf (planeStructure (k := k))) 2

abbrev rightExterior : (Spec (CommRingCat.of (rightChartRing k))).Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf (rightStructure (k := k))) 2

/-- The original intrinsic exterior map of the original complementary blowdown chart. -/
def rightMap :
    (schemeModulePullback (planeRightMap (k := k))).obj (planeExterior (k := k)) ⟶
      rightExterior (k := k) :=
  SchemeKaehlerExteriorPullbackTransport.map (planeStructure (k := k))
    (planeRightMap (k := k)) (rightStructure (k := k)) (rightStructure_comp (k := k)) 2

/-- For every pair of original plane functions, the unit wedge maps to the
wedge of the original chart images in the original intrinsic exterior sheaf. -/
theorem rightMap_unit_wedge_D (v : Fin 2 → planeRing k) :
    (rightMap (k := k)).val.app (op ⊤)
        (((schemeModulePullbackPushforwardAdjunction (planeRightMap (k := k))).unit.app
          (planeExterior (k := k))).val.app (op ⊤)
            (SchemeExteriorPower.wedge (baseRingSheaf (planeStructure (k := k))) 2 ⊤
              (fun i => (baseRingDerivation (planeStructure (k := k))).d
                (StructureSheaf.toOpen (planeRing k) ⊤ (v i))))) =
      SchemeExteriorPower.wedge (baseRingSheaf (rightStructure (k := k))) 2 ⊤
        (fun i => (baseRingDerivation (rightStructure (k := k))).d
          (StructureSheaf.toOpen (rightChartRing k) ⊤ (rightBaseMap (v i)))) :=
  SchemeKaehlerExteriorPullbackTransport.map_unit_wedge_toOpen
    (planeStructure (k := k)) (rightBaseMap (k := k)) (rightStructure (k := k))
    (rightStructure_comp (k := k)) 2 v

/-- Infer the original chart normalization before comparing its named public type. -/
private def rightMap_unit_coordinate_proof (k : Type u) [Field k] :=
  (SchemeKaehlerExteriorPullbackTransport.map_unit_pair_toOpen
    (planeStructure (k := k)) (rightBaseMap (k := k)) (rightStructure (k := k))
    (rightStructure_comp (k := k)) uCoord vCoord).trans
      (rightPulledPlaneWedge_eq (k := k) ⊤)

/-- The actual intrinsic differential pullback has the original exceptional
coefficient on the original ordered plane coordinate wedge. -/
theorem rightMap_unit_coordinate :
    (rightMap (k := k)).val.app (op ⊤)
        (((schemeModulePullbackPushforwardAdjunction (planeRightMap (k := k))).unit.app
          (planeExterior (k := k))).val.app (op ⊤)
            (differentialWedge (planeStructure (k := k)) ⊤
              (StructureSheaf.toOpen (planeRing k) ⊤ uCoord)
              (StructureSheaf.toOpen (planeRing k) ⊤ vCoord))) =
      (-StructureSheaf.toOpen (rightChartRing k) ⊤ rightV) •
        rightCoordinateWedge (k := k) ⊤ :=
  rightMap_unit_coordinate_proof k

end KltDP.Examples.FrobeniusBlowupIntrinsicDifferentialRightPullback
