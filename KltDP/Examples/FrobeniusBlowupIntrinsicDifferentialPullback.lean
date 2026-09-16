import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport
import KltDP.Examples.FrobeniusBlowupIntrinsicDifferentialWedge
import KltDP.Examples.FrobeniusBlowupDifferentialExceptionalSheaf

/-!
# The actual first Rees differential pullback retains its Jacobian

The original blowdown map induces the original intrinsic exterior differential
map. Its actual pullback-unit image of the original plane coordinate wedge
has the original exceptional equation as coefficient. The target structure
map is transported only by the proved equality of the original structure
morphisms. No map normalization or canonical-divisor formula is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusBlowupIntrinsicDifferentialPullback

open KltDP.Geometry KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.AffineDifferentialExteriorNormalization
open FrobeniusBlowupContact FrobeniusBlowupSmooth
open FrobeniusBlowupDifferentialMap FrobeniusBlowupDifferentialPullbackComp
open FrobeniusBlowupIntrinsicDifferentialWedge

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The original first blowdown chart commutes with its original field map. -/
theorem leftStructure_comp :
    planeChartMap (k := k) ≫ planeStructure (k := k) = leftStructure (k := k) := by
  change Spec.map (CommRingCat.ofHom (baseMap (k := k))) ≫
    Spec.map (CommRingCat.ofHom (planeConstants (k := k))) =
      Spec.map (CommRingCat.ofHom (chartConstants (centerU (k := k))))
  rw [← Spec.map_comp]
  rfl

abbrev planeExterior : (Spec (CommRingCat.of (planeRing k))).Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf (planeStructure (k := k))) 2

abbrev leftExterior : (Spec (CommRingCat.of (reesChartRing k))).Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf (leftStructure (k := k))) 2

/-- The original intrinsic exterior map of the original first blowdown chart. -/
def leftMap :
    (schemeModulePullback (planeChartMap (k := k))).obj (planeExterior (k := k)) ⟶
      leftExterior (k := k) :=
  SchemeKaehlerExteriorPullbackTransport.map (planeStructure (k := k))
    (planeChartMap (k := k)) (leftStructure (k := k)) (leftStructure_comp (k := k)) 2

/-- For every pair of original plane functions, the unit wedge maps to the
wedge of the original chart images in the original intrinsic exterior sheaf. -/
theorem leftMap_unit_wedge_D (v : Fin 2 → planeRing k) :
    (leftMap (k := k)).val.app (op ⊤)
        (((schemeModulePullbackPushforwardAdjunction (planeChartMap (k := k))).unit.app
          (planeExterior (k := k))).val.app (op ⊤)
            (SchemeExteriorPower.wedge (baseRingSheaf (planeStructure (k := k))) 2 ⊤
              (fun i => (baseRingDerivation (planeStructure (k := k))).d
                (StructureSheaf.toOpen (planeRing k) ⊤ (v i))))) =
      SchemeExteriorPower.wedge (baseRingSheaf (leftStructure (k := k))) 2 ⊤
        (fun i => (baseRingDerivation (leftStructure (k := k))).d
          (StructureSheaf.toOpen (reesChartRing k) ⊤ (baseMap (v i)))) :=
  SchemeKaehlerExteriorPullbackTransport.map_unit_wedge_toOpen
    (planeStructure (k := k)) (baseMap (k := k)) (leftStructure (k := k))
    (leftStructure_comp (k := k)) 2 v

/-- Infer the original chart normalization before comparing its named public type. -/
private def leftMap_unit_coordinate_proof (k : Type u) [Field k] :=
  (SchemeKaehlerExteriorPullbackTransport.map_unit_pair_toOpen
    (planeStructure (k := k)) (baseMap (k := k)) (leftStructure (k := k))
    (leftStructure_comp (k := k)) uCoord vCoord).trans
      (leftPulledPlaneWedge_eq (k := k) ⊤)

/-- The actual intrinsic differential pullback has the original exceptional
coefficient on the original ordered plane coordinate wedge. -/
theorem leftMap_unit_coordinate :
    (leftMap (k := k)).val.app (op ⊤)
        (((schemeModulePullbackPushforwardAdjunction (planeChartMap (k := k))).unit.app
          (planeExterior (k := k))).val.app (op ⊤)
            (differentialWedge (planeStructure (k := k)) ⊤
              (StructureSheaf.toOpen (planeRing k) ⊤ uCoord)
              (StructureSheaf.toOpen (planeRing k) ⊤ vCoord))) =
      StructureSheaf.toOpen (reesChartRing k) ⊤ chartU •
        leftCoordinateWedge (k := k) ⊤ :=
  leftMap_unit_coordinate_proof k

end KltDP.Examples.FrobeniusBlowupIntrinsicDifferentialPullback
