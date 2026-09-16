import KltDP.Geometry.AffineDifferentialExteriorNormalization
import KltDP.Examples.FrobeniusBlowupDifferentialRightMap

/-!
# Original Rees Jacobians in the intrinsic differential exterior sheaf

The two actual Rees equations give the determinant coefficients `u` and `-v`
inside the intrinsic exterior sheaves, on every original open. The original
affine Kähler comparison preserves the ordered coordinate wedges as wedges
of native differential tilde sections. No arbitrary line isomorphism or
determinant-compatibility premise is used.

This does not yet identify the intrinsic differential pullback map with the
native top-differential tilde map or descend the canonical Cartier formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusBlowupIntrinsicDifferentialWedge

open KltDP.Geometry KltDP.Geometry.AffineDifferentialExteriorNormalization
open FrobeniusBlowupContact FrobeniusBlowupSmooth
open FrobeniusBlowupDifferentialOverlap FrobeniusBlowupDifferentialRightMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance : Algebra k (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartFieldAlgebra
local instance : Algebra k (rightChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra

/-- The first original chart retains its actual field structure map. -/
abbrev leftStructure : Spec (CommRingCat.of (reesChartRing k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (chartConstants (centerU (k := k))))

/-- The complementary original chart retains its actual field structure map. -/
abbrev rightStructure : Spec (CommRingCat.of (rightChartRing k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (chartConstants (centerV (k := k))))

/-- The first chart's original ordered differential wedge. -/
def leftCoordinateWedge (U : Opens (PrimeSpectrum (reesChartRing k))) :=
  differentialWedge (leftStructure (k := k)) U
    (StructureSheaf.toOpen (reesChartRing k) U chartU)
    (StructureSheaf.toOpen (reesChartRing k) U chartW)

/-- The original plane coordinates, mapped along the actual first Rees map. -/
def leftPulledPlaneWedge (U : Opens (PrimeSpectrum (reesChartRing k))) :=
  differentialWedge (leftStructure (k := k)) U
    (StructureSheaf.toOpen (reesChartRing k) U (baseMap uCoord))
    (StructureSheaf.toOpen (reesChartRing k) U (baseMap vCoord))

/-- The determinant coefficient is the actual first exceptional equation. -/
theorem leftPulledPlaneWedge_eq (U : Opens (PrimeSpectrum (reesChartRing k))) :
    leftPulledPlaneWedge (k := k) U =
      StructureSheaf.toOpen (reesChartRing k) U chartU • leftCoordinateWedge (k := k) U := by
  have hv : StructureSheaf.toOpen (reesChartRing k) U (baseMap vCoord) =
      StructureSheaf.toOpen (reesChartRing k) U chartU *
        StructureSheaf.toOpen (reesChartRing k) U chartW :=
    (congrArg (StructureSheaf.toOpen (reesChartRing k) U)
      (chartU_mul_chartW (k := k)).symm).trans
        ((StructureSheaf.toOpen (reesChartRing k) U).hom.map_mul chartU chartW)
  exact (congrArg (fun b => differentialWedge (leftStructure (k := k)) U
    (StructureSheaf.toOpen (reesChartRing k) U chartU) b) hv).trans
      (differentialWedge_mul (leftStructure (k := k)) U
        (StructureSheaf.toOpen (reesChartRing k) U chartU)
        (StructureSheaf.toOpen (reesChartRing k) U chartW))

/-- The second chart retains the native order `(v,u/v)`. -/
def rightCoordinateWedge (U : Opens (PrimeSpectrum (rightChartRing k))) :=
  differentialWedge (rightStructure (k := k)) U
    (StructureSheaf.toOpen (rightChartRing k) U rightV)
    (StructureSheaf.toOpen (rightChartRing k) U rightS)

/-- The original plane coordinates, mapped along the actual second Rees map. -/
def rightPulledPlaneWedge (U : Opens (PrimeSpectrum (rightChartRing k))) :=
  differentialWedge (rightStructure (k := k)) U
    (StructureSheaf.toOpen (rightChartRing k) U (rightBaseMap uCoord))
    (StructureSheaf.toOpen (rightChartRing k) U (rightBaseMap vCoord))

/-- Coordinate order gives minus the actual second exceptional equation. -/
theorem rightPulledPlaneWedge_eq (U : Opens (PrimeSpectrum (rightChartRing k))) :
    rightPulledPlaneWedge (k := k) U =
      (-StructureSheaf.toOpen (rightChartRing k) U rightV) •
        rightCoordinateWedge (k := k) U := by
  have hu : StructureSheaf.toOpen (rightChartRing k) U (rightBaseMap uCoord) =
      StructureSheaf.toOpen (rightChartRing k) U rightV *
        StructureSheaf.toOpen (rightChartRing k) U rightS :=
    (congrArg (StructureSheaf.toOpen (rightChartRing k) U)
      (rightV_mul_rightS (k := k)).symm).trans
        ((StructureSheaf.toOpen (rightChartRing k) U).hom.map_mul rightV rightS)
  refine (congrArg (fun a => differentialWedge (rightStructure (k := k)) U a
    (StructureSheaf.toOpen (rightChartRing k) U rightV)) hu).trans ?_
  refine (differentialWedge_swap (rightStructure (k := k)) U
    (StructureSheaf.toOpen (rightChartRing k) U rightV *
      StructureSheaf.toOpen (rightChartRing k) U rightS)
    (StructureSheaf.toOpen (rightChartRing k) U rightV)).trans ?_
  exact (congrArg Neg.neg (differentialWedge_mul (rightStructure (k := k)) U
    (StructureSheaf.toOpen (rightChartRing k) U rightV)
    (StructureSheaf.toOpen (rightChartRing k) U rightS))).trans
      (neg_smul (StructureSheaf.toOpen (rightChartRing k) U rightV)
        (rightCoordinateWedge (k := k) U)).symm

/-- The plane comparison retains exactly the original ordered `du ∧ dv`. -/
theorem planeCoordinateWedge_native (U : Opens (PrimeSpectrum (planeRing k))) :
    (exteriorIso k (planeRing k) 2).hom.val.app (op U)
        (differentialWedge (planeStructure (k := k)) U
          (StructureSheaf.toOpen (planeRing k) U uCoord)
          (StructureSheaf.toOpen (planeRing k) U vCoord)) =
      SchemeExteriorPower.wedge (AffineKaehlerTildeDerivation.differentialModule
        k (planeRing k)).tilde 2 U
        (fun i => ModuleCat.Tilde.toOpen (AffineKaehlerTildeDerivation.differentialModule
          k (planeRing k)) U (KaehlerDifferential.D k (planeRing k) (![uCoord, vCoord] i))) :=
  exteriorIso_differentialWedge_toOpen k (planeRing k) U uCoord vCoord

/-- The actual first chart comparison preserves its original native wedge. -/
theorem leftCoordinateWedge_native (U : Opens (PrimeSpectrum (reesChartRing k))) :
    (exteriorIso k (reesChartRing k) 2).hom.val.app (op U)
        (leftCoordinateWedge (k := k) U) =
      SchemeExteriorPower.wedge (AffineKaehlerTildeDerivation.differentialModule
        k (reesChartRing k)).tilde 2 U
        (fun i => ModuleCat.Tilde.toOpen (AffineKaehlerTildeDerivation.differentialModule
          k (reesChartRing k)) U (KaehlerDifferential.D k (reesChartRing k)
            (![chartU, chartW] i))) :=
  exteriorIso_differentialWedge_toOpen k (reesChartRing k) U chartU chartW

/-- The actual second chart comparison preserves native order `(v,u/v)`. -/
theorem rightCoordinateWedge_native (U : Opens (PrimeSpectrum (rightChartRing k))) :
    (exteriorIso k (rightChartRing k) 2).hom.val.app (op U)
        (rightCoordinateWedge (k := k) U) =
      SchemeExteriorPower.wedge (AffineKaehlerTildeDerivation.differentialModule
        k (rightChartRing k)).tilde 2 U
        (fun i => ModuleCat.Tilde.toOpen (AffineKaehlerTildeDerivation.differentialModule
          k (rightChartRing k)) U (KaehlerDifferential.D k (rightChartRing k)
            (![rightV, rightS] i))) :=
  exteriorIso_differentialWedge_toOpen k (rightChartRing k) U rightV rightS

end KltDP.Examples.FrobeniusBlowupIntrinsicDifferentialWedge
