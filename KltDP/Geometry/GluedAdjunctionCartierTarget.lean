import KltDP.Geometry.GluedAdjunctionCartierNormal
import KltDP.Geometry.GluedAdjunctionIntrinsicChart
import KltDP.Geometry.SmoothCanonicalExteriorComparison

/-!
# The original canonical-Cartier target of smooth adjunction

The proved ambient canonical comparison and the actual Cartier normal
comparison identify the global adjunction target with the restriction of
the original ambient canonical line tensored with O(E).
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u
namespace KltDP.Geometry.GluedAdjunctionCartierTarget

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsSmoothOfRelativeDimension 2 f]
  (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)

/-- The original global ambient-normal target, expressed in the original canonical line. -/
def iso :
    GluedAdjunctionIntrinsicChart.targetSheaf f
        (effectiveCartierIdealDataOfRegularEquations X E hE) ≅
      (schemeModulePullback (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo).obj
        ((SmoothSurfaceKaehlerAtlas.canonicalSheafOfSmoothSurface f).obj ⊗
          cartierDivisorModule X E) :=
  let I := effectiveCartierIdealDataOfRegularEquations X E hE
  tensorIso
      ((schemeModulePullback I.gluedTo).mapIso
        (SmoothCanonicalExteriorComparison.canonicalSheafOfSmoothSurfaceIsoExterior f).symm)
      (GluedAdjunctionCartierNormal.normalIso X E hE) ≪≫
    (schemeModulePullbackTensorIso I.gluedTo
      (SmoothSurfaceKaehlerAtlas.canonicalSheafOfSmoothSurface f).obj
      (cartierDivisorModule X E)).symm

end KltDP.Geometry.GluedAdjunctionCartierTarget
