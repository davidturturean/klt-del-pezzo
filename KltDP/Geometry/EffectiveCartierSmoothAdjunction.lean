import KltDP.Geometry.GluedSmoothCurveAdjunction
import KltDP.Geometry.GluedAdjunctionCartierTarget

/-!
# Adjunction for the original smooth effective Cartier curve

The actual chart maps glue under the original smoothness hypotheses. Their
normal factor is the restriction of the original O(E), so the resulting
isomorphism has the original ambient canonical-Cartier tensor as its target.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u
namespace KltDP.Geometry.EffectiveCartierSmoothAdjunction

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsSmoothOfRelativeDimension 2 f]
  (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
  [IsSmoothOfRelativeDimension 1
    ((effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo ≫ f)]

/-- The original smooth effective Cartier curve has the original adjunction isomorphism.
The local regularity hypothesis is derived from the actual Cartier equations. -/
def iso :
    SchemeKaehlerSheaf.baseRingSheaf
        ((effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo ≫ f) ≅
      (schemeModulePullback (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo).obj
        ((SmoothSurfaceKaehlerAtlas.canonicalSheafOfSmoothSurface f).obj ⊗
          cartierDivisorModule X E) :=
  GluedSmoothCurveAdjunction.iso f (effectiveCartierIdealDataOfRegularEquations X E hE)
      (effectiveCartierIdealDataOfRegularEquations_regular X E hE) ≪≫
    GluedAdjunctionCartierTarget.iso f E hE

end KltDP.Geometry.EffectiveCartierSmoothAdjunction
