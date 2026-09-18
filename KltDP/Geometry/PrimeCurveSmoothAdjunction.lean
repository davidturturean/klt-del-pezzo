import KltDP.Geometry.EffectiveCartierSmoothAdjunction
import KltDP.Geometry.AdjunctionFormulaSeed

/-!
# The original adjunction interface for an actual smooth prime curve

The accepted Cartier ideal of the original prime curve equals its original
vanishing ideal as ideal-sheaf data. This equality specializes the proved
effective-Cartier adjunction to the original curve, inclusion, cotangent
sheaf, ambient canonical line, and Cartier divisor.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u
namespace KltDP.Geometry.PrimeCurveSmoothAdjunction

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 X.structureMorphism]
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  (C : X.PrimeCurve) [IsSmoothOfRelativeDimension 1 C.toSpec]

/-- The original adjunction-isomorphism premise is proved for the actual smooth prime curve. -/
theorem adjunctionIso : AdjunctionSeed.AdjunctionIso X hregular
    (SmoothSurfaceKaehlerAtlas.canonicalSheafOfSmoothSurface X.structureMorphism) C := by
  let E := X.primeCurveCartier hregular C
  let hE := X.primeCurveCartier_hasRegularEquations hregular C
  have hI : effectiveCartierIdealDataOfRegularEquations X.toScheme E hE =
      C.vanishingIdeal := X.primeCurveCartier_idealData_eq_vanishingIdeal hregular C
  letI : IsSmoothOfRelativeDimension 1
      ((effectiveCartierIdealDataOfRegularEquations X.toScheme E hE).gluedTo ≫
        X.structureMorphism) := by
    rw [hI]
    exact inferInstanceAs (IsSmoothOfRelativeDimension 1 C.toSpec)
  change Nonempty
    (SchemeKaehlerSheaf.baseRingSheaf (C.vanishingIdeal.gluedTo ≫ X.structureMorphism) ≅
      (schemeModulePullback C.vanishingIdeal.gluedTo).obj
        ((SmoothSurfaceKaehlerAtlas.canonicalSheafOfSmoothSurface X.structureMorphism).obj ⊗
          cartierDivisorModule X.toScheme E))
  rw [← hI]
  exact ⟨EffectiveCartierSmoothAdjunction.iso X.structureMorphism E hE⟩

end KltDP.Geometry.PrimeCurveSmoothAdjunction
