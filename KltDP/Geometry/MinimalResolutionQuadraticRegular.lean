import KltDP.Geometry.RegularSurfaceSmoothLiteralUse
import KltDP.Geometry.SelectedRamificationDivisorUnion
import KltDP.Geometry.Resolution

/-!
# Regularity of the original cover from an actual minimal resolution

The source smoothness proof is derived with an explicit minimal resolution
argument. The cover regularity conclusions retain the original atlas and
avoid section-dependent smoothness instances in downstream theorem types.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.MinimalResolutionQuadraticRegular

open NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme)

local instance minimalResolutionQuadraticRegularSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance minimalResolutionQuadraticRegularMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- The original minimal resolution is smooth for its original structure morphism. -/
theorem source_isSmooth (hmin : IsMinimalResolution S X π) : IsSmooth S.structureMorphism := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  exact IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism

variable (hmin : IsMinimalResolution S X π)
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)

include hmin h2 hred hne

/-- The same original cover has regular points when its original branch is smooth. -/
theorem cover_regularPoints
    (hsm : IsSmooth
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism)) :
    ∀ y : (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme,
      RegularPoint (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme y := by
  letI : IsSmooth S.structureMorphism := source_isSmooth π hmin
  exact OriginalCartierRamificationSmooth.regularPoints_of_smooth_base_and_branch
    S E hE L e h2 hred hne hsm

/-- An actual disjoint smooth selected branch gives regularity of that same cover. -/
theorem selectedCover_regularPoints (N : Finset S.PrimeCurve)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hcurves : ∀ C ∈ N, IsSmooth C.toSpec) :
    ∀ y : (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme,
      RegularPoint (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme y := by
  letI : IsSmooth S.structureMorphism := source_isSmooth π hmin
  exact S.selectedRamificationCover_regularPoints N E hE L e h2 hred hne hIJ hdisj hcurves

end KltDP.Geometry.MinimalResolutionQuadraticRegular

#print axioms KltDP.Geometry.MinimalResolutionQuadraticRegular.source_isSmooth
#print axioms KltDP.Geometry.MinimalResolutionQuadraticRegular.cover_regularPoints
#print axioms KltDP.Geometry.MinimalResolutionQuadraticRegular.selectedCover_regularPoints
