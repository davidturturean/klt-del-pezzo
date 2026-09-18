import KltDP.Geometry.SelectedPrimeRamificationMaps
import KltDP.Geometry.PrimeCurveClosedImage
import KltDP.Geometry.OriginalCartierQuadraticSurface
import KltDP.Geometry.QuadraticOriginalGenericPoint
import KltDP.Geometry.PrimeCurveCartierProjectionCases

/-!
# Actual ramification prime curves on the original quadratic surface

The actual selected closed immersions define prime curves on the same
original normal projective cover. Their original source identifications
commute with the original surface projection and the base field.
The existing Cartier projection theorem therefore computes the
intersection of every such curve with an actual pulled-back divisor.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance selectedRamificationPrimeCurvesSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance selectedRamificationPrimeCurvesMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : HasRegularCartierEquations S.toScheme E) (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))

local notation "A" => effectiveCartierQuadraticAtlas S.toScheme E hE L e
local notation "CoverSurface" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne

include hIJ

/-- The actual image of each selected ramification immersion is a prime curve on the same cover. -/
def selectedRamificationPrimeCurve (C : {C : S.PrimeCurve // C ∈ N}) : (CoverSurface).PrimeCurve :=
  C.val.closedImage (T := CoverSurface) (S.selectedPrimeRamificationMap N E hE L e hIJ C)

@[simp] theorem coe_selectedRamificationPrimeCurve (C : {C : S.PrimeCurve // C ∈ N}) :
    (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C : Set (CoverSurface).toScheme) =
      Set.range (S.selectedPrimeRamificationMap N E hE L e hIJ C).base := rfl

/-- Its reduced prime-curve scheme is the original selected curve scheme. -/
def selectedRamificationPrimeCurveSourceIso (C : {C : S.PrimeCurve // C ∈ N}) :
    (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C).toScheme ≅ C.val.toScheme :=
  C.val.closedImageSourceIso (T := CoverSurface) (S.selectedPrimeRamificationMap N E hE L e hIJ C)

@[reassoc] theorem selectedRamificationPrimeCurveSourceIso_hom_toBase
    (C : {C : S.PrimeCurve // C ∈ N}) :
    (S.selectedRamificationPrimeCurveSourceIso N E hE L e h2 hred hne hIJ C).hom ≫
        C.val.inclusion =
      (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C).inclusion ≫
        (A).morphism := by
  rw [← S.selectedPrimeRamificationMap_toBase N E hE L e hIJ C, ← Category.assoc]
  exact congrArg (fun g => g ≫ (A).morphism)
    (C.val.closedImageSourceIso_hom_map (T := CoverSurface)
      (S.selectedPrimeRamificationMap N E hE L e hIJ C))

@[reassoc] theorem selectedRamificationPrimeCurveSourceIso_hom_toSpec
    (C : {C : S.PrimeCurve // C ∈ N}) :
    (S.selectedRamificationPrimeCurveSourceIso N E hE L e h2 hred hne hIJ C).hom ≫ C.val.toSpec =
      (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C).toSpec := by
  change _ ≫ C.val.inclusion ≫ S.structureMorphism = _ ≫ ((A).morphism ≫ S.structureMorphism)
  rw [← Category.assoc, selectedRamificationPrimeCurveSourceIso_hom_toBase, Category.assoc]

/-- The actual projection identifies pulled-back intersections with the original curve's degree. -/
theorem selectedRamificationPrimeCurve_intersection_pullback
    (C : {C : S.PrimeCurve // C ∈ N})
    (F : CartierDivisor S.toScheme) (hF : HasRegularCartierEquations S.toScheme F) :
    letI : IsIntegral (A).scheme := (CoverSurface).integral
    letI : GenericPointPreserving (A).morphism := (A).morphism_genericPointPreserving
    (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C).intersectionNumber
      (pullbackDivisor (A).morphism F hF) = C.val.intersectionNumber F := by
  letI : IsIntegral (A).scheme := (CoverSurface).integral
  letI : GenericPointPreserving (A).morphism := (A).morphism_genericPointPreserving
  exact PrimeCurveCartierProjectionCases.intersectionNumber_pullbackDivisor_eq_of_isoFactor
    (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C) C.val (A).morphism
    (S.selectedRamificationPrimeCurveSourceIso N E hE L e h2 hred hne hIJ C).hom
    (S.selectedRamificationPrimeCurveSourceIso_hom_toBase N E hE L e h2 hred hne hIJ C).symm
    (S.selectedRamificationPrimeCurveSourceIso_hom_toSpec N E hE L e h2 hred hne hIJ C) F hF

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.selectedRamificationPrimeCurve_intersection_pullback

