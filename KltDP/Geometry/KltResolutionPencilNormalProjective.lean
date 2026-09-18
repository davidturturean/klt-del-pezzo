import KltDP.Geometry.KltResolutionPencilGenusZero
import KltDP.Geometry.ProjectiveSurfaceFibers
import KltDP.Geometry.MinimalResolutionDebts
import KltDP.Geometry.ClosedPoints
import Mathlib.Algebra.CharP.Algebra

/-! The same original constructed genus-zero pencil has a projective normal
generic fiber over the original residue field. Its characteristic is
inherited through the actual structure-morphism map to that residue field.
No change of field, algebraic closure, smoothness, or new source input is used. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry

/-- The actual structure morphism preserves characteristic in every
original residue field, by injectivity of its map from the ground field. -/
theorem baseToResidueFieldMap_charP
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (σ : Y ⟶ Spec (CommRingCat.of k)) (y : Y)
    (p : ℕ) [CharP k p] : CharP (Y.residueField y) p :=
  charP_of_injective_ringHom (baseToResidueFieldMap σ y).hom.injective p

namespace IsMinimalResolution

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {ρ : S.toScheme ⟶ X.toScheme}

local instance pencilNormalProjectiveSourceIntegral : IsIntegral S.toScheme := S.integral
local instance pencilNormalProjectiveTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- Projectivity, normality and characteristic for the actual generic fiber
of the same original constructed pencil, with all prior geometry retained. -/
theorem exists_connectedPencil_normalProjectiveGenusZero_of_kltDelPezzo
    (hmin : IsMinimalResolution S X ρ) (hDP : IsKltDelPezzo X)
    (hrank : X.picardRank = 1) (p : ℕ) [CharP k p] (hp : 0 < p)
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (F : CartierDivisor S.toScheme)
    (hF : Positivity.IsNef S.structureMorphism
      (cartierDivisorInvertibleSheaf S.toScheme F))
    (hFF : S.intersectionPairing hmin.regular F F = 0)
    (hKF : S.intersectionPairing hmin.regular K F = -2) :
    ∃ g : S.toScheme ⟶ projectiveSpace k 1,
      g ≫ projectiveSpaceToSpec k 1 = S.structureMorphism ∧
      IsProper g ∧ Surjective g ∧ IsDominant g ∧ Flat g ∧ IsIso g.c ∧
      Nonempty ((pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
          cartierDivisorModule S.toScheme F) ∧
      (∀ (l : Type u) [Field l] (q : Spec (CommRingCat.of l) ⟶ projectiveSpace k 1),
        ConnectedSpace (pullback g q : Scheme.{u})) ∧
      (let C := g.fiber (genericPoint (projectiveSpace k 1))
       let f := g.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))
       let M := SheafOfModules.unit C.ringCatSheaf
       CharP ((projectiveSpace k 1).residueField (genericPoint (projectiveSpace k 1))) p ∧
         IsIntegral C ∧ IsNormalScheme C ∧ IsProjectiveOverField f ∧ IsProper f ∧
         (∀ x : C, RegularPoint C x) ∧ topologicalKrullDim C = 1 ∧
         eulerCharacteristic f M = 1 ∧ cohomologyDimension f M 0 = 1 ∧
         cohomologyDimension f M 1 = 0 ∧ Subsingleton (H M 1) ∧
         IsIso ((Scheme.ΓSpecIso ((projectiveSpace k 1).residueField
           (genericPoint (projectiveSpace k 1)))).inv ≫ f.appTop) ∧
         Function.Bijective (baseFieldToGlobalSections f)) := by
  obtain ⟨g, hg, hproper, hsurj, hdom, hflat, hc, ⟨e⟩, hconnected,
      hI, hP, hR, hdim, hχ, h0, h1, hvan, hscalar, hbij⟩ :=
    hmin.exists_connectedPencil_genericGenusZero_of_kltDelPezzo
      hDP hrank p hp K eK F hF hFF hKF
  refine ⟨g, hg, hproper, hsurj, hdom, hflat, hc, ⟨e⟩, hconnected, ?_⟩
  exact ⟨baseToResidueFieldMap_charP (projectiveSpaceToSpec k 1) _ p,
    hI, isNormalScheme_of_regularPoint hR,
    S.projectiveLine_genericFiber_isProjective g hg, hP,
    hR, hdim, hχ, h0, h1, hvan, hscalar, hbij⟩

end IsMinimalResolution
end KltDP.Geometry

#print axioms KltDP.Geometry.baseToResidueFieldMap_charP
#check @KltDP.Geometry.IsMinimalResolution.exists_connectedPencil_normalProjectiveGenusZero_of_kltDelPezzo
#print axioms KltDP.Geometry.IsMinimalResolution.exists_connectedPencil_normalProjectiveGenusZero_of_kltDelPezzo
