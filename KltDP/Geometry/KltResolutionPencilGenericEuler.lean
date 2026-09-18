import KltDP.Geometry.KltResolutionConnectedPencil
import KltDP.Geometry.SquareZeroFamilyEuler

/-! The original minimal-resolution square-zero divisor constructs the
same proper, flat, surjective pencil with geometrically connected fibers
and original generic-fiber Euler characteristic one. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.IsMinimalResolution

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {ρ : S.toScheme ⟶ X.toScheme}

local instance pencilEulerSourceIntegral : IsIntegral S.toScheme := S.integral
local instance pencilEulerTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

theorem exists_flat_connectedPencil_genericEuler_one_of_kltDelPezzo
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
      IsProper g ∧ Surjective g ∧ Flat g ∧ IsIso g.c ∧
      Nonempty ((pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
          cartierDivisorModule S.toScheme F) ∧
      (∀ (l : Type u) [Field l] (q : Spec (CommRingCat.of l) ⟶ projectiveSpace k 1),
        ConnectedSpace (pullback g q : Scheme.{u})) ∧
      eulerCharacteristic (g.fiberToSpecResidueField (genericPoint (projectiveSpace k 1)))
        (SheafOfModules.unit (g.fiber (genericPoint (projectiveSpace k 1))).ringCatSheaf) = 1 := by
  obtain ⟨g, hg, hgproper, hgsurj, hgc, ⟨e⟩, hconnected⟩ :=
    hmin.exists_geometricallyConnectedPencil_of_nef_squareZero_of_kltDelPezzo
      hDP hrank p hp K eK F hF hFF hKF
  letI : IsProper g := hgproper
  letI : Surjective g := hgsurj
  letI : IsDominant g := ⟨g.surjective.denseRange⟩
  letI : Flat g := DominantRegularCurveFlat.flat_projectiveLine g
  refine ⟨g, hg, hgproper, hgsurj, inferInstance, hgc, ⟨e⟩, hconnected, ?_⟩
  exact S.squareZero_genericFiber_eulerCharacteristic_eq_one hmin.regular K eK F hFF hKF g hg e

end KltDP.Geometry.IsMinimalResolution

#check @KltDP.Geometry.IsMinimalResolution.exists_flat_connectedPencil_genericEuler_one_of_kltDelPezzo
#print axioms KltDP.Geometry.IsMinimalResolution.exists_flat_connectedPencil_genericEuler_one_of_kltDelPezzo
