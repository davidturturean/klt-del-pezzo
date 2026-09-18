import KltDP.Geometry.KltResolutionPencilGenericEuler
import KltDP.Geometry.SquareZeroGenericFiberCohomology
import KltDP.Geometry.SurfaceGenericFiberEulerDimension

/-! The original minimal resolution constructs a single pencil whose
original generic fiber is a regular proper integral curve of dimension
one and genus zero. All scalar and cohomology statements concern the
original residue field and structure module. Geometric connectedness is
retained for every field-valued fiber of the same constructed map.
Smoothness and a projective-line isomorphism of its generic fiber remain
separate conclusions; neither is assumed or asserted here. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.IsMinimalResolution

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {ρ : S.toScheme ⟶ X.toScheme}

local instance pencilGenusZeroSourceIntegral : IsIntegral S.toScheme := S.integral
local instance pencilGenusZeroTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- The actual constructed pencil, its original fiber geometry and native
cohomology, with no supplied pencil, genus, or global-scalar identification. -/
theorem exists_connectedPencil_genericGenusZero_of_kltDelPezzo
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
       IsIntegral C ∧ IsProper f ∧ (∀ x : C, RegularPoint C x) ∧
         topologicalKrullDim C = 1 ∧ eulerCharacteristic f M = 1 ∧
         cohomologyDimension f M 0 = 1 ∧ cohomologyDimension f M 1 = 0 ∧
         Subsingleton (H M 1) ∧
         IsIso ((Scheme.ΓSpecIso ((projectiveSpace k 1).residueField
           (genericPoint (projectiveSpace k 1)))).inv ≫ f.appTop) ∧
         Function.Bijective (baseFieldToGlobalSections f)) := by
  obtain ⟨g, hg, hproper, hsurj, hflat, hc, ⟨e⟩, hconnected, hχ⟩ :=
    hmin.exists_flat_connectedPencil_genericEuler_one_of_kltDelPezzo
      hDP hrank p hp K eK F hF hFF hKF
  letI : IsProper g := hproper
  letI : Surjective g := hsurj
  letI : IsDominant g := ⟨g.surjective.denseRange⟩
  obtain ⟨hI, hP, hR, hle⟩ :=
    SurfaceProjectiveLineGenericFiber.geometry S hmin.regular g hg
  letI : IsIntegral (g.fiber (genericPoint (projectiveSpace k 1))) := hI
  letI : IsProper (g.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))) := hP
  have hdim := SurfaceGenericFiberDimensionOne.dimension_eq_one_of_eulerCharacteristic_eq_one
    S g hχ
  obtain ⟨h0, h1, hvan, hbij⟩ :=
    S.squareZero_genericFiber_cohomology hmin.regular K eK F hFF hKF g hg e
  have hscalar := ProperIntegralCurveEulerOne.globalScalar_isIso
    (g.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))) hle hχ
  refine ⟨g, hg, hproper, hsurj, inferInstance, hflat, hc, ⟨e⟩, hconnected, ?_⟩
  exact ⟨hI, hP, hR, hdim, hχ, h0, h1, hvan, hscalar, hbij⟩

end KltDP.Geometry.IsMinimalResolution

#check @KltDP.Geometry.IsMinimalResolution.exists_connectedPencil_genericGenusZero_of_kltDelPezzo
#print axioms KltDP.Geometry.IsMinimalResolution.exists_connectedPencil_genericGenusZero_of_kltDelPezzo
