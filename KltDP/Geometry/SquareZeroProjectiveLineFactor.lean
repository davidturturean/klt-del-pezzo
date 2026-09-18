import KltDP.Geometry.ProjectiveLineIntegralPicardGenerator
import KltDP.Geometry.SquareZeroPicardPrimitive
import KltDP.Geometry.ProjectiveSpaceDegreeOneGlobalGeneration
import KltDP.Geometry.GloballyGeneratedPullback
import KltDP.Geometry.DegreeOneProjectiveLineIsomorphism
import KltDP.Geometry.SchemeKernelIdealIsoTransport

/-! Primitivity forces the actual finite map between the original P1
bases of a factorized square-zero system to have degree one. Its
isomorphism is then produced by the existing actual degree-one theorem. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance degreeOneFactorIntegral : IsIntegral X.toScheme := X.integral
local instance degreeOneFactorLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

include eK in
/-- The actual base-map degree is one; the input is its original
pullback isomorphism to F, not any degree or class-divisibility assertion. -/
theorem squareZero_projectiveLine_factor_degree_eq_one
    (F : CartierDivisor X.toScheme)
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (f : X.toScheme ⟶ projectiveSpace k 1)
    (g : projectiveSpace k 1 ⟶ projectiveSpace k 1)
    (e : (pullbackInvertibleSheaf (f ≫ g)
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
        cartierDivisorModule X.toScheme F) :
    ProjectiveLineDegree.degree k
      (pullbackInvertibleSheaf g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)) = 1 := by
  let H := ProjectiveSpaceDegreeOneSheaf.degreeOne k 1
  let L := pullbackInvertibleSheaf g H
  let d : ℤ := ProjectiveLineDegree.degree k L
  let e' : (pullbackInvertibleSheaf f L).obj ≅ cartierDivisorModule X.toScheme F :=
    (schemeModulePullbackCompIso f g).app H.obj ≪≫ e
  have hpic : schemePicardPullbackHom f L.toPic = cartierPicardClass X.toScheme F :=
    (schemePicardPullbackHom_toPic f L).trans
      (SchemeKernelIdealIsoTransport.toPic_eq_of_iso
        (pullbackInvertibleSheaf f L) (cartierDivisorInvertibleSheaf X.toScheme F) e')
  have hL : L.toPic = H.toPic ^ d :=
    ProjectiveLineIntegralPicardGenerator.toPic_eq_degreeOne_zpow k L
  have hm : (schemePicardPullbackHom f H.toPic) ^ d = cartierPicardClass X.toScheme F := by
    rw [← map_zpow, ← hL]
    exact hpic
  have hdiv : d • Additive.ofMul (schemePicardPullbackHom f H.toPic) =
      cartierPicardHom X.toScheme F := congrArg Additive.ofMul hm
  have hu := X.squareZero_picard_multiplicity_isUnit hX K eK F hFF hKF d
    (Additive.ofMul (schemePicardPullbackHom f H.toPic)) hdiv
  have hd : 0 ≤ d :=
    ProjectiveLineIntegralPicardGenerator.degree_nonneg_of_globallyGenerated k L
      (GloballyGeneratedPullback.isGloballyGenerated g H.obj
        (ProjectiveSpaceDegreeOneSheaf.degreeOne_isGloballyGenerated k 1))
  change d = 1
  rcases Int.isUnit_eq_one_or hu with he | he
  · exact he
  · omega

include eK in
/-- The SAME finite base map is an isomorphism after primitivity computes
its actual degree. No nefness or rationality assumption is needed here. -/
theorem squareZero_projectiveLine_factor_isIso
    (F : CartierDivisor X.toScheme)
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (f : X.toScheme ⟶ projectiveSpace k 1)
    (g : projectiveSpace k 1 ⟶ projectiveSpace k 1)
    [IsFinite g] [GenericPointPreserving g]
    (hg : g ≫ projectiveSpaceToSpec k 1 = projectiveSpaceToSpec k 1)
    (e : (pullbackInvertibleSheaf (f ≫ g)
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
        cartierDivisorModule X.toScheme F) : IsIso g := by
  apply DegreeOneProjectiveLineIsomorphism.isIso_of_degree_one
    (projectiveSpaceToSpec k 1) g hg (ProjectiveLineDegree.dim_le_one k)
  exact X.squareZero_projectiveLine_factor_degree_eq_one hX K eK F hFF hKF f g e

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_projectiveLine_factor_isIso
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_projectiveLine_factor_isIso
