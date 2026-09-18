import KltDP.Geometry.SquareZeroCompletePencilMorphismEulerOne
import KltDP.Geometry.ProjectiveConstantDegree
import KltDP.Geometry.NonconstantProperCurveSurjective
import KltDP.Geometry.ProperGenericPointSurjective
import KltDP.Geometry.ProjectivePlane
import KltDP.Geometry.LocallyOfFiniteTypeNoetherian

/-! The same actual square-zero pencil map is proper and surjective
when chi(O)=1. A constant map would contradict the original line's
proved two-dimensional section space. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance surjectiveEulerOnePencilIntegral : IsIntegral X.toScheme := X.integral
local instance surjectiveEulerOnePencilTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

include eK in
/-- The supplied original pencil map itself is proper, generic-point
preserving, dominant and surjective. Its pullback comparison is retained. -/
theorem squareZero_completePencilMorphism_properties_of_euler_one
    (hchi : eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) = 1)
    (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (g : X.toScheme ⟶ projectiveSpace k 1)
    (hg : g ≫ projectiveSpaceToSpec k 1 = X.structureMorphism)
    (e : (pullbackInvertibleSheaf g
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
        cartierDivisorModule X.toScheme F) :
    IsProper g ∧ GenericPointPreserving g ∧ IsDominant g ∧ Surjective g := by
  letI : NoetherianSpace (projectiveSpace k 1) :=
    noetherianSpace_of_locallyOfFiniteType_quasiCompact_spec (projectiveSpaceToSpec k 1)
  letI : IsProper g := by
    letI : IsProper (g ≫ projectiveSpaceToSpec k 1) := by rw [hg]; infer_instance
    exact IsProper.of_comp_of_isSeparated g (projectiveSpaceToSpec k 1)
  have hunit : cohomologyDimension X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 0 = 1 := by
    rw [cohomologyDimension_zero_eq_finrank_sections]
    exact globalSections_finrank_one X.structureMorphism
  have htwo := (X.squareZero_hZero_eq_two_and_hOne_eq_zero_of_euler_one
    hX K eK hchi F hF hFF hKF).1
  have hn : ¬ ∃ p : Spec (CommRingCat.of k) ⟶ projectiveSpace k 1,
      X.structureMorphism ≫ p = g := by
    rintro ⟨p, rfl⟩
    let eUnit : cartierDivisorModule X.toScheme F ≅
        _root_.SheafOfModules.unit X.toScheme.ringCatSheaf :=
      e.symm ≪≫ ProjectiveConstantDegree.pullbackDegreeOneUnitIso X.structureMorphism p
    have hdim := finrank_eq_of_iso X.structureMorphism 0 eUnit
    change cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme F) 0 =
      cohomologyDimension X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 0 at hdim
    rw [htwo, hunit] at hdim
    omega
  have hdim : topologicalKrullDim (projectiveSpace k 1) ≤ 1 :=
    (projectiveSpace_topologicalKrullDim k 1).le
  letI : GenericPointPreserving g :=
    ProperNonconstantCurve.genericPointPreserving_of_not_factors_through_structure
      X.structureMorphism (projectiveSpaceToSpec k 1) g hg hdim hn
  letI : IsDominant g := NonconstantProperCurveSurjective.dominant_of_genericPointPreserving g
  letI : Surjective g := surjective_of_proper_genericPointPreserving g
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_completePencilMorphism_properties_of_euler_one
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_completePencilMorphism_properties_of_euler_one
