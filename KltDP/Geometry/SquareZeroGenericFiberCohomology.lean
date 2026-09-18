import KltDP.Geometry.SquareZeroFamilyEuler
import KltDP.Geometry.SurfaceProjectiveLineGenericFiber
import KltDP.Geometry.ProperIntegralCurveEulerOne

/-! The actual square-zero pencil has the native cohomology of a genus-zero
curve on its original generic fiber. The ground field is the original
residue field at the generic point, not an algebraic closure or a chosen
isomorphic field. No rationality or geometric integrality is asserted. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
local instance genericEulerSourceIntegral : IsIntegral X.toScheme := X.integral
local instance genericEulerTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- Actual generic-fiber H0 has dimension one, H1 vanishes, and the
original scalar map identifies its ground field with all global functions. -/
theorem squareZero_genericFiber_cohomology
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2)
    (F : CartierDivisor X.toScheme)
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (π : X.toScheme ⟶ projectiveSpace k 1) [IsProper π] [IsDominant π]
    (hπ : π ≫ projectiveSpaceToSpec k 1 = X.structureMorphism)
    (eF : (pullbackInvertibleSheaf π
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
        cartierDivisorModule X.toScheme F) :
    let f := π.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))
    let M := SheafOfModules.unit
      (π.fiber (genericPoint (projectiveSpace k 1))).ringCatSheaf
    cohomologyDimension f M 0 = 1 ∧ cohomologyDimension f M 1 = 0 ∧
      Subsingleton (H M 1) ∧ Function.Bijective (baseFieldToGlobalSections f) := by
  dsimp only
  obtain ⟨hI, hP, _hR, hD⟩ := SurfaceProjectiveLineGenericFiber.geometry X hX π hπ
  letI : IsIntegral (π.fiber (genericPoint (projectiveSpace k 1))) := hI
  letI : IsProper (π.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))) := hP
  have hχ := X.squareZero_genericFiber_eulerCharacteristic_eq_one
    hX K eK F hFF hKF π hπ eF
  obtain ⟨h0, h1⟩ := ProperIntegralCurveEulerOne.cohomology_dimensions _ hD hχ
  exact ⟨h0, h1, ProperIntegralCurveEulerOne.hOne_subsingleton _ hD hχ,
    ProperIntegralCurveEulerOne.baseFieldToGlobalSections_bijective _ hD hχ⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_genericFiber_cohomology
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_genericFiber_cohomology
