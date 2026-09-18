import KltDP.Geometry.ProjectiveLineCurveProduct
import KltDP.Geometry.HartshorneRuledConditional
import KltDP.Geometry.ProjectiveLineAffineVanishingProved
import KltDP.Geometry.SurfaceEulerStructureSheaf
import KltDP.Geometry.ProjectivePlane
import KltDP.Examples.FrobeniusRulingClassPairing

/-!
# Structure cohomology of the original projective-line product

The entire reviewed ruled-surface genus theorem remains explicit. Its
inputs are produced from the original product projection, section and
scheme-theoretic closed fibers. The base projective line's genus is
already proved by affine vanishing. No product cohomology value is supplied.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u

namespace KltDP.Geometry.ProjectiveLineProductStructureCohomologyConditional

open KltDP.Examples.FrobeniusStageZeroProjective
open KltDP.Examples.FrobeniusRulingClassPairing

variable (hGenus :
∀ (k : Type u) [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
  [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
  (hCdim : topologicalKrullDim C = 1)
  (hCreg : ∀ y : C, RegularPoint C y)
  (π : X.toScheme ⟶ C)
  (hbase : π ≫ c = X.structureMorphism)
  (hsurj : Function.Surjective π.base)
  (hfib : ∀ y : C, IsClosed ({y} : Set C) →
    ∃ e : π.fiber y ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 =
        π.fiberι y ≫ X.structureMorphism)
  (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C),
  (eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) - 1 =
    -(CurveCanonical.genus c : ℤ)) ∧
  (cohomologyDimension X.structureMorphism
      (relativeDifferentialExterior X.structureMorphism 2) 0 = 0) ∧
  (cohomologyDimension X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 =
    CurveCanonical.genus c)
)

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- All actual points of the original projective line are regular. -/
theorem line_regular (y : projectiveSpace k 1) :
    RegularPoint (projectiveSpace k 1) y := by
  letI : IsNoetherianRing ((projectiveSpace k 1).presheaf.stalk y) :=
    (projectiveSpace_isProjectiveOverField k 1).isNoetherianRing_stalk y
  apply regularPoint_of_normal_of_ringKrullDim_le_one
    (projectiveSpace k 1) (projectiveSpace_isNormalScheme k 1) y
  exact (ringKrullDim_stalk_le_topologicalKrullDim (projectiveSpace k 1) y).trans_eq
    (by simpa using projectiveSpace_topologicalKrullDim k 1)

include hGenus in
/-- The original product has chi(O)=1, pg=0, h1(O)=0 and h2(O)=0. -/
theorem values :
    let X := projectiveProductSurface (k := k)
    eulerCharacteristic X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) = 1 ∧
      cohomologyDimension X.structureMorphism
        (relativeDifferentialExterior X.structureMorphism 2) 0 = 0 ∧
      cohomologyDimension X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 = 0 ∧
      cohomologyDimension X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 2 = 0 := by
  let X := projectiveProductSurface (k := k)
  let c := projectiveSpaceToSpec k 1
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : LocallyOfFiniteType c :=
    (projectiveSpace_isProjectiveOverField k 1).locallyOfFiniteType
  letI : IsProper c := (projectiveSpace_isProjectiveOverField k 1).isProper
  have hdim : topologicalKrullDim (projectiveSpace k 1) = 1 := by
    simpa using projectiveSpace_topologicalKrullDim k 1
  have h := hGenus k X baseRegular (projectiveSpace k 1) c hdim line_regular
    (ProjectiveLineCurveProduct.projection c)
    (ProjectiveLineCurveProduct.projection_over_base c)
    (ProjectiveLineCurveProduct.projection_surjective c).surj
    (fun y hy => ⟨ProjectiveLineCurveProduct.fiberIso c y hy,
      ProjectiveLineCurveProduct.fiberIso_over_base c y hy⟩)
    (ProjectiveLineCurveProduct.sectionMap c)
    (ProjectiveLineCurveProduct.sectionMap_projection c)
  have hg : CurveCanonical.genus c = 0 :=
    AffineCohomologyPort.genus_projectiveLine_eq_zero k
  rw [hg] at h
  have hchi : eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) = 1 := by
    exact sub_eq_zero.mp (by simpa using h.1)
  have heuler := normalProjectiveSurface_eulerCharacteristic_unit X
  change eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) =
    1 - (cohomologyDimension X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 : ℤ) +
      (cohomologyDimension X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 2 : ℤ) at heuler
  refine ⟨hchi, h.2.1, h.2.2, ?_⟩
  rw [hchi, h.2.2] at heuler
  have htwo : (cohomologyDimension X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 2 : ℤ) = 0 := by
    omega
  exact_mod_cast htwo

end KltDP.Geometry.ProjectiveLineProductStructureCohomologyConditional

#check @KltDP.Geometry.ProjectiveLineProductStructureCohomologyConditional.values
#print axioms KltDP.Geometry.ProjectiveLineProductStructureCohomologyConditional.values
