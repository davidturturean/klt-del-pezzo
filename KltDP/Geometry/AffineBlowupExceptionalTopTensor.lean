import KltDP.Geometry.AffineBlowupTopDifferential
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import KltDP.Geometry.SchemeModulePullbackTensorInclusion
import KltDP.Geometry.InvertibleTensorExact

/-!
# The original exceptional top tensor on an actual affine blowup

The target is the original exceptional kernel tensored with the original
intrinsic top-differential sheaf. Smooth relative dimension two proves that
its actual inclusion is monic. No factorization or canonical formula is input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.AffineBlowupTopDifferential

open AffineBlowup

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem structureTensorInclusion_mono {X : Scheme.{u}} {J : X.Modules}
    (i : J ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) [Mono i]
    (L : InvertibleSheaf X) : Mono (schemeStructureTensorInclusion i L.obj) := by
  letI := L.tensorRight_preservesFiniteLimits
  haveI : Mono (i ≫ (SchemeModuleStructureUnit.iso X).hom) := inferInstance
  change Mono ((tensorRight L.obj).map (i ≫ (SchemeModuleStructureUnit.iso X).hom) ≫
    (λ_ L.obj).hom)
  infer_instance

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] (I : Ideal R)

/-- The literal original global exceptional kernel tensor. -/
abbrev exceptionalTensor : (scheme I).Modules := exceptionalIdealModule I ⊗ topSheaf k R I

/-- Tensor the actual original kernel inclusion with the actual top sheaf. -/
def exceptionalInclusion : exceptionalTensor k R I ⟶ topSheaf k R I :=
  schemeStructureTensorInclusion (schemeKernelIdealι (exceptionalι I)) (topSheaf k R I)

variable [IsSmoothOfRelativeDimension 2 (structureMap k R I)]

/-- The original intrinsic top sheaf is invertible by actual smoothness. -/
def topLine : InvertibleSheaf (scheme I) :=
  ⟨topSheaf k R I,
    SmoothCanonicalExteriorComparison.relativeDifferentialExterior_isInvertible
      (structureMap k R I)⟩

/-- Monicity follows from the actual ideal inclusion and the derived invertible top sheaf. -/
theorem exceptionalInclusion_mono : Mono (exceptionalInclusion k R I) := by
  letI : Mono (schemeKernelIdealι (exceptionalι I)) := by
    unfold schemeKernelIdealι
    infer_instance
  exact structureTensorInclusion_mono (schemeKernelIdealι (exceptionalι I)) (topLine k R I)

end KltDP.Geometry.AffineBlowupTopDifferential
