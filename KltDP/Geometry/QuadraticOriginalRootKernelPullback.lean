import KltDP.Geometry.QuadraticOriginalSubchart
import KltDP.Geometry.QuadraticRootRegular
import KltDP.Geometry.SchemeKernelExplicitOpenSquare
import KltDP.Geometry.SpecPrincipalIdealTildeKernel

/-!
# The original root ideal on every original quadratic subchart

The original restricted chart is identified with the actual inverse-image
open. Its original root-zero square then identifies the original root
ideal tilde with the pullback of the same global ramification kernel.
The comparison retains both original inclusions.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)
variable {i : ι} {W : X.Opens} (hi : W ≤ D.opens i) (hW : IsAffineOpen W)

/-- The original subchart is the actual inverse-image open subscheme. -/
def framePreimageIso : D.frameChart hi ≅ (D.morphism ⁻¹ᵁ W).toScheme := by
  letI := D.frameGlobalι_isOpenImmersion hi hW
  exact IsOpenImmersion.isoOfRangeEq (D.frameGlobalι hi) (D.morphism ⁻¹ᵁ W).ι
    ((D.range_frameGlobalι hi hW).trans Subtype.range_coe.symm)

@[reassoc]
theorem framePreimageIso_hom_ι :
    (D.framePreimageIso hi hW).hom ≫ (D.morphism ⁻¹ᵁ W).ι = D.frameGlobalι hi := by
  letI := D.frameGlobalι_isOpenImmersion hi hW
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The original local root-zero kernel is the actual pulled global kernel. -/
def rootKernelPullbackIso :
    schemeKernelIdeal (rootZeroι (res X hi (D.sections i))) ≅
      (schemeModulePullback (D.frameGlobalι hi)).obj (schemeKernelIdeal D.rootZeroGlobalι) :=
  SchemeKernelExplicitOpenSquare.iso _ _ _ _ (D.rootZeroFrameGlobalIsPullback hi)
    (D.framePreimageIso hi hW) (D.framePreimageIso_hom_ι hi hW)

theorem rootKernelPullbackIso_inclusion :
    (D.rootKernelPullbackIso hi hW).hom ≫ pulledKernelInclusion D.rootZeroGlobalι (D.frameGlobalι hi) =
      schemeKernelIdealι (rootZeroι (res X hi (D.sections i))) :=
  SchemeKernelExplicitOpenSquare.iso_inclusion _ _ _ _ (D.rootZeroFrameGlobalIsPullback hi)
    (D.framePreimageIso hi hW) (D.framePreimageIso_hom_ι hi hW)

/-- The original regular root ideal tilde is the actual pulled ramification ideal. -/
def rootIdealTildePullbackIso (hs : res X hi (D.sections i) ∈ nonZeroDivisors Γ(X, W)) :
    (ModuleCat.of (CoverAlgebra (res X hi (D.sections i)))
      (rootIdeal (res X hi (D.sections i)))).tilde ≅
        (schemeModulePullback (D.frameGlobalι hi)).obj (schemeKernelIdeal D.rootZeroGlobalι) :=
  SpecPrincipalQuotient.idealTildeKernelIso (root (res X hi (D.sections i)))
    (root_mem_nonZeroDivisors (res X hi (D.sections i)) hs) ≪≫ D.rootKernelPullbackIso hi hW

theorem rootIdealTildePullbackIso_inclusion
    (hs : res X hi (D.sections i) ∈ nonZeroDivisors Γ(X, W)) :
    (D.rootIdealTildePullbackIso hi hW hs).hom ≫
        pulledKernelInclusion D.rootZeroGlobalι (D.frameGlobalι hi) =
      AffinePrincipalIdealTildeFrame.inclusion (rootIdeal (res X hi (D.sections i))) := by
  rw [rootIdealTildePullbackIso, Iso.trans_hom, Category.assoc,
    rootKernelPullbackIso_inclusion]
  exact SpecPrincipalQuotient.idealTildeKernelIso_inclusion
    (root (res X hi (D.sections i))) (root_mem_nonZeroDivisors (res X hi (D.sections i)) hs)

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.rootIdealTildePullbackIso_inclusion
