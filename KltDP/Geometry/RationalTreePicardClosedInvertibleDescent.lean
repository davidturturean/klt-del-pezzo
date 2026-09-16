import KltDP.Geometry.RationalTreePicardClosedUnionSheaf
import KltDP.Geometry.AffineInvertibleGlobalSectionsFlat
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Reconstruction of an actual invertible sheaf across an affine closed cover

The original quotient difference for I,J is tensored with the original
global-section module. Mathlib's flat tensor-kernel equivalence identifies
its kernel with the tensor of A/(I∩J). Flatness for an actual invertible
sheaf is derived from its original local rank-one charts by the existing
affine theorem, rather than supplied as a descent hypothesis.

If I∩J=0, the existing affine counit and tilde-kernel comparisons identify
the original invertible sheaf with this actual matching kernel. The map
on pure tensors retains the original pair of quotient restrictions.
Comparing the two tensor branches with geometric component restrictions,
and transporting global component frames through the nodal charts, remain
the next adapters; the rational-tree Picard endpoint is not asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (A : Type u) [CommRing A] (I J : Ideal A)
  (M : Type u) [AddCommGroup M] [Module A M]

/-- Tensor the original closed-branch difference with the original module. -/
def closedTensorDifference :
    M ⊗[A] ((A ⧸ I) × (A ⧸ J)) →ₗ[A] M ⊗[A] (A ⧸ I ⊔ J) :=
  TensorProduct.AlgebraTensorModule.lTensor A M (closedUnionDifference A I J)

/-- The pinned flat tensor-kernel theorem applies directly to the actual
closed-union kernel; no tensor exactness is reproved. -/
def closedFlatTensorKernelEquiv [Module.Flat A M] :
    M ⊗[A] (A ⧸ I ⊓ J) ≃ₗ[A] LinearMap.ker (closedTensorDifference A I J M) :=
  (TensorProduct.congr (LinearEquiv.refl A M) (closedUnionKernelEquiv A I J)).trans
    (LinearMap.tensorKerEquiv A M (closedUnionDifference A I J))

/-- The comparison uses precisely the original two quotient restrictions. -/
theorem closedFlatTensorKernelEquiv_tmul [Module.Flat A M]
    (m : M) (a : A ⧸ I ⊓ J) :
    (closedFlatTensorKernelEquiv A I J M (m ⊗ₜ[A] a) :
        M ⊗[A] ((A ⧸ I) × (A ⧸ J))) =
      m ⊗ₜ[A] closedUnionPairLinear A I J a := by
  simp only [closedFlatTensorKernelEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    LinearMap.tensorKerEquiv_apply, LinearMap.tensorKer_tmul] <;> rfl

/-- A scheme-theoretic closed cover recovers the original flat module
from its actual tensor matching kernel. -/
def closedCoverFlatKernelEquiv [Module.Flat A M] (h : I ⊓ J = ⊥) :
    M ≃ₗ[A] LinearMap.ker (closedTensorDifference A I J M) :=
  (TensorProduct.AlgebraTensorModule.rid A A M).symm.trans
    ((TensorProduct.congr (LinearEquiv.refl A M)
      ((Ideal.quotientEquivAlgOfEq A h).trans
        (AlgEquiv.quotientBot A A)).toLinearEquiv.symm).trans
      (closedFlatTensorKernelEquiv A I J M))

/-- The original tensor difference as a morphism of actual A-modules. -/
def closedTensorDifferenceHom :
    ModuleCat.of A (M ⊗[A] ((A ⧸ I) × (A ⧸ J))) ⟶
      ModuleCat.of A (M ⊗[A] (A ⧸ I ⊔ J)) :=
  ModuleCat.ofHom (closedTensorDifference A I J M)

/-- The original flat module is the categorical tensor matching kernel. -/
def closedCoverFlatModuleKernelIso [Module.Flat A M] (h : I ⊓ J = ⊥) :
    ModuleCat.of A M ≅ kernel (closedTensorDifferenceHom A I J M) :=
  (closedCoverFlatKernelEquiv A I J M h).toModuleIso ≪≫
    (ModuleCat.kernelIsoKer (closedTensorDifferenceHom A I J M)).symm

/-- The original tilde of a flat module is the whole-sheaf matching
kernel for the original tensor quotient difference. -/
def closedCoverFlatSheafKernelIso [Module.Flat A M] (h : I ⊓ J = ⊥) :
    (ModuleCat.of A M).tilde ≅
      kernel (AffineModuleTilde.map (closedTensorDifferenceHom A I J M)) :=
  AffineModuleTilde.mapIso (closedCoverFlatModuleKernelIso A I J M h) ≪≫
    AffineModuleTilde.kernelIso (closedTensorDifferenceHom A I J M)

/-- An arbitrary actual affine invertible sheaf is reconstructed by its
original closed-branch tensor matching kernel. Flatness and affine
reconstruction both follow from its actual local trivializations. -/
def invertibleClosedCoverKernelIso
    (L : InvertibleSheaf (Spec (CommRingCat.of A))) (h : I ⊓ J = ⊥) :
    L.obj ≅ kernel (AffineModuleTilde.map
      (closedTensorDifferenceHom A I J (AffineModuleTilde.sectionModule L.obj ⊤))) := by
  letI := AffineModuleTilde.invertibleGlobalSections_flat L
  exact (AffineModuleTilde.invertibleCounitIso L).symm ≪≫
    closedCoverFlatSheafKernelIso A I J (AffineModuleTilde.sectionModule L.obj ⊤) h

end KltDP.Geometry.RationalTreePicard
