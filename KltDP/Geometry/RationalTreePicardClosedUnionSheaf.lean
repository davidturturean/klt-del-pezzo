import KltDP.Geometry.RationalTreePicardClosedUnion
import KltDP.Geometry.AffineModuleTildeKernel
import KltDP.Geometry.AffineModuleTildeUnit

/-!
# The actual affine sheaf kernel for two closed pieces

The original quotient factors define the difference map
`A/I × A/J → A/(I+J)` as an A-linear map. Its kernel is the original
`A/(I∩J)` module, proved using common quotient lifts. Applying the existing
kernel comparison of the affine tilde functor yields an isomorphism to
the actual kernel in `(Spec A).Modules`, with its original inclusion.

When the two closed pieces cover `Spec A` scheme-theoretically (`I∩J=0`),
this gives the original structure-sheaf unit. Identifying each quotient
tilde sheaf with the pushforward of the closed piece's structure sheaf is
a separate comparison; no such identification is assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (A : Type u) [CommRing A] (I J : Ideal A)

/-- The original quotient factor, retaining its original A-linear action. -/
def quotientFactorLinear {I J : Ideal A} (h : I ≤ J) : (A ⧸ I) →ₗ[A] A ⧸ J :=
  ({ __ := Ideal.Quotient.factor h
     commutes' := fun _ => rfl } : (A ⧸ I) →ₐ[A] A ⧸ J).toLinearMap

/-- The difference of the two original restrictions to the intersection. -/
def closedUnionDifference : ((A ⧸ I) × (A ⧸ J)) →ₗ[A] A ⧸ I ⊔ J :=
  (quotientFactorLinear A (show I ≤ I ⊔ J from le_sup_left)).comp
      (LinearMap.fst A (A ⧸ I) (A ⧸ J)) -
    (quotientFactorLinear A (show J ≤ I ⊔ J from le_sup_right)).comp
      (LinearMap.snd A (A ⧸ I) (A ⧸ J))

/-- The original two quotient factors from the union quotient. -/
def closedUnionPairLinear : (A ⧸ I ⊓ J) →ₗ[A] (A ⧸ I) × (A ⧸ J) :=
  (quotientFactorLinear A (show I ⊓ J ≤ I from inf_le_left)).prod
    (quotientFactorLinear A (show I ⊓ J ≤ J from inf_le_right))

/-- The original pair map lands in the actual linear kernel of the
difference map. -/
def closedUnionKernelLinear :
    (A ⧸ I ⊓ J) →ₗ[A] LinearMap.ker (closedUnionDifference A I J) :=
  (closedUnionPairLinear A I J).codRestrict _ (by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (I ⊔ J) a - Ideal.Quotient.mk (I ⊔ J) a = 0
    exact sub_self _)

theorem closedUnionKernelLinear_injective :
    Function.Injective (closedUnionKernelLinear A I J) := by
  intro x y h
  apply closedUnionMap_injective A I J
  apply Subtype.ext
  have hpair : closedUnionPairLinear A I J x = closedUnionPairLinear A I J y :=
    congrArg (fun z : LinearMap.ker (closedUnionDifference A I J) => z.val) h
  exact hpair

theorem closedUnionKernelLinear_surjective :
    Function.Surjective (closedUnionKernelLinear A I J) := by
  intro z
  have hz := z.property
  change Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left) z.val.1 -
    Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right) z.val.2 = 0 at hz
  obtain ⟨x, hx, hy⟩ := exists_common_quotient_lift A I J z.val.1 z.val.2
    (sub_eq_zero.mp hz)
  refine ⟨Ideal.Quotient.mk (I ⊓ J) x, ?_⟩
  apply Subtype.ext
  exact Prod.ext hx hy

/-- The common-lift construction identifies the original A-modules. -/
def closedUnionKernelEquiv :
    (A ⧸ I ⊓ J) ≃ₗ[A] LinearMap.ker (closedUnionDifference A I J) :=
  LinearEquiv.ofBijective (closedUnionKernelLinear A I J)
    ⟨closedUnionKernelLinear_injective A I J, closedUnionKernelLinear_surjective A I J⟩

/-- The original difference map as a morphism of actual A-modules. -/
def closedUnionDifferenceHom :
    ModuleCat.of A ((A ⧸ I) × (A ⧸ J)) ⟶ ModuleCat.of A (A ⧸ I ⊔ J) :=
  ModuleCat.ofHom (closedUnionDifference A I J)

/-- The original quotient module is the categorical kernel. -/
def closedUnionModuleKernelIso :
    ModuleCat.of A (A ⧸ I ⊓ J) ≅ kernel (closedUnionDifferenceHom A I J) :=
  (closedUnionKernelEquiv A I J).toModuleIso ≪≫
    (ModuleCat.kernelIsoKer (closedUnionDifferenceHom A I J)).symm

/-- The comparison retains both original quotient components. -/
theorem closedUnionModuleKernelIso_hom_ι :
    (closedUnionModuleKernelIso A I J).hom ≫ kernel.ι (closedUnionDifferenceHom A I J) =
      ModuleCat.ofHom (closedUnionPairLinear A I J) := by
  have hk : (ModuleCat.kernelIsoKer (closedUnionDifferenceHom A I J)).symm.hom ≫
      kernel.ι (closedUnionDifferenceHom A I J) =
        ModuleCat.ofHom (LinearMap.ker (closedUnionDifference A I J)).subtype :=
    ModuleCat.kernelIsoKer_inv_kernel_ι (closedUnionDifferenceHom A I J)
  rw [closedUnionModuleKernelIso, Iso.trans_hom, Category.assoc, hk]
  rfl

/-- The actual tilde of the union quotient is the actual module-sheaf
kernel on the original affine scheme Spec A. -/
def closedUnionSheafKernelIso :
    (ModuleCat.of A (A ⧸ I ⊓ J)).tilde ≅
      kernel (AffineModuleTilde.map (closedUnionDifferenceHom A I J)) :=
  AffineModuleTilde.mapIso (closedUnionModuleKernelIso A I J) ≪≫
    AffineModuleTilde.kernelIso (closedUnionDifferenceHom A I J)

/-- The actual sheaf comparison commutes with the original pair inclusion. -/
theorem closedUnionSheafKernelIso_hom_ι :
    (closedUnionSheafKernelIso A I J).hom ≫
        kernel.ι (AffineModuleTilde.map (closedUnionDifferenceHom A I J)) =
      AffineModuleTilde.map (ModuleCat.ofHom (closedUnionPairLinear A I J)) := by
  have hk : (AffineModuleTilde.kernelIso (closedUnionDifferenceHom A I J)).hom ≫
      kernel.ι (AffineModuleTilde.map (closedUnionDifferenceHom A I J)) =
        AffineModuleTilde.map (kernel.ι (closedUnionDifferenceHom A I J)) :=
    AffineModuleTilde.kernelIso_hom_ι (closedUnionDifferenceHom A I J)
  rw [closedUnionSheafKernelIso, Iso.trans_hom, Category.assoc, hk,
    AffineModuleTilde.mapIso_hom, ← AffineModuleTilde.map_comp,
    closedUnionModuleKernelIso_hom_ι]

/-- A scheme-theoretic closed cover recovers the original structure-sheaf
unit as the actual matching kernel. -/
def closedCoverUnitKernelIso (h : I ⊓ J = ⊥) :
    _root_.SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ≅
      kernel (AffineModuleTilde.map (closedUnionDifferenceHom A I J)) :=
  (AffineModuleTilde.unitIso A).symm ≪≫
    (AffineModuleTilde.linearEquivIso
      (M := ModuleCat.of A (A ⧸ I ⊓ J)) (N := ModuleCat.of A A)
      ((Ideal.quotientEquivAlgOfEq A h).trans (AlgEquiv.quotientBot A A)).toLinearEquiv).symm ≪≫
        closedUnionSheafKernelIso A I J

end KltDP.Geometry.RationalTreePicard
