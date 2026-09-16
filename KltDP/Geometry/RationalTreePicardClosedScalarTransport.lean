import KltDP.Geometry.RationalTreePicardClosedComponentFrame

/-!
# Original quotient scalars and geometric component frames

The standard A-action on A/I comes from the submodule quotient. The
change-of-rings functor instead uses Module.compHom along the original
quotient map. We prove their identity-carrier linear equivalence using
the actual algebra scalar law, and transport it through the original
tensor product. The second identity-carrier equivalence checks the
restricted scalar action on extension of scalars on pure tensors.

These comparisons connect the original tensor branch M ⊗ A/I in the
closed-union matching diagram to the actual geometric component frame.
Every original pure tensor keeps its numerator and its module element.
No equality of the two scalar structures is presumed by elaboration.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- Identity on the original quotient carrier, with its two A-actions
related by the original quotient algebra scalar law. -/
def quotientCompHomEquiv :
    (A ⧸ I) ≃ₗ[A]
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (ModuleCat.of (A ⧸ I) (A ⧸ I)) where
  toFun := fun b => b
  invFun := fun b => b
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' a b := by
    change (a • b : A ⧸ I) = Ideal.Quotient.mk I a * b
    simpa only [Ideal.Quotient.algebraMap_eq] using (Algebra.smul_def a b)

@[simp]
theorem quotientCompHomEquiv_apply (b : A ⧸ I) :
    quotientCompHomEquiv A I b = b := rfl

variable (M : ModuleCat.{u} A)

/-- The original tensor carrier with quotient-map scalars has the same
A-action as the actual restriction of the scalar-extension module. -/
def quotientTensorRestrictionEquiv :
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
      (ModuleCat.of (A ⧸ I) (A ⧸ I))) ⊗[A] M ≃ₗ[A]
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero]
    | tmul b m => rfl
    | add x y hx hy => simpa only [smul_add] using congrArg₂ (· + ·) hx hy

/-- The original branch tensor is the original restricted extension
module, with the quotient action transported explicitly. -/
def closedBranchTensorEquiv :
    M ⊗[A] (A ⧸ I) ≃ₗ[A]
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M) :=
  (TensorProduct.comm A M (A ⧸ I)).trans
    ((TensorProduct.congr (quotientCompHomEquiv A I) (LinearEquiv.refl A M)).trans
      (quotientTensorRestrictionEquiv A I M))

/-- The transport retains the two original factors of every pure tensor. -/
@[simp]
theorem closedBranchTensorEquiv_tmul (m : M) (b : A ⧸ I) :
    closedBranchTensorEquiv A I M (m ⊗ₜ[A] b) =
      (b ⊗ₜ[A, Ideal.Quotient.mk I] m) := rfl

variable (L : InvertibleSheaf (Spec (CommRingCat.of A)))
  (frame : (schemeModulePullback (closedComponentInclusion A I)).obj L.obj ≅
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)

/-- The actual component frame now trivializes the original branch
tensor used in the closed-union matching diagram. -/
def closedBranchFrameEquiv :
    AffineModuleTilde.sectionModule L.obj ⊤ ⊗[A] (A ⧸ I) ≃ₗ[A] A ⧸ I :=
  (closedBranchTensorEquiv A I (AffineModuleTilde.sectionModule L.obj ⊤)).trans
    (((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapIso
      (closedComponentFrameModuleIso A I L frame)).toLinearEquiv.trans
        (quotientCompHomEquiv A I).symm)

/-- The resulting scalar is the original module frame applied to the
original extension tensor; no basis or numerator is replaced. -/
theorem closedBranchFrameEquiv_tmul
    (m : AffineModuleTilde.sectionModule L.obj ⊤) (b : A ⧸ I) :
    closedBranchFrameEquiv A I L frame (m ⊗ₜ[A] b) =
      (closedComponentFrameModuleIso A I L frame).hom
        (b ⊗ₜ[A, Ideal.Quotient.mk I] m) := rfl

end KltDP.Geometry.RationalTreePicard
