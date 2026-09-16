import KltDP.Geometry.RationalTreePicardClosedScalarTransport
import KltDP.Compatibility.ModuleTransitionUnit

/-!
# Original node-fiber compatibility of two closed-component frames

Each actual geometric component frame is restricted to the original
intersection quotient A/(I+J). The original scalar-extension composition
isomorphism and tensor-unit equivalence give two frames of the SAME
original intersection-fiber module. The existing transition-unit theorem
therefore constructs the unit relating their original coordinates.

The final equation compares the original quotient restrictions of the
original component tensor coordinates, with no compatibility equation
supplied as a hypothesis. At an actual simple rational node the further
geometric identification of A/(I+J) with the ground field is still needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.RationalTreePicard

section ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Equality of the original scalar maps transports a pure tensor without
changing either original factor. -/
theorem extension_eqToIso_tmul {f g : R →+* S} (h : f = g)
    (M : ModuleCat.{u} R) (s : S) (m : M) :
    (eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj M) h)).hom
        (s ⊗ₜ[R, f] m) = s ⊗ₜ[R, g] m := by
  cases h
  rfl

/-- Scalar extension of the original rank-one ring module is the original
target ring module, through the pinned tensor-unit equivalence. -/
def extensionRingModuleIso (f : R →+* S) :
    (ModuleCat.extendScalars f).obj (ModuleCat.of R R) ≅ ModuleCat.of S S := by
  letI := f.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso

/-- The unit comparison evaluates by the original ring homomorphism. -/
theorem extensionRingModuleIso_one_tmul (f : R →+* S) (r : R) :
    (extensionRingModuleIso f).hom ((1 : S) ⊗ₜ[R, f] r) = f r := by
  letI := f.toAlgebra
  change r • (1 : S) = f r
  change f r * 1 = f r
  exact mul_one _

end ScalarExtension

variable (A : Type u) [CommRing A] (I K : Ideal A) (hIK : I ≤ K)
  (M : ModuleCat.{u} A)

/-- The original intersection-fiber module equals scalar extension first
to the component and then to the intersection, using the original quotient
factor identity rather than an assumed comparison. -/
def closedNodeExtensionIso :
    (ModuleCat.extendScalars (Ideal.Quotient.mk K)).obj M ≅
      (ModuleCat.extendScalars (Ideal.Quotient.factor hIK)).obj
        ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M) :=
  eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj M)
    (Ideal.Quotient.factor_comp_mk hIK).symm) ≪≫
      (ModuleCat.extendScalarsComp (Ideal.Quotient.mk I)
        (Ideal.Quotient.factor hIK)).app M

/-- The original module element remains the same through the two stages
of scalar extension. -/
theorem closedNodeExtensionIso_one_tmul (m : M) :
    (closedNodeExtensionIso A I K hIK M).hom
        ((1 : A ⧸ K) ⊗ₜ[A, Ideal.Quotient.mk K] m) =
      (1 : A ⧸ K) ⊗ₜ[A ⧸ I, Ideal.Quotient.factor hIK]
        ((1 : A ⧸ I) ⊗ₜ[A, Ideal.Quotient.mk I] m) := by
  change (ModuleCat.extendScalarsComp (Ideal.Quotient.mk I)
      (Ideal.Quotient.factor hIK)).hom.app M
        ((eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj M)
          (Ideal.Quotient.factor_comp_mk hIK).symm)).hom
            ((1 : A ⧸ K) ⊗ₜ[A, Ideal.Quotient.mk K] m)) = _
  rw [extension_eqToIso_tmul (Ideal.Quotient.factor_comp_mk hIK).symm M 1 m,
    ModuleCat.extendScalarsComp_hom_app_one_tmul]

variable (L : InvertibleSheaf (Spec (CommRingCat.of A)))
  (frame : (schemeModulePullback (closedComponentInclusion A I)).obj L.obj ≅
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)

/-- An actual geometric component frame induces a frame of the original
intersection-fiber module, through its original quotient restriction. -/
def closedNodeFrameModuleIso :
    (ModuleCat.extendScalars (Ideal.Quotient.mk K)).obj
      (AffineModuleTilde.sectionModule L.obj ⊤) ≅ ModuleCat.of (A ⧸ K) (A ⧸ K) :=
  closedNodeExtensionIso A I K hIK (AffineModuleTilde.sectionModule L.obj ⊤) ≪≫
    (ModuleCat.extendScalars (Ideal.Quotient.factor hIK)).mapIso
      (closedComponentFrameModuleIso A I L frame) ≪≫
        extensionRingModuleIso (Ideal.Quotient.factor hIK)

/-- This fiber frame is exactly the original quotient of the original
component-frame coordinate of the same section. -/
theorem closedNodeFrameModuleIso_one_tmul
    (m : AffineModuleTilde.sectionModule L.obj ⊤) :
    (closedNodeFrameModuleIso A I K hIK L frame).hom
        ((1 : A ⧸ K) ⊗ₜ[A, Ideal.Quotient.mk K] m) =
      Ideal.Quotient.factor hIK
        ((closedComponentFrameModuleIso A I L frame).hom
          ((1 : A ⧸ I) ⊗ₜ[A, Ideal.Quotient.mk I] m)) := by
  change (extensionRingModuleIso (Ideal.Quotient.factor hIK)).hom
    ((ModuleCat.extendScalars (Ideal.Quotient.factor hIK)).map
      (closedComponentFrameModuleIso A I L frame).hom
        ((closedNodeExtensionIso A I K hIK
          (AffineModuleTilde.sectionModule L.obj ⊤)).hom
            ((1 : A ⧸ K) ⊗ₜ[A, Ideal.Quotient.mk K] m))) = _
  rw [closedNodeExtensionIso_one_tmul, ModuleCat.ExtendScalars.map_tmul,
    extensionRingModuleIso_one_tmul]

section TwoComponents

variable (J : Ideal A)
  (leftFrame : (schemeModulePullback (closedComponentInclusion A I)).obj L.obj ≅
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)
  (rightFrame : (schemeModulePullback (closedComponentInclusion A J)).obj L.obj ≅
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf)

/-- The original two component frames determine their intersection unit;
neither the unit nor its coordinate-change identity is assumed. -/
def closedNodeTransitionUnit : (A ⧸ I ⊔ J)ˣ :=
  KltDP.Module.transitionUnit
    (closedNodeFrameModuleIso A J (I ⊔ J) le_sup_right L rightFrame).toLinearEquiv
    (closedNodeFrameModuleIso A I (I ⊔ J) le_sup_left L leftFrame).toLinearEquiv

/-- Original component coordinates of every original global section obey
the matching equation with the constructed original intersection unit. -/
theorem closedNodeTransitionUnit_matching
    (m : AffineModuleTilde.sectionModule L.obj ⊤) :
    Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left)
        (closedBranchFrameEquiv A I L leftFrame (m ⊗ₜ[A] (1 : A ⧸ I))) =
      (closedNodeTransitionUnit A I L J leftFrame rightFrame : A ⧸ I ⊔ J) *
        Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right)
          (closedBranchFrameEquiv A J L rightFrame (m ⊗ₜ[A] (1 : A ⧸ J))) := by
  have h := KltDP.Module.transitionUnit_mul_apply
    (closedNodeFrameModuleIso A J (I ⊔ J) le_sup_right L rightFrame).toLinearEquiv
    (closedNodeFrameModuleIso A I (I ⊔ J) le_sup_left L leftFrame).toLinearEquiv
    ((1 : A ⧸ I ⊔ J) ⊗ₜ[A, Ideal.Quotient.mk (I ⊔ J)] m)
  change (closedNodeTransitionUnit A I L J leftFrame rightFrame : A ⧸ I ⊔ J) *
      (closedNodeFrameModuleIso A J (I ⊔ J) le_sup_right L rightFrame).hom
        ((1 : A ⧸ I ⊔ J) ⊗ₜ[A, Ideal.Quotient.mk (I ⊔ J)] m) =
    (closedNodeFrameModuleIso A I (I ⊔ J) le_sup_left L leftFrame).hom
      ((1 : A ⧸ I ⊔ J) ⊗ₜ[A, Ideal.Quotient.mk (I ⊔ J)] m) at h
  rw [closedNodeFrameModuleIso_one_tmul, closedNodeFrameModuleIso_one_tmul] at h
  exact h.symm

end TwoComponents

end KltDP.Geometry.RationalTreePicard
