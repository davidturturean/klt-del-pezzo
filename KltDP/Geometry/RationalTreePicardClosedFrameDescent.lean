import KltDP.Geometry.RationalTreePicardClosedFrameMatching
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Affine descent from actual frames on two closed components

The original node frame identifies the tensor of the original quotient
difference with the scalar difference derived from the two geometric
frames. The pinned tensor-product distribution over pairs and the proved
flat tensor-kernel equivalence then reconstruct the original line bundle.

The affine hypotheses refer to the original ideals: they cover
scheme-theoretically, and their intersection is reduced with one-point
support. Deriving these data from a general nodal curve, and compatibility
of these affine isomorphisms on overlaps, remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.RationalTreePicard

section NodeTensor

variable (A : Type u) [CommRing A] (I K : Ideal A) (hIK : I ≤ K)
  (L : InvertibleSheaf (Spec (CommRingCat.of A)))
  (frame : (schemeModulePullback (closedComponentInclusion A I)).obj L.obj ≅
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)

/-- The original node frame, with the tensor carrier and original
quotient scalar action transported explicitly. -/
def closedNodeTensorFrameEquiv :
    AffineModuleTilde.sectionModule L.obj ⊤ ⊗[A] (A ⧸ K) ≃ₗ[A] A ⧸ K :=
  (closedBranchTensorEquiv A K (AffineModuleTilde.sectionModule L.obj ⊤)).trans
    (((ModuleCat.restrictScalars (Ideal.Quotient.mk K)).mapIso
      (closedNodeFrameModuleIso A I K hIK L frame)).toLinearEquiv.trans
        (quotientCompHomEquiv A K).symm)

/-- On the original section generator, the node frame is the original
quotient of its component coordinate. -/
theorem closedNodeTensorFrameEquiv_one_tmul
    (m : AffineModuleTilde.sectionModule L.obj ⊤) :
    closedNodeTensorFrameEquiv A I K hIK L frame (m ⊗ₜ[A] (1 : A ⧸ K)) =
      quotientFactorLinear A hIK
        (closedBranchFrameEquiv A I L frame (m ⊗ₜ[A] (1 : A ⧸ I))) :=
  closedNodeFrameModuleIso_one_tmul A I K hIK L frame m

/-- An original quotient scalar moves across the same original tensor. -/
private theorem quotient_tmul_mk (M : Type u) [AddCommGroup M] [Module A M]
    (m : M) (a : A) :
    m ⊗ₜ[A] Ideal.Quotient.mk K a = a • (m ⊗ₜ[A] (1 : A ⧸ K)) := by
  simpa only [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq] using
    (TensorProduct.tmul_smul a m (1 : A ⧸ K))

/-- Compatibility with the original quotient factor holds for every
branch coefficient, not only the distinguished tensor generator. -/
theorem closedNodeTensorFrameEquiv_factor
    (m : AffineModuleTilde.sectionModule L.obj ⊤) (b : A ⧸ I) :
    closedNodeTensorFrameEquiv A I K hIK L frame
        (m ⊗ₜ[A] quotientFactorLinear A hIK b) =
      quotientFactorLinear A hIK
        (closedBranchFrameEquiv A I L frame (m ⊗ₜ[A] b)) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  change closedNodeTensorFrameEquiv A I K hIK L frame
      (m ⊗ₜ[A] Ideal.Quotient.mk K a) =
    quotientFactorLinear A hIK
      (closedBranchFrameEquiv A I L frame (m ⊗ₜ[A] Ideal.Quotient.mk I a))
  rw [quotient_tmul_mk A K, quotient_tmul_mk A I, map_smul, map_smul, map_smul,
    closedNodeTensorFrameEquiv_one_tmul]

end NodeTensor

variable (k A : Type u) [Field k] [IsAlgClosed k] [CommRing A]
  [Algebra k A] [Algebra.FiniteType k A]
  (I J : Ideal A) (q : PrimeSpectrum A)
  (hsupport : PrimeSpectrum.zeroLocus (I ⊔ J : Ideal A) = {q})
  [IsReduced (A ⧸ I ⊔ J)]
  (L : InvertibleSheaf (Spec (CommRingCat.of A)))
  (leftFrame : (schemeModulePullback (closedComponentInclusion A I)).obj L.obj ≅
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)
  (rightFrame : (schemeModulePullback (closedComponentInclusion A J)).obj L.obj ≅
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf)

/-- The derived scalar lift relates the two original node frames on the
whole original tensor module. -/
theorem closedNodeTensorFrameEquiv_transition
    (x : AffineModuleTilde.sectionModule L.obj ⊤ ⊗[A] (A ⧸ I ⊔ J)) :
    closedNodeTensorFrameEquiv A I (I ⊔ J) le_sup_left L leftFrame x =
      closedLineGaugeUnit A
          (closedFrameScalar k A I J q hsupport L leftFrame rightFrame) •
        closedNodeTensorFrameEquiv A J (I ⊔ J) le_sup_right L rightFrame x := by
  rw [Units.smul_def, Algebra.smul_def]
  change _ = algebraMap A (A ⧸ I ⊔ J)
      (algebraMap k A (closedFrameScalar k A I J q hsupport L leftFrame rightFrame : k)) * _
  rw [← IsScalarTower.algebraMap_apply k A (A ⧸ I ⊔ J)]
  rw [show algebraMap k (A ⧸ I ⊔ J)
      (closedFrameScalar k A I J q hsupport L leftFrame rightFrame : k) =
        (closedNodeTransitionUnit A I L J leftFrame rightFrame : A ⧸ I ⊔ J) from
    reducedNodeScalarUnit_algebraMap A I J q hsupport k _]
  exact (KltDP.Module.transitionUnit_mul_apply
    (closedNodeFrameModuleIso A J (I ⊔ J) le_sup_right L rightFrame).toLinearEquiv
    (closedNodeFrameModuleIso A I (I ⊔ J) le_sup_left L leftFrame).toLinearEquiv
    (closedBranchTensorEquiv A (I ⊔ J) (AffineModuleTilde.sectionModule L.obj ⊤) x)).symm

/-- Pinned tensor distribution and the actual component frames give the
original component-coordinate equivalence. -/
def closedTensorCoordinateEquiv :
    AffineModuleTilde.sectionModule L.obj ⊤ ⊗[A] ((A ⧸ I) × (A ⧸ J)) ≃ₗ[A]
      (A ⧸ I) × (A ⧸ J) :=
  (TensorProduct.prodRight A A (AffineModuleTilde.sectionModule L.obj ⊤)
    (A ⧸ I) (A ⧸ J)).trans
      ((closedBranchFrameEquiv A I L leftFrame).prodCongr
        (closedBranchFrameEquiv A J L rightFrame))

/-- The square with the original tensor difference and the derived scalar
difference commutes through the actual right node frame. -/
theorem closedTensorCoordinate_difference
    (x : AffineModuleTilde.sectionModule L.obj ⊤ ⊗[A] ((A ⧸ I) × (A ⧸ J))) :
    closedLineDifference A I J
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame)
        (closedTensorCoordinateEquiv A I J L leftFrame rightFrame x) =
      closedNodeTensorFrameEquiv A J (I ⊔ J) le_sup_right L rightFrame
        (closedTensorDifference A I J (AffineModuleTilde.sectionModule L.obj ⊤) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero]
  | tmul m z =>
    change (closedLineGaugeUnit A
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame))⁻¹ •
        quotientFactorLinear A (show I ≤ I ⊔ J from le_sup_left)
          (closedBranchFrameEquiv A I L leftFrame (m ⊗ₜ[A] z.1)) -
        quotientFactorLinear A (show J ≤ I ⊔ J from le_sup_right)
          (closedBranchFrameEquiv A J L rightFrame (m ⊗ₜ[A] z.2)) =
      closedNodeTensorFrameEquiv A J (I ⊔ J) le_sup_right L rightFrame
        (m ⊗ₜ[A] (quotientFactorLinear A (show I ≤ I ⊔ J from le_sup_left) z.1 -
          quotientFactorLinear A (show J ≤ I ⊔ J from le_sup_right) z.2))
    have hsub (a b : AffineModuleTilde.sectionModule L.obj ⊤ ⊗[A] (A ⧸ I ⊔ J)) :
        closedNodeTensorFrameEquiv A J (I ⊔ J) le_sup_right L rightFrame (a - b) =
          closedNodeTensorFrameEquiv A J (I ⊔ J) le_sup_right L rightFrame a -
            closedNodeTensorFrameEquiv A J (I ⊔ J) le_sup_right L rightFrame b :=
      (closedNodeTensorFrameEquiv A J (I ⊔ J) le_sup_right L rightFrame).toLinearMap.map_sub a b
    rw [TensorProduct.tmul_sub, hsub,
      ← closedNodeTensorFrameEquiv_factor A I (I ⊔ J) le_sup_left,
      ← closedNodeTensorFrameEquiv_factor A J (I ⊔ J) le_sup_right,
      closedNodeTensorFrameEquiv_transition k A I J q hsupport L leftFrame rightFrame,
      inv_smul_smul]
  | add x y hx hy =>
    simpa only [LinearMap.map_add, LinearEquiv.map_add] using congrArg₂ (· + ·) hx hy

/-- The original tensor kernel is precisely the inverse image of the
actual scalar kernel under the actual component-coordinate equivalence. -/
theorem closedTensorKernel_eq_comap :
    LinearMap.ker (closedTensorDifference A I J (AffineModuleTilde.sectionModule L.obj ⊤)) =
      (LinearMap.ker (closedLineDifference A I J
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame))).comap
          (closedTensorCoordinateEquiv A I J L leftFrame rightFrame).toLinearMap := by
  ext x
  change closedTensorDifference A I J (AffineModuleTilde.sectionModule L.obj ⊤) x = 0 ↔
    closedLineDifference A I J
      (closedFrameScalar k A I J q hsupport L leftFrame rightFrame)
      (closedTensorCoordinateEquiv A I J L leftFrame rightFrame x) = 0
  rw [closedTensorCoordinate_difference]
  exact (closedNodeTensorFrameEquiv A J (I ⊔ J) le_sup_right L rightFrame).map_eq_zero_iff.symm

/-- Actual component coordinates restrict to the equivalence of the two
actual matching kernels; node-frame injectivity was proved by its iso. -/
def closedTensorCoordinateKernelEquiv :
    LinearMap.ker (closedTensorDifference A I J (AffineModuleTilde.sectionModule L.obj ⊤)) ≃ₗ[A]
      LinearMap.ker (closedLineDifference A I J
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame)) :=
  (LinearEquiv.ofEq _ _
    (closedTensorKernel_eq_comap k A I J q hsupport L leftFrame rightFrame)).trans
      (LinearEquiv.ofSubmodule' (closedTensorCoordinateEquiv A I J L leftFrame rightFrame) _)

/-- The original global-section module is the scalar matching kernel.
Flatness follows from the actual invertible sheaf's local frames. -/
def closedFrameDescentEquiv (hcover : I ⊓ J = ⊥) :
    AffineModuleTilde.sectionModule L.obj ⊤ ≃ₗ[A]
      LinearMap.ker (closedLineDifference A I J
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame)) := by
  letI := AffineModuleTilde.invertibleGlobalSections_flat L
  exact (closedCoverFlatKernelEquiv A I J
    (AffineModuleTilde.sectionModule L.obj ⊤) hcover).trans
      (closedTensorCoordinateKernelEquiv k A I J q hsupport L leftFrame rightFrame)

/-- The constructed equivalence uses exactly the previously defined
original section-to-matching map. -/
theorem closedFrameDescentEquiv_apply (hcover : I ⊓ J = ⊥)
    (m : AffineModuleTilde.sectionModule L.obj ⊤) :
    closedFrameDescentEquiv k A I J q hsupport L leftFrame rightFrame hcover m =
      closedFrameMatchingLinear k A I J q hsupport L leftFrame rightFrame m := by
  letI := AffineModuleTilde.invertibleGlobalSections_flat L
  have hcoord :
      (closedCoverFlatKernelEquiv A I J (AffineModuleTilde.sectionModule L.obj ⊤)
          hcover m : AffineModuleTilde.sectionModule L.obj ⊤ ⊗[A]
            ((A ⧸ I) × (A ⧸ J))) = m ⊗ₜ[A] (1, 1) := by
    let e : (A ⧸ I ⊓ J) ≃ₐ[A] A :=
      (Ideal.quotientEquivAlgOfEq A hcover).trans (AlgEquiv.quotientBot A A)
    have he : e.symm 1 = 1 := map_one e.symm
    change (closedFlatTensorKernelEquiv A I J (AffineModuleTilde.sectionModule L.obj ⊤)
        (m ⊗ₜ[A] e.symm 1) : AffineModuleTilde.sectionModule L.obj ⊤ ⊗[A]
          ((A ⧸ I) × (A ⧸ J))) = _
    rw [he, closedFlatTensorKernelEquiv_tmul]
    apply congrArg (fun z => m ⊗ₜ[A] z)
    change (Ideal.Quotient.factor (show I ⊓ J ≤ I from inf_le_left) 1,
      Ideal.Quotient.factor (show I ⊓ J ≤ J from inf_le_right) 1) = (1, 1)
    simp only [map_one]
  apply Subtype.ext
  change closedTensorCoordinateEquiv A I J L leftFrame rightFrame
      (closedCoverFlatKernelEquiv A I J (AffineModuleTilde.sectionModule L.obj ⊤)
        hcover m : AffineModuleTilde.sectionModule L.obj ⊤ ⊗[A]
          ((A ⧸ I) × (A ⧸ J))) =
    closedFrameCoordinatePair A I J L leftFrame rightFrame m
  rw [hcoord]
  rfl

/-- Bijectivity holds for the original matching map itself. -/
theorem closedFrameMatchingLinear_bijective (hcover : I ⊓ J = ⊥) :
    Function.Bijective
      (closedFrameMatchingLinear k A I J q hsupport L leftFrame rightFrame) := by
  have he : (closedFrameDescentEquiv k A I J q hsupport L leftFrame rightFrame
      hcover).toLinearMap =
        closedFrameMatchingLinear k A I J q hsupport L leftFrame rightFrame := by
    apply LinearMap.ext
    intro m
    exact closedFrameDescentEquiv_apply k A I J q hsupport L leftFrame rightFrame hcover m
  rw [← he]
  exact (closedFrameDescentEquiv k A I J q hsupport L leftFrame rightFrame hcover).bijective

/-- The original line bundle is the actual scalar matching sheaf. -/
def closedFrameDescentSheafIso (hcover : I ⊓ J = ⊥) :
    L.obj ≅ closedLineMatchingSheaf A I J
      (closedFrameScalar k A I J q hsupport L leftFrame rightFrame) :=
  (AffineModuleTilde.invertibleCounitIso L).symm ≪≫
    AffineModuleTilde.mapIso ((closedFrameDescentEquiv k A I J q hsupport L
      leftFrame rightFrame hcover).toModuleIso ≪≫
        (ModuleCat.kernelIsoKer (closedLineDifferenceHom A I J
          (closedFrameScalar k A I J q hsupport L leftFrame rightFrame))).symm) ≪≫
      AffineModuleTilde.kernelIso (closedLineDifferenceHom A I J
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame))

/-- The sheaf isomorphism has the previously constructed original
matching map as its forward morphism. -/
theorem closedFrameDescentSheafIso_hom (hcover : I ⊓ J = ⊥) :
    (closedFrameDescentSheafIso k A I J q hsupport L leftFrame rightFrame hcover).hom =
      closedFrameMatchingSheafMap k A I J q hsupport L leftFrame rightFrame := by
  have he : (closedFrameDescentEquiv k A I J q hsupport L leftFrame rightFrame
      hcover).toModuleIso.hom = ModuleCat.ofHom
        (X := AffineModuleTilde.sectionModule L.obj ⊤)
        (Y := LinearMap.ker (closedLineDifference A I J
          (closedFrameScalar k A I J q hsupport L leftFrame rightFrame)))
        (closedFrameMatchingLinear k A I J q hsupport L leftFrame rightFrame) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact closedFrameDescentEquiv_apply k A I J q hsupport L leftFrame rightFrame hcover m
  change (AffineModuleTilde.invertibleCounitIso L).inv ≫
      AffineModuleTilde.map
        ((closedFrameDescentEquiv k A I J q hsupport L leftFrame rightFrame
          hcover).toModuleIso.hom ≫
          (ModuleCat.kernelIsoKer (closedLineDifferenceHom A I J
            (closedFrameScalar k A I J q hsupport L leftFrame rightFrame))).symm.hom) ≫
        (AffineModuleTilde.kernelIso (closedLineDifferenceHom A I J
          (closedFrameScalar k A I J q hsupport L leftFrame rightFrame))).hom = _
  rw [AffineModuleTilde.map_comp, he]
  rfl

/-- The original sheaf comparison retains the actual pair of geometric
component coordinates after inclusion in the matching-kernel source. -/
theorem closedFrameMatchingSheafMap_ι :
    closedFrameMatchingSheafMap k A I J q hsupport L leftFrame rightFrame ≫
        kernel.ι (AffineModuleTilde.map (closedLineDifferenceHom A I J
          (closedFrameScalar k A I J q hsupport L leftFrame rightFrame))) =
      (AffineModuleTilde.invertibleCounitIso L).inv ≫
        AffineModuleTilde.map (ModuleCat.ofHom
          (X := AffineModuleTilde.sectionModule L.obj ⊤)
          (Y := (A ⧸ I) × (A ⧸ J))
          (closedFrameCoordinatePair A I J L leftFrame rightFrame)) := by
  let d := closedLineDifferenceHom A I J
    (closedFrameScalar k A I J q hsupport L leftFrame rightFrame)
  have hsheaf : (AffineModuleTilde.kernelIso d).hom ≫
      kernel.ι (AffineModuleTilde.map d) = AffineModuleTilde.map (kernel.ι d) :=
    AffineModuleTilde.kernelIso_hom_ι d
  have hmodule : (ModuleCat.kernelIsoKer d).symm.hom ≫ kernel.ι d =
      ModuleCat.ofHom (LinearMap.ker d.hom).subtype :=
    ModuleCat.kernelIsoKer_inv_kernel_ι d
  have hpair : ModuleCat.ofHom
      (X := AffineModuleTilde.sectionModule L.obj ⊤)
      (Y := LinearMap.ker d.hom)
      (closedFrameMatchingLinear k A I J q hsupport L leftFrame rightFrame) ≫
      ModuleCat.ofHom (LinearMap.ker d.hom).subtype =
        ModuleCat.ofHom
          (X := AffineModuleTilde.sectionModule L.obj ⊤)
          (Y := (A ⧸ I) × (A ⧸ J))
          (closedFrameCoordinatePair A I J L leftFrame rightFrame) := rfl
  change ((AffineModuleTilde.invertibleCounitIso L).inv ≫
      AffineModuleTilde.map (ModuleCat.ofHom
        (X := AffineModuleTilde.sectionModule L.obj ⊤)
        (Y := LinearMap.ker d.hom)
        (closedFrameMatchingLinear k A I J q hsupport L leftFrame rightFrame)) ≫
      (AffineModuleTilde.mapIso (ModuleCat.kernelIsoKer d).symm).hom ≫
      (AffineModuleTilde.kernelIso d).hom) ≫ kernel.ι (AffineModuleTilde.map d) = _
  simp only [Category.assoc]
  rw [hsheaf, AffineModuleTilde.mapIso_hom, ← AffineModuleTilde.map_comp,
    hmodule, ← AffineModuleTilde.map_comp, hpair]

/-- An original affine line bundle with actual frames on two original
closed components meeting in a reduced rational point is trivial. -/
def closedFrameUnitIso (hcover : I ⊓ J = ⊥) :
    L.obj ≅ _root_.SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf :=
  closedFrameDescentSheafIso k A I J q hsupport L leftFrame rightFrame hcover ≪≫
    (closedLineUnitIso A I J
      (closedFrameScalar k A I J q hsupport L leftFrame rightFrame) hcover).symm

end KltDP.Geometry.RationalTreePicard
