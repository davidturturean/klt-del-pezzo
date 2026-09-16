import KltDP.Geometry.RationalTreePicardClosedUnionSheaf
import KltDP.Geometry.RationalTreePicardClosedPushforward
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Scalar line-bundle gluing across two actual closed components

For the original quotient restrictions, the equation
`res_I(x) = g res_J(y)` is written as a kernel of the normalized difference
`g⁻¹ res_I(x) - res_J(y)`. The scalar node unit is mapped from the original
base algebra; a component unit lifting it is constructed, not assumed.

Scaling the first original component coordinate gives a linear equivalence
with the already proved untwisted closed-union kernel. The existing affine
tilde kernel comparison proves that this actual matching sheaf is trivial
when I∩J=0. Its two component maps land in the actual closed pushforwards
through the original quotient-tilde comparisons.

This is the two-component scalar gluing step. Reduction of an arbitrary
nodal curve and line bundle to these data remains a separate argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.RationalTreePicard

variable {k : Type u} [CommRing k] (A : Type u) [CommRing A] [Algebra k A]
  (I J : Ideal A) (g : kˣ)

/-- The actual base scalar gives the needed component gauge unit. -/
def closedLineGaugeUnit : Aˣ := Units.map (algebraMap k A).toMonoidHom g

/-- The original component-coordinate change, linear over A. -/
def closedLineGauge : ((A ⧸ I) × (A ⧸ J)) ≃ₗ[A] (A ⧸ I) × (A ⧸ J) :=
  LinearEquiv.prodCongr
    (LinearEquiv.smulOfUnit (M := A ⧸ I) (closedLineGaugeUnit A g)⁻¹)
    (LinearEquiv.refl A (A ⧸ J))

/-- The original quotient maps with the prescribed scalar node transition. -/
def closedLineDifference : ((A ⧸ I) × (A ⧸ J)) →ₗ[A] A ⧸ I ⊔ J :=
  ((closedLineGaugeUnit A g)⁻¹ : Aˣ) •
      (quotientFactorLinear A (show I ≤ I ⊔ J from le_sup_left)).comp
        (LinearMap.fst A (A ⧸ I) (A ⧸ J)) -
    (quotientFactorLinear A (show J ≤ I ⊔ J from le_sup_right)).comp
      (LinearMap.snd A (A ⧸ I) (A ⧸ J))

/-- The coordinate change retains exactly the original quotient maps. -/
theorem closedLineDifference_eq (z : (A ⧸ I) × (A ⧸ J)) :
    closedLineDifference A I J g z =
      closedUnionDifference A I J (closedLineGauge A I J g z) := by
  change ((closedLineGaugeUnit A g)⁻¹ : Aˣ) •
      quotientFactorLinear A (show I ≤ I ⊔ J from le_sup_left) z.1 -
      quotientFactorLinear A (show J ≤ I ⊔ J from le_sup_right) z.2 =
    quotientFactorLinear A (show I ≤ I ⊔ J from le_sup_left)
        (((closedLineGaugeUnit A g)⁻¹ : Aˣ) • z.1) -
      quotientFactorLinear A (show J ≤ I ⊔ J from le_sup_right) z.2
  simp only [Units.smul_def, map_smul]

/-- The normalized difference is precisely the original gluing equation,
with g acting on the second branch value. -/
theorem mem_closedLineKernel_iff (z : (A ⧸ I) × (A ⧸ J)) :
    z ∈ LinearMap.ker (closedLineDifference A I J g) ↔
      quotientFactorLinear A (show I ≤ I ⊔ J from le_sup_left) z.1 =
        closedLineGaugeUnit A g •
          quotientFactorLinear A (show J ≤ I ⊔ J from le_sup_right) z.2 := by
  change ((closedLineGaugeUnit A g)⁻¹ •
      quotientFactorLinear A (show I ≤ I ⊔ J from le_sup_left) z.1 -
      quotientFactorLinear A (show J ≤ I ⊔ J from le_sup_right) z.2 = 0) ↔ _
  rw [sub_eq_zero]
  exact inv_smul_eq_iff

/-- The actual twisted kernel is the preimage of the actual untwisted
kernel under the constructed coordinate change. -/
theorem closedLineKernel_eq_comap :
    LinearMap.ker (closedLineDifference A I J g) =
      (LinearMap.ker (closedUnionDifference A I J)).comap
        (closedLineGauge A I J g).toLinearMap := by
  ext z
  change closedLineDifference A I J g z = 0 ↔
    closedUnionDifference A I J (closedLineGauge A I J g z) = 0
  rw [closedLineDifference_eq]

/-- The original component gauge induces the actual linear kernel
equivalence, using Mathlib's restriction of a linear equivalence. -/
def closedLineKernelEquiv :
    LinearMap.ker (closedLineDifference A I J g) ≃ₗ[A]
      LinearMap.ker (closedUnionDifference A I J) :=
  (LinearEquiv.ofEq _ _ (closedLineKernel_eq_comap A I J g)).trans
    (LinearEquiv.ofSubmodule' (closedLineGauge A I J g)
      (LinearMap.ker (closedUnionDifference A I J)))

/-- The original difference as a morphism of A-modules. -/
def closedLineDifferenceHom :
    ModuleCat.of A ((A ⧸ I) × (A ⧸ J)) ⟶ ModuleCat.of A (A ⧸ I ⊔ J) :=
  ModuleCat.ofHom (closedLineDifference A I J g)

/-- The original union quotient gives the categorical twisted kernel. -/
def closedLineModuleKernelIso :
    ModuleCat.of A (A ⧸ I ⊓ J) ≅ kernel (closedLineDifferenceHom A I J g) :=
  ((closedUnionKernelEquiv A I J).trans (closedLineKernelEquiv A I J g).symm).toModuleIso ≪≫
    (ModuleCat.kernelIsoKer (closedLineDifferenceHom A I J g)).symm

/-- The constructed generator uses the inverse gauge on the original
pair of component quotient maps. -/
def closedLinePairLinear : (A ⧸ I ⊓ J) →ₗ[A] (A ⧸ I) × (A ⧸ J) :=
  (closedLineGauge A I J g).symm.toLinearMap.comp (closedUnionPairLinear A I J)

/-- The kernel comparison preserves the original component coordinates,
with exactly the specified gauge. -/
theorem closedLineModuleKernelIso_hom_ι :
    (closedLineModuleKernelIso A I J g).hom ≫
        kernel.ι (closedLineDifferenceHom A I J g) =
      ModuleCat.ofHom (closedLinePairLinear A I J g) := by
  have hk : (ModuleCat.kernelIsoKer (closedLineDifferenceHom A I J g)).symm.hom ≫
      kernel.ι (closedLineDifferenceHom A I J g) =
        ModuleCat.ofHom (LinearMap.ker (closedLineDifference A I J g)).subtype :=
    ModuleCat.kernelIsoKer_inv_kernel_ι (closedLineDifferenceHom A I J g)
  rw [closedLineModuleKernelIso, Iso.trans_hom, Category.assoc, hk]
  rfl

/-- The actual sheaf of sections matching with the specified node scalar. -/
abbrev closedLineMatchingSheaf : (Spec (CommRingCat.of A)).Modules :=
  kernel (AffineModuleTilde.map (closedLineDifferenceHom A I J g))

/-- The literal tilde of the original union quotient is the actual
twisted matching sheaf. -/
def closedLineQuotientSheafIso :
    (ModuleCat.of A (A ⧸ I ⊓ J)).tilde ≅ closedLineMatchingSheaf A I J g :=
  AffineModuleTilde.mapIso (closedLineModuleKernelIso A I J g) ≪≫
    AffineModuleTilde.kernelIso (closedLineDifferenceHom A I J g)

/-- The whole-sheaf comparison retains the same original component maps. -/
theorem closedLineQuotientSheafIso_hom_ι :
    (closedLineQuotientSheafIso A I J g).hom ≫
        kernel.ι (AffineModuleTilde.map (closedLineDifferenceHom A I J g)) =
      AffineModuleTilde.map (ModuleCat.ofHom (closedLinePairLinear A I J g)) := by
  have hk : (AffineModuleTilde.kernelIso (closedLineDifferenceHom A I J g)).hom ≫
      kernel.ι (AffineModuleTilde.map (closedLineDifferenceHom A I J g)) =
        AffineModuleTilde.map (kernel.ι (closedLineDifferenceHom A I J g)) :=
    AffineModuleTilde.kernelIso_hom_ι (closedLineDifferenceHom A I J g)
  rw [closedLineQuotientSheafIso, Iso.trans_hom, Category.assoc, hk,
    AffineModuleTilde.mapIso_hom, ← AffineModuleTilde.map_comp,
    closedLineModuleKernelIso_hom_ι]

/-- Scalar gluing across a scheme-theoretic closed cover gives an actual
trivialization of the matching line sheaf. -/
def closedLineUnitIso (h : I ⊓ J = ⊥) :
    _root_.SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ≅
      closedLineMatchingSheaf A I J g :=
  (AffineModuleTilde.unitIso A).symm ≪≫
    (AffineModuleTilde.linearEquivIso
      (M := ModuleCat.of A (A ⧸ I ⊓ J)) (N := ModuleCat.of A A)
      ((Ideal.quotientEquivAlgOfEq A h).trans (AlgEquiv.quotientBot A A)).toLinearEquiv).symm ≪≫
        closedLineQuotientSheafIso A I J g

/-- The first original component map lands in the actual closed
pushforward of its structure sheaf. -/
def closedLineLeftComponentMap :
    closedLineMatchingSheaf A I J g ⟶ componentUnitPushforward A (A ⧸ I) :=
  kernel.ι (AffineModuleTilde.map (closedLineDifferenceHom A I J g)) ≫
    AffineModuleTilde.map (ModuleCat.ofHom (LinearMap.fst A (A ⧸ I) (A ⧸ J))) ≫
      (quotientTildePushforwardUnitIso A I).hom

/-- The second original component map uses the other original projection. -/
def closedLineRightComponentMap :
    closedLineMatchingSheaf A I J g ⟶ componentUnitPushforward A (A ⧸ J) :=
  kernel.ι (AffineModuleTilde.map (closedLineDifferenceHom A I J g)) ≫
    AffineModuleTilde.map (ModuleCat.ofHom (LinearMap.snd A (A ⧸ I) (A ⧸ J))) ≫
      (quotientTildePushforwardUnitIso A J).hom

end KltDP.Geometry.RationalTreePicard
