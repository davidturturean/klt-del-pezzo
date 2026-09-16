/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

The tilde tensor-inverse transport follows the proved construction in
MazurTorsion/Upstream/DivisorLineBundle.lean, revision
9327963d4ec14fba49c7b14b004fd00707ffc2e9, lines 627–642. The existing
regular principal frames replace its newer Module.Invertible interface.
The generic evaluation-cancellation proof reuses the accepted argument
in KltDP/Geometry/SchemeInvertibleDualPullback.lean, lines 31–62.
-/
import KltDP.RingTheory.RegularPrincipalConormal
import KltDP.Geometry.AffineModuleTildeTensorIso
import KltDP.Geometry.AffineModuleTildeFunctor
import KltDP.Geometry.AffineModuleTildeUnit
import KltDP.Geometry.SchemeInvertibleDualPullback

/-!
# Actual tilde dual of a regular principal conormal module

The original module dual of `J.Cotangent`, followed by the original tilde
functor, is identified with the existing sheaf dual of the conormal tilde.
The comparison is characterized by the original evaluation: on module
pure tensors the transported pairing is precisely `m ⊗ ℓ ↦ ℓ m`.

Only an actual regular principal equation of `J` is assumed. The resulting
evaluation and dual comparison are independent of that equation. General
coherent-Hom localization, global conormal matching, common affine
refinements and global adjunction remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u v w

namespace KltDP.Geometry.PrincipalConormalTildeDual

section TensorCancellation

variable {C : Type w} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

private def tensorLeftEquivalenceOfInverse {P D : C} (d : P ⊗ D ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft P) (tensorLeft D)
    ((tensorLeftTensor D P).symm ≪≫
      (tensoringLeft C).mapIso ((β_ D P) ≪≫ d) ≪≫ leftUnitorNatIso C).symm
    ((tensorLeftTensor P D).symm ≪≫
      (tensoringLeft C).mapIso d ≪≫ leftUnitorNatIso C)

private def tensorLeftFullyFaithfulOfInverse {P D : C} (d : P ⊗ D ≅ 𝟙_ C) :
    (tensorLeft P).FullyFaithful :=
  (tensorLeftEquivalenceOfInverse d).fullyFaithfulFunctor

private def comparisonOfEvaluations {P B D U : C}
    (hP : (tensorLeft P).FullyFaithful) (e : P ⊗ B ≅ U) (d : P ⊗ D ≅ U) :
    B ≅ D :=
  hP.preimageIso (e ≪≫ d.symm)

private theorem comparisonOfEvaluations_comp {P B D U : C}
    (hP : (tensorLeft P).FullyFaithful) (e : P ⊗ B ≅ U) (d : P ⊗ D ≅ U) :
    P ◁ (comparisonOfEvaluations hP e d).hom ≫ d.hom = e.hom := by
  change (tensorLeft P).map (hP.preimage (e ≪≫ d.symm).hom) ≫ d.hom = e.hom
  rw [hP.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem comparisonOfEvaluations_unique {P B D U : C}
    (hP : (tensorLeft P).FullyFaithful) (e : P ⊗ B ≅ U) (d : P ⊗ D ≅ U)
    (m : B ⟶ D) (hm : P ◁ m ≫ d.hom = e.hom) :
    m = (comparisonOfEvaluations hP e d).hom := by
  apply hP.map_injective
  apply (cancel_mono d.hom).1
  exact hm.trans (comparisonOfEvaluations_comp hP e d).symm

end TensorCancellation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance structureSectionsComm (S : Scheme.{u}) :
    ∀ U, IsMulCommutative (S.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (S.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance modulesMonoidal (S : Scheme.{u}) : MonoidalCategory S.Modules :=
  Scheme.Modules.monoidalCategory S

local instance modulesSymmetric (S : Scheme.{u}) : SymmetricCategory S.Modules :=
  Scheme.Modules.symmetricCategory S

variable {A : Type u} [CommRing A] (J : Ideal A)

/-- The actual ideal conormal module, with its original quotient-ring action. -/
abbrev conormalModule : ModuleCat.{u} (A ⧸ J) := ModuleCat.of (A ⧸ J) J.Cotangent

/-- The actual module dual of the ideal conormal module. -/
abbrev normalModule : ModuleCat.{u} (A ⧸ J) :=
  ModuleCat.of (A ⧸ J) (Module.Dual (A ⧸ J) J.Cotangent)

variable (d : J) (hJ : Ideal.span {(d : A)} = J)
  (hregular : (d : A) ∈ nonZeroDivisors A)

/-- The regular principal frames make the actual module evaluation invertible. -/
def moduleEvaluationEquiv :
    AffineModuleTildeTensor.tensorModule (conormalModule J) (normalModule J)
      ≃ₗ[A ⧸ J] (A ⧸ J) :=
  TensorProduct.congr
    (KltDP.RingTheory.principalConormalEquiv J d hJ hregular).symm
    (KltDP.RingTheory.principalNormalEquiv J d hJ hregular) ≪≫ₗ
      TensorProduct.lid (A ⧸ J) (A ⧸ J)

/-- The produced pairing is the original evaluation on every pure tensor. -/
theorem moduleEvaluationEquiv_tmul (m : J.Cotangent)
    (ℓ : Module.Dual (A ⧸ J) J.Cotangent) :
    moduleEvaluationEquiv J d hJ hregular (m ⊗ₜ[A ⧸ J] ℓ) = ℓ m := by
  simp only [moduleEvaluationEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    TensorProduct.lid_tmul, KltDP.RingTheory.principalNormalEquiv_apply]
  rw [← map_smul]
  exact congrArg ℓ
    ((KltDP.RingTheory.principalConormalEquiv J d hJ hregular).apply_symm_apply m)

/-- Ordinary evaluation does not depend on the chosen regular equation. -/
theorem moduleEvaluationEquiv_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (heregular : (e : A) ∈ nonZeroDivisors A) :
    moduleEvaluationEquiv J e hE heregular = moduleEvaluationEquiv J d hJ hregular := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro m ℓ
  exact (moduleEvaluationEquiv_tmul J e hE heregular m ℓ).trans
    (moduleEvaluationEquiv_tmul J d hJ hregular m ℓ).symm

/-- The original equation frame proves that the conormal tilde is a line. -/
def conormalFrameIso :
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf ≅
      (conormalModule J).tilde :=
  (AffineModuleTilde.unitIso (A ⧸ J)).symm ≪≫
    AffineModuleTilde.linearEquivIso
      (M := ModuleCat.of (A ⧸ J) (A ⧸ J)) (N := conormalModule J)
      (KltDP.RingTheory.principalConormalEquiv J d hJ hregular)

/-- Rank one is produced for the actual conormal tilde, with no line witness input. -/
def conormalLine : InvertibleSheaf (Spec (CommRingCat.of (A ⧸ J))) :=
  InvertibleSheaf.ofIso (InvertibleSheaf.trivial (Spec (CommRingCat.of (A ⧸ J))))
    (conormalFrameIso J d hJ hregular)

/-- Actual module evaluation transported through the original tilde tensor and unit maps. -/
def transportedEvaluationIso :
    (conormalModule J).tilde ⊗ (normalModule J).tilde ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf :=
  (AffineModuleTildeTensor.iso (conormalModule J) (normalModule J)).symm ≪≫
    AffineModuleTilde.linearEquivIso
      (M := AffineModuleTildeTensor.tensorModule (conormalModule J) (normalModule J))
      (N := ModuleCat.of (A ⧸ J) (A ⧸ J))
      (moduleEvaluationEquiv J d hJ hregular) ≪≫
    AffineModuleTilde.unitIso (A ⧸ J)

/-- This transported evaluation retains the original tensor comparison and actual pairing. -/
theorem transportedEvaluationIso_hom :
    (transportedEvaluationIso J d hJ hregular).hom =
      (AffineModuleTildeTensor.iso (conormalModule J) (normalModule J)).inv ≫
        (AffineModuleTilde.linearEquivIso
          (M := AffineModuleTildeTensor.tensorModule (conormalModule J) (normalModule J))
          (N := ModuleCat.of (A ⧸ J) (A ⧸ J))
          (moduleEvaluationEquiv J d hJ hregular)).hom ≫
        (AffineModuleTilde.unitIso (A ⧸ J)).hom := rfl

/-- The transported original evaluation is independent of the regular equation. -/
theorem transportedEvaluationIso_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (heregular : (e : A) ∈ nonZeroDivisors A) :
    transportedEvaluationIso J e hE heregular =
      transportedEvaluationIso J d hJ hregular := by
  unfold transportedEvaluationIso
  rw [moduleEvaluationEquiv_eq J d hJ hregular e hE heregular]

private def conormalSheafEvaluationIso :
    (conormalModule J).tilde ⊗
        KltDP.SheafOfModules.dual (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf
          (conormalModule J).tilde ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf := by
  letI : KltDP.SheafOfModules.IsInvertible
      (R := (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf) (conormalModule J).tilde :=
    (conormalLine J d hJ hregular).property
  exact KltDP.SheafOfModules.evaluationIso (Spec (CommRingCat.of (A ⧸ J))).sheaf.val
    (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf.cond (conormalModule J).tilde

private def conormalTensorFullyFaithful :
    (tensorLeft (conormalModule J).tilde).FullyFaithful :=
  tensorLeftFullyFaithfulOfInverse
    (conormalSheafEvaluationIso J d hJ hregular ≪≫
      (PresheafOfModules.sheafTensorUnitIso (Spec (CommRingCat.of (A ⧸ J))).sheaf.val
        (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf.cond).symm)

/-- Tilde of the actual normal module is the existing dual of the conormal tilde. -/
def iso :
    (normalModule J).tilde ≅
      KltDP.SheafOfModules.dual (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf
        (conormalModule J).tilde :=
  comparisonOfEvaluations (conormalTensorFullyFaithful J d hJ hregular)
    (transportedEvaluationIso J d hJ hregular)
    (conormalSheafEvaluationIso J d hJ hregular)

/-- The produced comparison preserves the existing evaluation with the exact unit normalization. -/
theorem iso_evaluation :
    (conormalModule J).tilde ◁ (iso J d hJ hregular).hom ≫
      KltDP.SheafOfModules.evaluation (Spec (CommRingCat.of (A ⧸ J))).sheaf.val
        (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf.cond (conormalModule J).tilde =
      (transportedEvaluationIso J d hJ hregular).hom :=
  comparisonOfEvaluations_comp (conormalTensorFullyFaithful J d hJ hregular)
    (transportedEvaluationIso J d hJ hregular)
    (conormalSheafEvaluationIso J d hJ hregular)

/-- Matching the actual evaluation characterizes the produced forward map uniquely. -/
theorem iso_unique
    (m : (normalModule J).tilde ⟶
      KltDP.SheafOfModules.dual (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf
        (conormalModule J).tilde)
    (hm : (conormalModule J).tilde ◁ m ≫
      KltDP.SheafOfModules.evaluation (Spec (CommRingCat.of (A ⧸ J))).sheaf.val
        (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf.cond (conormalModule J).tilde =
      (transportedEvaluationIso J d hJ hregular).hom) :
    m = (iso J d hJ hregular).hom :=
  comparisonOfEvaluations_unique (conormalTensorFullyFaithful J d hJ hregular)
    (transportedEvaluationIso J d hJ hregular)
    (conormalSheafEvaluationIso J d hJ hregular) m hm

/-- The actual dual comparison is independent of the regular equation. -/
theorem iso_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (heregular : (e : A) ∈ nonZeroDivisors A) :
    iso J e hE heregular = iso J d hJ hregular := by
  apply Iso.ext
  apply iso_unique J d hJ hregular
  exact (iso_evaluation J e hE heregular).trans
    (congrArg (fun i => i.hom) (transportedEvaluationIso_eq J d hJ hregular e hE heregular))

end KltDP.Geometry.PrincipalConormalTildeDual
