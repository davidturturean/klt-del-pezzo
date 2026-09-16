/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck

Adapted from CBirkbeck/AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/Picard/PicComparison.lean, lines 408–447.
The forward argument is stated over an arbitrary small site using the
actual local singleton bases already constructed in this project.
-/
import KltDP.Compatibility.InvertibleModuleSheaf
import KltDP.Compatibility.SheafEvaluationTrivialization
import KltDP.Compatibility.SheafificationOnCover
import KltDP.Compatibility.SheafModuleSymmetric
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.Algebra.Divisibility.Units

/-!
# Locally free rank-one sheaves are tensor-invertible

Restrict each actual local trivialization along maps into its covering
object. The presheaf evaluation is bijective there, so actual sheafification
inverts it. Its counit and the proved tensor/unit comparison isomorphisms
give a tensor inverse, namely the sheaf of local linear functionals.

Only the forward implication is supplied. No evaluation isomorphism,
tensor-invertibility, or converse local-freeness theorem is assumed.
-/

noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.SheafOfModules

section Trivializations

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  {M : _root_.SheafOfModules.{u} R}

/-- Express an existing free-singleton trivialization as an isomorphism
to the actual unit sheaf on its over-site. -/
noncomputable def LocalTrivializations.unitIso (t : LocalTrivializations M) (i : t.I) :
    M.over (t.X i) ≅ _root_.SheafOfModules.unit (R.over (t.X i)) :=
  (t.iso i).symm ≪≫
    _root_.SheafOfModules.freeUniqueIsoUnit (R := R.over (t.X i)) PUnit

/-- An actual local trivialization restricts along every map into its
covering object. -/
noncomputable def LocalTrivializations.unitIsoOver (t : LocalTrivializations M)
    (i : t.I) {U : C} (f : U ⟶ t.X i) :
    M.over U ≅ _root_.SheafOfModules.unit (R.over U) :=
  ((_root_.SheafOfModules.overFunctorMap R f).app M).symm ≪≫
    (_root_.SheafOfModules.overMap R f).mapIso (t.unitIso i) ≪≫
      _root_.SheafOfModules.overMapUnitIso R f

end Trivializations

section Tensor

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [J.WEqualsLocallyBijective AddCommGrp.{u}] [HasWeakSheafify J AddCommGrp.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  (S : Cᵒᵖ ⥤ CommRingCat.{u})
  (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))

private abbrev invertibleTensorRingSheaf : Sheaf J RingCat.{u} :=
  ⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩

local instance : ∀ U, IsMulCommutative ((invertibleTensorRingSheaf S hS).val.obj U) :=
  fun U => ⟨⟨fun a b => mul_comm a b⟩⟩

set_option maxHeartbeats 800000 in
/-- Local singleton bases make the actual presheaf evaluation locally
bijective and therefore inverted by module sheafification. -/
theorem evaluationPre_mem_sheafificationW
    (M : _root_.SheafOfModules.{u} (invertibleTensorRingSheaf S hS)) [IsInvertible M] :
    PresheafOfModules.sheafificationW (𝟙 (invertibleTensorRingSheaf S hS).val) (evaluationPre S hS M) := by
  let t : LocalTrivializations (R := invertibleTensorRingSheaf S hS) M :=
    LocalTrivializations.ofIsInvertible (R := invertibleTensorRingSheaf S hS) M
  apply PresheafOfModules.sheafificationW_of_bijective_on_coversTop
    (R := invertibleTensorRingSheaf S hS)
    (evaluationPre S hS M) t.X t.coversTop
  intro i U f
  exact bijective_evaluationPre_app_of_trivialization S hS M U
    (LocalTrivializations.unitIsoOver (R := invertibleTensorRingSheaf S hS) t i f)

/-- The evaluation obtained from the sheafification adjunction is an
isomorphism for an actual locally free rank-one sheaf. -/
theorem isIso_evaluationSheafified
    (M : _root_.SheafOfModules.{u} (invertibleTensorRingSheaf S hS)) [IsInvertible M] :
    IsIso (evaluationSheafified S hS M) := by
  haveI : IsIso ((PresheafOfModules.sheafification (𝟙 (invertibleTensorRingSheaf S hS).val)).map
      (evaluationPre S hS M)) :=
    (PresheafOfModules.sheafificationW_iff (𝟙 (invertibleTensorRingSheaf S hS).val) (evaluationPre S hS M)).mp
      (evaluationPre_mem_sheafificationW S hS M)
  rw [evaluationSheafified_eq_sheafification_map]
  infer_instance

/-- Evaluation on the actual localized tensor is an isomorphism. -/
theorem isIso_evaluation (M : _root_.SheafOfModules.{u} (invertibleTensorRingSheaf S hS)) [IsInvertible M] :
    letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    IsIso (evaluation S hS M) := by
  letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  letI := isIso_evaluationSheafified S hS M
  change IsIso ((PresheafOfModules.sheafTensorIsoSheafification S hS M
    (dual (invertibleTensorRingSheaf S hS) M)).hom ≫ evaluationSheafified S hS M)
  infer_instance

/-- The actual tensor-dual evaluation isomorphism, with its original
evaluation morphism as the forward map. -/
noncomputable def evaluationIso (M : _root_.SheafOfModules.{u} (invertibleTensorRingSheaf S hS)) [IsInvertible M] :
    letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    M ⊗ dual (invertibleTensorRingSheaf S hS) M ≅ _root_.SheafOfModules.unit (invertibleTensorRingSheaf S hS) := by
  letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  letI := isIso_evaluation S hS M
  exact asIso (evaluation S hS M)

/-- The sheaf dual is a tensor inverse, with the actual monoidal unit
identified by the established sheafification counit. -/
noncomputable def tensorDualIsoUnit (M : _root_.SheafOfModules.{u} (invertibleTensorRingSheaf S hS)) [IsInvertible M] :
    letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    M ⊗ dual (invertibleTensorRingSheaf S hS) M ≅ 𝟙_ (_root_.SheafOfModules.{u} (invertibleTensorRingSheaf S hS)) := by
  letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  exact evaluationIso S hS M ≪≫ (PresheafOfModules.sheafTensorUnitIso S hS).symm

/-- The isomorphism class of an actual locally free rank-one module
sheaf is a unit in the existing skeleton tensor monoid. -/
theorem IsInvertible.isUnit_toSkeleton
    (M : _root_.SheafOfModules.{u} (invertibleTensorRingSheaf S hS)) [IsInvertible M] :
    letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    IsUnit (toSkeleton M) := by
  letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  letI := PresheafOfModules.sheafOfModulesSymmetricCategory S hS
  refine isUnit_of_dvd_one ⟨toSkeleton (dual (invertibleTensorRingSheaf S hS) M), ?_⟩
  rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
  exact Quotient.sound ⟨(tensorDualIsoUnit S hS M).symm⟩

end Tensor

end KltDP.SheafOfModules
