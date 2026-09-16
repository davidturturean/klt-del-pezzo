/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck

Adapted from CBirkbeck/AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/Picard/PicComparison.lean,
the scalar factorization, section bijection and component evaluation argument.
The component statement uses an actual over-site trivialization directly,
so no scheme pullback or restriction comparison is required.
-/
import KltDP.Compatibility.SheafDualUnit
import KltDP.Compatibility.SheafEvaluation

/-!
# Evaluation on an actual rank-one trivialization

An isomorphism from a restricted module sheaf to the unit identifies its
local linear functionals with scalar multiples of that isomorphism. The
resulting evaluation on sections and its tensor pairing are bijective.
No evaluation isomorphism is included among the hypotheses.
-/

noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.SheafOfModules

section Sections

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- Every functional on a trivial rank-one module is the scalar multiple
of its trivialization obtained by evaluation on the inverse generator. -/
theorem evalSection_factor (M : _root_.SheafOfModules R) (U : C)
    [∀ V, IsMulCommutative (R.val.obj V)]
    (ψ : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m : M.val.obj (op U)) :
    evalSection R M U φ m =
      dualUnitSectionsEquiv R U (ψ.inv ≫ φ) * evalSection R M U ψ.hom m := by
  have hφ : φ = ψ.hom ≫ (ψ.inv ≫ φ) := by rw [Iso.hom_inv_id_assoc]
  have hε : ψ.inv ≫ φ =
      overUnitScalarEnd R U (dualUnitSectionsEquiv R U (ψ.inv ≫ φ)) :=
    ((dualUnitSectionsEquiv R U).symm_apply_apply (ψ.inv ≫ φ)).symm
  calc
    evalSection R M U φ m =
        evalSection R M U (ψ.hom ≫ overUnitScalarEnd R U
          (dualUnitSectionsEquiv R U (ψ.inv ≫ φ))) m := by rw [← hε, ← hφ]
    _ = evalSection R M U (letI := dualSectionsModule R M U
          dualUnitSectionsEquiv R U (ψ.inv ≫ φ) • ψ.hom) m := rfl
    _ = dualUnitSectionsEquiv R U (ψ.inv ≫ φ) • evalSection R M U ψ.hom m :=
      evalSection_smul_left R M U ψ.hom _ m
    _ = dualUnitSectionsEquiv R U (ψ.inv ≫ φ) * evalSection R M U ψ.hom m := rfl

/-- Evaluation against a trivialization is the composite of the actual
section equivalences and the sections map of that sheaf isomorphism. -/
theorem bijective_evalSection_iso (M : _root_.SheafOfModules R) (U : C)
    (ψ : M.over U ≅ _root_.SheafOfModules.unit (R.over U)) :
    Function.Bijective (fun m => evalSection R M U ψ.hom m) := by
  have hcomp : (fun m => evalSection R M U ψ.hom m) =
      (overUnitSectionEquiv R U).symm ∘
        (fun s => _root_.SheafOfModules.sectionsMap ψ.hom s) ∘
        overSectionEquiv R M U := rfl
  rw [hcomp]
  refine Function.Bijective.comp (Equiv.bijective _)
    (Function.Bijective.comp ?_ (Equiv.bijective _))
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun s => _root_.SheafOfModules.sectionsMap ψ.inv s, fun s => ?_, fun s => ?_⟩
  · change _root_.SheafOfModules.sectionsMap ψ.inv
      (_root_.SheafOfModules.sectionsMap ψ.hom s) = s
    rw [← _root_.SheafOfModules.sectionsMap_comp, Iso.hom_inv_id,
      _root_.SheafOfModules.sectionsMap_id]
  · change _root_.SheafOfModules.sectionsMap ψ.hom
      (_root_.SheafOfModules.sectionsMap ψ.inv s) = s
    rw [← _root_.SheafOfModules.sectionsMap_comp, Iso.inv_hom_id,
      _root_.SheafOfModules.sectionsMap_id]

end Sections

section Tensor

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [J.WEqualsLocallyBijective AddCommGrp.{u}] [HasWeakSheafify J AddCommGrp.{u}]
  (S : Cᵒᵖ ⥤ CommRingCat.{u})
  (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))

private abbrev evaluationTrivializationRingSheaf : Sheaf J RingCat.{u} :=
  ⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩

local instance : ∀ U, IsMulCommutative ((evaluationTrivializationRingSheaf S hS).val.obj U) :=
  fun U => ⟨⟨fun a b => mul_comm a b⟩⟩

/-- A trivialization on the actual over-site makes the presheaf evaluation
component bijective. Its inverse sends `c` to `ψ⁻¹(c) ⊗ ψ`. -/
theorem bijective_evaluationPre_app_of_trivialization
    (M : _root_.SheafOfModules.{u} (evaluationTrivializationRingSheaf S hS)) (U : C)
    (ψ : M.over U ≅ _root_.SheafOfModules.unit ((evaluationTrivializationRingSheaf S hS).over U)) :
    Function.Bijective ((evaluationPre S hS M).app (op U)) := by
  letI := dualSectionsModule (evaluationTrivializationRingSheaf S hS) M U
  let hL : M.val.obj (op U) ≃ₗ[(evaluationTrivializationRingSheaf S hS).val.obj (op U)] (evaluationTrivializationRingSheaf S hS).val.obj (op U) :=
    LinearEquiv.ofBijective
      { toFun := fun m => evalSection (evaluationTrivializationRingSheaf S hS) M U ψ.hom m
        map_add' := fun a b => evalSection_add_right (evaluationTrivializationRingSheaf S hS) M U ψ.hom a b
        map_smul' := fun c a => evalSection_smul_right (evaluationTrivializationRingSheaf S hS) M U ψ.hom c a }
      (bijective_evalSection_iso (evaluationTrivializationRingSheaf S hS) M U ψ)
  letI : CommSemiring ((evaluationTrivializationRingSheaf S hS).val.obj (op U)) :=
    inferInstanceAs (CommSemiring (S.obj (op U)))
  letI : Module ((evaluationTrivializationRingSheaf S hS).val.obj (op U)) (M.val.obj (op U)) :=
    inferInstanceAs (Module (S.obj (op U)) (M.val.obj (op U)))
  letI : Module ((evaluationTrivializationRingSheaf S hS).val.obj (op U)) ((dual (evaluationTrivializationRingSheaf S hS) M).val.obj (op U)) :=
    inferInstanceAs (Module (S.obj (op U)) ((dual (evaluationTrivializationRingSheaf S hS) M).val.obj (op U)))
  let k : (PresheafOfModules.unit (S ⋙ forget₂ CommRingCat RingCat)).obj (op U) ⟶
      (M.val ⊗ (dual (evaluationTrivializationRingSheaf S hS) M).val :
        PresheafOfModules (S ⋙ forget₂ CommRingCat RingCat)).obj (op U) :=
    ModuleCat.ofHom
      (((TensorProduct.mk ((evaluationTrivializationRingSheaf S hS).val.obj (op U))
        (M.val.obj (op U)) ((dual (evaluationTrivializationRingSheaf S hS) M).val.obj (op U))).flip ψ.hom) ∘ₗ
        hL.symm.toLinearMap)
  have hki : k ≫ (evaluationPre S hS M).app (op U) = 𝟙 _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id,
      LinearMap.comp_apply, LinearMap.id_apply]
    exact hL.apply_symm_apply c
  have hik : (evaluationPre S hS M).app (op U) ≫ k = 𝟙 _ := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m φ => ?_
    have hc := evalSection_factor (evaluationTrivializationRingSheaf S hS) M U ψ φ m
    have hsm : hL.symm (evalSection (evaluationTrivializationRingSheaf S hS) M U φ m) =
        dualUnitSectionsEquiv (evaluationTrivializationRingSheaf S hS) U (ψ.inv ≫ φ) • m :=
      hL.injective ((hL.apply_symm_apply _).trans (hc.trans
        ((_root_.map_smul hL _ m).trans (smul_eq_mul _ _)).symm))
    have hcψ : dualUnitSectionsEquiv (evaluationTrivializationRingSheaf S hS) U (ψ.inv ≫ φ) • ψ.hom = φ := by
      change ψ.hom ≫ overUnitScalarEnd (evaluationTrivializationRingSheaf S hS) U
        (dualUnitSectionsEquiv (evaluationTrivializationRingSheaf S hS) U (ψ.inv ≫ φ)) = φ
      exact (congrArg (fun t => ψ.hom ≫ t)
        ((dualUnitSectionsEquiv (evaluationTrivializationRingSheaf S hS) U).symm_apply_apply (ψ.inv ≫ φ))).trans
          (Iso.hom_inv_id_assoc ψ φ)
    exact (congrArg (fun x => x ⊗ₜ[(evaluationTrivializationRingSheaf S hS).val.obj (op U)] ψ.hom) hsm).trans
      ((TensorProduct.smul_tmul _ m ψ.hom).trans (congrArg (fun y => m ⊗ₜ y) hcψ))
  letI : IsIso ((evaluationPre S hS M).app (op U)) := ⟨k, hik, hki⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

end Tensor

end KltDP.SheafOfModules
