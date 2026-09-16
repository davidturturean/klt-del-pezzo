/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck

Adapted from CBirkbeck/AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/Picard/Evaluation.lean.
The actual pairing and adjunction lift are retained. The tensor comparison
uses the project's proved localization tensor isomorphism.
-/
import KltDP.Compatibility.SheafDualUnit
import KltDP.Compatibility.SheafModuleMonoidal

/-!
# Evaluation against the actual sheaf dual

The sectionwise bilinear pairing gives a presheaf tensor morphism.
Module sheafification lifts it to a morphism of actual module sheaves;
the proved tensor comparison gives evaluation on the localized tensor.
No evaluation isomorphism or local rank-one condition is assumed here.
-/

noncomputable section

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

universe u

namespace KltDP.SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

private theorem moduleMap_comp_apply (M : _root_.SheafOfModules R)
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (m : M.val.obj U) :
    M.val.map (f ≫ g) m = M.val.map g (M.val.map f m) :=
  CategoryTheory.congr_fun (M.val.presheaf.map_comp f g) m

/-- A section of `M` over `U`, regarded as a section on the over-site of `U`. -/
noncomputable def overSection (M : _root_.SheafOfModules R) (U : C)
    (m : M.val.obj (op U)) : (M.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun (V : (Over U)ᵒᵖ) => M.val.map V.unop.hom.op m)
    (fun {V W : (Over U)ᵒᵖ} f => by
      change M.val.map f.unop.left.op (M.val.map V.unop.hom.op m) =
        M.val.map W.unop.hom.op m
      calc
        M.val.map f.unop.left.op (M.val.map V.unop.hom.op m) =
            M.val.map (V.unop.hom.op ≫ f.unop.left.op) m :=
          (moduleMap_comp_apply R M V.unop.hom.op f.unop.left.op m).symm
        _ = M.val.map W.unop.hom.op m := by rw [← op_comp, Over.w]; rfl)

/-- Sections on the over-site restriction are sections over the original object. -/
noncomputable def overSectionEquiv (M : _root_.SheafOfModules R) (U : C) :
    M.val.obj (op U) ≃ (M.over U).sections where
  toFun := overSection R M U
  invFun s := s.val (op (Over.mk (CategoryStruct.id U)))
  left_inv m := by
    change M.val.map (CategoryStruct.id U).op m = m
    rw [op_id, M.val.map_id]
    rfl
  right_inv s := by
    apply PresheafOfModules.sections_ext
    intro V
    change M.val.map V.unop.hom.op
      (s.val (op (Over.mk (CategoryStruct.id U)))) = s.val V
    exact s.property
      (Over.homMk V.unop.hom (by simp) : V.unop ⟶ Over.mk (𝟙 U)).op

@[simp]
theorem overSection_apply (M : _root_.SheafOfModules R) (U : C)
    (m : M.val.obj (op U)) (V : (Over U)ᵒᵖ) :
    (overSection R M U m).val V = M.val.map V.unop.hom.op m :=
  rfl

variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- Evaluate a local functional against a section of a module. -/
noncomputable def evalSection (M : _root_.SheafOfModules R) (U : C)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m : M.val.obj (op U)) : R.val.obj (op U) :=
  (overUnitSectionEquiv R U).symm
    (_root_.SheafOfModules.sectionsMap φ (overSection R M U m))

@[simp]
theorem evalSection_eq (M : _root_.SheafOfModules R) (U : C)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m : M.val.obj (op U)) :
    evalSection R M U φ m =
      φ.val.app (op (Over.mk (CategoryStruct.id U)))
        (M.val.map (CategoryStruct.id U).op m) :=
  rfl

theorem evalSection_add_right (M : _root_.SheafOfModules R) (U : C)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m m' : M.val.obj (op U)) :
    evalSection R M U φ (m + m') =
      evalSection R M U φ m + evalSection R M U φ m' := by
  simp only [evalSection_eq, map_add]

theorem evalSection_smul_right (M : _root_.SheafOfModules R) (U : C)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (r : R.val.obj (op U)) (m : M.val.obj (op U)) :
    evalSection R M U φ (r • m) = r • evalSection R M U φ m := by
  simp only [evalSection_eq]
  rw [PresheafOfModules.map_smul]
  erw [(φ.val.app (op (Over.mk (CategoryStruct.id U)))).hom.map_smul]
  congr 1
  rw [op_id, R.val.map_id]
  rfl

theorem evalSection_add_left (M : _root_.SheafOfModules R) (U : C)
    (φ ψ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m : M.val.obj (op U)) :
    evalSection R M U (φ + ψ) m =
      evalSection R M U φ m + evalSection R M U ψ m := by
  simp only [evalSection_eq]
  rfl

theorem evalSection_smul_left (M : _root_.SheafOfModules R) (U : C)
    [∀ V, IsMulCommutative (R.val.obj V)]
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (r : R.val.obj (op U)) (m : M.val.obj (op U)) :
    evalSection R M U (letI := dualSectionsModule R M U; r • φ) m =
      r • evalSection R M U φ m := by
  change evalSection R M U (φ ≫ overUnitScalarEnd R U r) m = _
  simp only [evalSection_eq]
  change
    (show R.val.obj (op U) from
      φ.val.app (op (Over.mk (CategoryStruct.id U)))
        (M.val.map (CategoryStruct.id U).op m)) *
        (show R.val.obj (op U) from
          R.val.map (CategoryStruct.id U).op r) =
      r * (show R.val.obj (op U) from
        φ.val.app (op (Over.mk (CategoryStruct.id U)))
          (M.val.map (CategoryStruct.id U).op m))
  have hr : (show R.val.obj (op U) from
      R.val.map (CategoryStruct.id U).op r) = r := by
    rw [op_id, R.val.map_id]
    rfl
  rw [hr]
  exact mul_comm _ r

/-- Evaluation commutes with restriction. -/
theorem evalSection_naturality (M : _root_.SheafOfModules R)
    {U V : Cᵒᵖ} (i : U ⟶ V)
    (φ : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop))
    (m : M.val.obj U) :
    evalSection R M V.unop (dualRestrict R M i φ) (M.val.map i m) =
      R.val.map i (evalSection R M U.unop φ m) := by
  change
    (dualRestrict R M i φ).val.app
        (op (Over.mk (CategoryStruct.id V.unop)))
        (M.val.map (CategoryStruct.id V.unop).op (M.val.map i m)) =
      R.val.map i
        (φ.val.app (op (Over.mk (CategoryStruct.id U.unop)))
          (M.val.map (CategoryStruct.id U.unop).op m))
  dsimp [dualRestrict, _root_.SheafOfModules.overMapUnitIso,
    _root_.SheafOfModules.overMap, _root_.SheafOfModules.pushforward,
    _root_.SheafOfModules.overFunctorMap]
  simp
  exact PresheafOfModules.naturality_apply φ.val
    ((Over.homMk i.unop (by
      show i.unop ≫ CategoryStruct.id (Opposite.unop U) =
        CategoryStruct.id (Opposite.unop V) ≫ i.unop
      simp) :
      (Over.map i.unop).obj
          (Over.mk (CategoryStruct.id (Opposite.unop V))) ⟶
        Over.mk (CategoryStruct.id (Opposite.unop U))).op) m

section Tensor

variable [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [HasWeakSheafify J AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  (S : Cᵒᵖ ⥤ CommRingCat.{u})
  (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))

local instance : ∀ U, IsMulCommutative ((S ⋙ forget₂ CommRingCat RingCat).obj U) :=
  fun U => ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The actual sectionwise evaluation pairing as a presheaf tensor morphism. -/
noncomputable def evaluationPre
    (M : _root_.SheafOfModules.{u}
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) :
    (M.val ⊗ (dual
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) M).val :
        PresheafOfModules (S ⋙ forget₂ CommRingCat RingCat)) ⟶
      PresheafOfModules.unit (S ⋙ forget₂ CommRingCat RingCat) where
  app U := ModuleCat.ofHom (TensorProduct.lift (by
    letI := dualSectionsModule
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) M U.unop
    letI : SMulCommClass
        ((S ⋙ forget₂ CommRingCat RingCat).obj U)
        ((S ⋙ forget₂ CommRingCat RingCat).obj U)
        ((S ⋙ forget₂ CommRingCat RingCat).obj U) :=
      ⟨fun a b c => by
        show a * (b * c) = b * (a * c)
        rw [← mul_assoc, mul_comm a b, mul_assoc]⟩
    exact LinearMap.mk₂
      ((S ⋙ forget₂ CommRingCat RingCat).obj U)
      (fun m φ => evalSection
        (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) M U.unop φ m)
      (fun m m' φ => evalSection_add_right
        (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) M U.unop φ m m')
      (fun r m φ => evalSection_smul_right
        (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) M U.unop φ r m)
      (fun m φ ψ => evalSection_add_left
        (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) M U.unop φ ψ m)
      (fun r m φ => evalSection_smul_left
        (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) M U.unop φ r m)))
  naturality {U V} i := by
    refine ModuleCat.MonoidalCategory.tensor_ext (fun m φ => ?_)
    exact evalSection_naturality
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) M i φ m

/-- On a pure tensor, evaluation is the original local functional applied
to the original section. -/
@[simp]
theorem evaluationPre_app_tmul
    (M : _root_.SheafOfModules.{u}
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}))
    (U : Cᵒᵖ) (m : M.val.obj U)
    (φ : (dual
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) M).val.obj U) :
    (evaluationPre S hS M).app U (m ⊗ₜ φ) =
      evalSection (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})
        M U.unop φ m := by
  rfl

/-- The actual sheafification adjunction lifts the presheaf pairing to
a morphism into the unit module sheaf. -/
noncomputable def evaluationSheafified
    (M : _root_.SheafOfModules.{u}
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) :
    (PresheafOfModules.sheafification
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).val)).obj
      (M.val ⊗ (dual
        (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) M).val) ⟶
      _root_.SheafOfModules.unit
        (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).val)).homEquiv
    _ (_root_.SheafOfModules.unit
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}))).symm
        (evaluationPre S hS M)

set_option maxHeartbeats 800000 in
/-- The adjunction lift is sheafification of the pairing followed by
the actual sheafification counit. -/
theorem evaluationSheafified_eq_sheafification_map
    (M : _root_.SheafOfModules.{u}
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) :
    evaluationSheafified S hS M =
      (PresheafOfModules.sheafification
        (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).val)).map
          (evaluationPre S hS M) ≫
      (PresheafOfModules.sheafificationForgetIso
        (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})
        (_root_.SheafOfModules.unit
          (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}))).hom := by
  dsimp only [evaluationSheafified, PresheafOfModules.sheafificationForgetIso,
    CategoryTheory.asIso_hom]
  rfl

/-- Evaluation on the actual localized sheaf tensor. The comparison is
the proved tensor/sheafification isomorphism, followed by the pairing. -/
noncomputable def evaluation
    (M : _root_.SheafOfModules.{u}
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) :
    letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    M ⊗ dual (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) M ⟶
      _root_.SheafOfModules.unit
        (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) := by
  letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  exact (PresheafOfModules.sheafTensorIsoSheafification S hS M
      (dual (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) M)).hom ≫
    evaluationSheafified S hS M

end Tensor

end KltDP.SheafOfModules
