/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Brian Nugent

Adapted from official Mathlib 5aedf732b6987e8c26ab3c9ebc855314f82b045f:
Algebra/Category/ModuleCat/Sheaf/Free.lean:194–207,
Algebra/Category/ModuleCat/Sheaf/Generators.lean:161–200,
Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:329–349,
and CategoryTheory/Sites/Over.lean (coverPreserving_over_star).
The original pinned coproduct free sheaf and Over-site restrictions are retained.
-/
import KltDP.Compatibility.SheafLocalBasis
import KltDP.Compatibility.ModulePushforwardAdjunction
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Finite generating sections on the original Over-site

A functor preserving colimits and the unit carries an actual generating family
to one with exactly the same index type. For the pinned Over restriction the
needed preservation is proved from its actual adjunction: the right adjoint
uses `Over.star` and the canonical ring restriction along `prod.snd`.

Thus finite global generators give the original `LocalGeneratorsData` and
`IsFiniteType`, without assuming any restriction-preservation conclusion.
No coherence assertion, kernel finiteness, or finite-presentation equivalence
is part of this file.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u₁ v₁ u₂ v₂

namespace SheafOfModules

section Map

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
  [HasWeakSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [HasWeakSheafify K AddCommGrp.{u}] [K.WEqualsLocallyBijective AddCommGrp.{u}]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
  [PreservesColimitsOfSize.{u, u} F]

local instance : PreservesColimitsOfSize.{0, 0} F :=
  preservesColimitsOfSize_shrink F

/-- Coproduct preservation and an actual unit isomorphism give the comparison
between the original free sheaves. -/
def mapFreeIso (I : Type u) (η : unit S ≅ F.obj (unit R)) :
    free (R := S) I ≅ F.obj (free (R := R) I) :=
  Sigma.mapIso (fun _ : I => η) ≪≫
    (PreservesCoproduct.iso F (fun _ : I => unit R)).symm

variable {F} {M : SheafOfModules.{u} R}

/-- The transported family uses the original mapped epimorphism. -/
def GeneratingSections.mapFreeHom (G : M.GeneratingSections)
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F] (η : unit S ≅ F.obj (unit R)) :
    free (R := S) G.I ⟶ F.obj M :=
  (mapFreeIso F G.I η).hom ≫ F.map G.π

/-- A genuine generating family is transported with the same index type. -/
def GeneratingSections.map (G : M.GeneratingSections)
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F] (η : unit S ≅ F.obj (unit R)) :
    (F.obj M).GeneratingSections where
  I := G.I
  s := (F.obj M).freeHomEquiv (G.mapFreeHom F η)
  epi := by
    simp only [Equiv.symm_apply_apply]
    dsimp only [GeneratingSections.mapFreeHom]
    infer_instance

@[simp]
theorem GeneratingSections.map_I (G : M.GeneratingSections)
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F] (η : unit S ≅ F.obj (unit R)) :
    (G.map F η).I = G.I := rfl

/-- The actual presentation morphism is the free comparison followed by
the mapped original presentation morphism. -/
theorem GeneratingSections.map_π_eq (G : M.GeneratingSections)
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F] (η : unit S ≅ F.obj (unit R)) :
    (G.map F η).π = (mapFreeIso F G.I η).hom ≫ F.map G.π :=
  (F.obj M).freeHomEquiv.symm_apply_apply _

end Map

section Over

variable {C : Type u₁} [Category.{u₁} C] [HasBinaryProducts C]
  (J : GrothendieckTopology C)

/-- The product functor sends covering sieves to covering sieves for the
original Over topology. -/
theorem overStar_coverPreserving (U : C) :
    CoverPreserving J (J.over U) (Over.star U) where
  cover_preserve {V S} hS := by
    refine J.superset_covering ?_
      (J.pullback_stable (prod.snd : U ⨯ V ⟶ V) hS)
    intro W f hf
    dsimp [Sieve.overEquiv]
    rw [← Presieve.functorPushforward_comp]
    refine ⟨W, f ≫ prod.snd, prod.lift (f ≫ prod.fst) (𝟙 W), hf, ?_⟩
    apply CategoryTheory.Limits.prod.hom_ext <;> simp

/-- Continuity is proved from the actual product functor, rather than
assumed when restricting generators. -/
instance overStar_isContinuous (U : C) :
    Functor.IsContinuous.{v} (Over.star U) J (J.over U) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat (J.over U) (Over.star U))
    (overStar_coverPreserving J U)

variable {J} (R : Sheaf J RingCat.{u})

private theorem overForgetStar_counit (U V : C) :
    (Over.forgetAdjStar U).counit.app V = (prod.snd : U ⨯ V ⟶ V) := by
  simp [Over.forgetAdjStar, Adjunction.comp_counit_app, coalgebraEquivOver,
    Equivalence.symm]
  change (𝟙 (U ⨯ V)) ≫ (prod.snd : U ⨯ V ⟶ V) = prod.snd
  exact Category.id_comp _

/-- The original ring sheaf maps to the pushforward of its Over restriction
by the actual section restriction along the second product projection. -/
def pushforwardOver (U : C) :
    R ⟶ ((Over.star U).sheafPushforwardContinuous RingCat.{u} J (J.over U)).obj
      (R.over U) where
  val := whiskerRight (NatTrans.op (Over.forgetAdjStar U).counit) R.val

/-- The canonical adjunction counit is the original second-projection
restriction on ring sections. -/
theorem pushforwardOver_val_app (U : C) (V : Cᵒᵖ) :
    (pushforwardOver R U).val.app V =
      R.val.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op := by
  change R.val.map ((Over.forgetAdjStar U).counit.app V.unop).op = _
  rw [overForgetStar_counit]

/-- The original Over restriction is left adjoint to the actual product-site
pushforward. Both ring compatibility equations use the original restriction maps. -/
def overPushforwardOverAdj (U : C) :
    overFunctor R U ⊣ pushforward (pushforwardOver R U) := by
  refine KltDP.SheafModuleAdjunction.pushforwardPushforwardAdj
    (F := Over.forget U) (G := Over.star U) (Over.forgetAdjStar U)
    (𝟙 (R.over U)) (pushforwardOver R U) ?_ ?_
  · ext V r
    rfl
  · ext V r
    change R.val.map ((Over.forgetAdjStar U).unit.app V.unop).left.op
      (R.val.map ((Over.forgetAdjStar U).counit.app V.unop.left).op r) = r
    change (R.val.map ((Over.forgetAdjStar U).counit.app V.unop.left).op ≫
      R.val.map ((Over.forget U).map
        ((Over.forgetAdjStar U).unit.app V.unop)).op) r = r
    rw [← Functor.map_comp, ← op_comp]
    have ht : (Over.forget U).map ((Over.forgetAdjStar U).unit.app V.unop) ≫
        (Over.forgetAdjStar U).counit.app V.unop.left = 𝟙 V.unop.left :=
      (Over.forgetAdjStar U).left_triangle_components V.unop
    have hmap := congrArg (fun a : V.unop.left ⟶ V.unop.left =>
      R.val.map a.op r) ht
    exact hmap.trans (by
      change R.val.map (𝟙 (op V.unop.left)) r = r
      exact ConcreteCategory.congr_hom (R.val.map_id (op V.unop.left)) r)

/-- Colimit and epimorphism preservation of actual Over restriction now
follow from the proved adjunction. -/
instance overFunctor_isLeftAdjoint (U : C) : (overFunctor R U).IsLeftAdjoint :=
  (overPushforwardOverAdj R U).isLeftAdjoint

variable [HasWeakSheafify J AddCommGrp.{u}]
  [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

variable {R}

/-- Original global generators restrict to the original Over-site at every
object. The cover consists of all objects and each generator index is retained. -/
def GeneratingSections.localGeneratorsData {M : SheafOfModules.{u} R}
    (G : M.GeneratingSections) : M.LocalGeneratorsData where
  I := C
  X := id
  coversTop U := by
    have h : Sieve.ofObjects (id : C → C) U = ⊤ := by
      ext V f
      exact ⟨fun _ => trivial, fun _ => ⟨V, ⟨𝟙 V⟩⟩⟩
    rw [h]
    exact J.top_mem U
  generators U := G.map (overFunctor R U) (unitOverIso (R := R) U).symm

@[simp]
theorem GeneratingSections.localGeneratorsData_generators_I {M : SheafOfModules.{u} R}
    (G : M.GeneratingSections) (U : C) :
    (G.localGeneratorsData.generators U).I = G.I := rfl

/-- Finite original global generators make the original sheaf finite type. -/
theorem GeneratingSections.isFiniteType {M : SheafOfModules.{u} R}
    (G : M.GeneratingSections) [Finite G.I] : M.IsFiniteType :=
  ⟨G.localGeneratorsData, fun _ => inferInstanceAs (Finite G.I)⟩

/-- An actual epimorphism from a finite free sheaf supplies finite type. -/
theorem isFiniteType_of_free_epi {M : SheafOfModules.{u} R}
    {I : Type u} [Finite I] (p : free (R := R) I ⟶ M) [Epi p] : M.IsFiniteType := by
  letI : Finite ((free.generatingSections I).ofEpi p).I := inferInstanceAs (Finite I)
  exact ((free.generatingSections I).ofEpi p).isFiniteType

end Over

end SheafOfModules
