/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck, Joël Riou

The actual dual-sheaf construction is adapted from CBirkbeck/AINTLIB,
7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/Picard/Dual.lean, through dual_val.
The narrow over-map functors follow official Mathlib at
3edb3c0658f69f197b1e501b1f7623f3f7b3898c,
Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean.

Adaptations expose the actual pinned pushforward maps, state the unit-sheaf
composition hypotheses explicitly, use the pinned Subpresheaf names and sheaf
projections, and remove later elaborator options. No new sheaf condition is
assumed for the dual.
-/
import KltDP.Compatibility.SheafLocalBasis
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# The actual sheaf of module-linear local functionals

The dual has sections Hom_R(M|U, R|U) on the over-site of U. Its sheaf
condition follows from the ambient sheaf of additive Homs and descent of
module linearity along covering sieves. The construction uses the original
ring sheaf, module actions and restriction maps.

This module constructs the dual object. It does not assert a tensor inverse,
rank-one closure, an evaluation isomorphism or a Picard comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- Restriction along the actual over-category map. The ring comparison
is the identity after precomposition with the forgetful functors. -/
def overMap {U V : C} (f : U ⟶ V) :
    SheafOfModules.{u} (R.over V) ⥤ SheafOfModules.{u} (R.over U) :=
  pushforward (F := Over.map f) (J := J.over U) (K := J.over V) (𝟙 (R.over U))

/-- Successive restriction to V and then U agrees with restriction to U. -/
def overFunctorMap {U V : C} (f : U ⟶ V) :
    overFunctor R V ⋙ overMap R f ≅ overFunctor R U :=
  NatIso.ofComponents fun M ↦
    (fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _))

variable [∀ U : C, (J.over U).HasSheafCompose
  (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- The over-map restriction preserves the actual unit module sheaf. -/
def overMapUnitIso {U V : C} (f : U ⟶ V) :
    (overMap R f).obj (unit (R.over V)) ≅ unit (R.over U) :=
  Iso.refl _

end SheafOfModules

namespace KltDP.SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

private theorem ringMap_comp_apply {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (r : R.val.obj U) : R.val.map (f ≫ g) r = R.val.map g (R.val.map f r) :=
  CategoryTheory.congr_fun (R.val.map_comp f g) r

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- A section over `U` restricts to a section of the unit module on the over-site of
`U`. -/
noncomputable def overUnitSection (U : C) (r : R.val.obj (op U)) :
    (SheafOfModules.unit (R.over U)).sections :=
  PresheafOfModules.sectionsMk
    (fun (V : (Over U)ᵒᵖ) => R.val.map V.unop.hom.op r)
    (fun {V W : (Over U)ᵒᵖ} f => by
      change R.val.map f.unop.left.op (R.val.map V.unop.hom.op r) =
        R.val.map W.unop.hom.op r
      calc
        R.val.map f.unop.left.op (R.val.map V.unop.hom.op r) =
            R.val.map (V.unop.hom.op ≫ f.unop.left.op) r :=
          (ringMap_comp_apply R V.unop.hom.op f.unop.left.op r).symm
        _ = R.val.map W.unop.hom.op r := by
          rw [← op_comp, Over.w]
          rfl)

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})] in
@[simp]
theorem overUnitSection_apply (U : C) (r : R.val.obj (op U))
    (V : (Over U)ᵒᵖ) :
    (overUnitSection R U r).val V = R.val.map V.unop.hom.op r :=
  rfl

/-- Sections of the restricted structure sheaf on `Over U` are exactly sections on
`U`, by evaluation at the terminal object `U ⟶ U`. -/
noncomputable def overUnitSectionEquiv (U : C) :
    R.val.obj (op U) ≃ (SheafOfModules.unit (R.over U)).sections where
  toFun := overUnitSection R U
  invFun s := s.val (op (Over.mk (𝟙 U)))
  left_inv r := by
    change R.val.map (𝟙 U).op r = r
    rw [op_id, R.val.map_id]
    rfl
  right_inv s := by
    apply PresheafOfModules.sections_ext
    intro V
    change R.val.map V.unop.hom.op (s.val (op (Over.mk (𝟙 U)))) = s.val V
    exact s.property
      (Over.homMk V.unop.hom (by simp) : V.unop ⟶ Over.mk (𝟙 U)).op

/-- Multiplication by a section, as an endomorphism of the unit module on the
corresponding over-site. -/
noncomputable def overUnitScalarEnd (U : C) (r : R.val.obj (op U)) :
    End (SheafOfModules.unit (R.over U)) :=
  (SheafOfModules.unit (R.over U)).unitHomEquiv.symm (overUnitSection R U r)

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})] in
@[simp]
theorem overUnitScalarEnd_app_apply (U : C) (r : R.val.obj (op U))
    (V : (Over U)ᵒᵖ) (x : (R.over U).val.obj V) :
    (overUnitScalarEnd R U r).val.app V x =
      x * (show (R.over U).val.obj V from R.val.map V.unop.hom.op r) := by
  rfl

variable [∀ U, IsMulCommutative (R.val.obj U)]

/-- The central action of `O(U)` on the unit module over the over-site of `U`. -/
noncomputable def overUnitScalarEndRingHom (U : C) :
    R.val.obj (op U) →+* End (SheafOfModules.unit (R.over U)) where
  toFun := overUnitScalarEnd R U
  map_one' := by
    apply (SheafOfModules.forget _).map_injective
    ext V
    erw [overUnitScalarEnd_app_apply]
    rw [End.one_def]
    simp
    rfl
  map_mul' r s := by
    rw [mul_comm r s]
    apply (SheafOfModules.forget _).map_injective
    ext V
    repeat' erw [overUnitScalarEnd_app_apply]
    simp
  map_zero' := by
    apply (SheafOfModules.forget _).map_injective
    ext V
    erw [overUnitScalarEnd_app_apply]
    simp
    erw [PresheafOfModules.zero_app, ModuleCat.hom_zero]
    rfl
  map_add' r s := by
    apply (SheafOfModules.forget _).map_injective
    ext V
    repeat' erw [overUnitScalarEnd_app_apply]
    simp
    erw [SheafOfModules.add_val, PresheafOfModules.add_app, ModuleCat.hom_add]
    change _ = (overUnitScalarEnd R U r).val.app V
        (show (R.over U).val.obj V from 1) +
      (overUnitScalarEnd R U s).val.app V
        (show (R.over U).val.obj V from 1)
    rw [overUnitScalarEnd_app_apply, overUnitScalarEnd_app_apply, one_mul, one_mul]
    rfl

/-- The module structure on local linear functionals, induced by postcomposition with
scalar multiplication on the unit module. -/
noncomputable abbrev dualSectionsModule (M : _root_.SheafOfModules R) (U : C) :
    Module (R.val.obj (op U))
      (M.over U ⟶ _root_.SheafOfModules.unit (R.over U)) :=
  Module.compHom _ (overUnitScalarEndRingHom R U)

/-- Linear functionals on the restriction of `M` to the over-site of `U`. -/
noncomputable def dualSections (M : _root_.SheafOfModules R) (U : C) :
    ModuleCat (R.val.obj (op U)) :=
  letI := dualSectionsModule R M U
  ModuleCat.of _ (M.over U ⟶ _root_.SheafOfModules.unit (R.over U))

/-- Restrict a local linear functional along a morphism of the base site. -/
noncomputable def dualRestrict (M : _root_.SheafOfModules R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    M.over V.unop ⟶ _root_.SheafOfModules.unit (R.over V.unop) :=
  (_root_.SheafOfModules.overFunctorMap R f.unop).inv.app M ≫
    (_root_.SheafOfModules.overMap R f.unop).map α ≫
    (_root_.SheafOfModules.overMapUnitIso R f.unop).hom

/-- The additive internal Hom which contains the module-linear dual as a subpresheaf. -/
noncomputable def ambientDual (M : _root_.SheafOfModules R) :=
  CategoryTheory.sheafHom
    ((_root_.SheafOfModules.toSheaf R).obj M)
    ((_root_.SheafOfModules.toSheaf R).obj (_root_.SheafOfModules.unit R))

/-- Forget module-linearity from a local functional. -/
noncomputable def dualToAmbient (M : _root_.SheafOfModules R) (U : C) :
    (M.over U ⟶ _root_.SheafOfModules.unit (R.over U)) →
      (ambientDual R M).val.obj (op U) :=
  fun α ↦ (_root_.SheafOfModules.toSheaf (R.over U)).map α

omit [∀ U, IsMulCommutative (R.val.obj U)] in
theorem dualToAmbient_injective (M : _root_.SheafOfModules R) (U : C) :
    Function.Injective (dualToAmbient R M U) :=
  fun _ _ h ↦ (_root_.SheafOfModules.toSheaf (R.over U)).map_injective h

omit [∀ U, IsMulCommutative (R.val.obj U)] in
@[simp]
theorem ambientDual_map_dualToAmbient (M : _root_.SheafOfModules R)
    {U V : Cᵒᵖ} (f : U ⟶ V)
    (α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    (ambientDual R M).val.map f (dualToAmbient R M U.unop α) =
      dualToAmbient R M V.unop (dualRestrict R M f α) :=
  rfl

omit [∀ U, IsMulCommutative (R.val.obj U)] in
@[simp]
theorem dualRestrict_id (M : _root_.SheafOfModules R) (U : Cᵒᵖ)
    (α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    dualRestrict R M (𝟙 U) α = α := by
  apply dualToAmbient_injective R M U.unop
  exact congrFun ((ambientDual R M).val.map_id U) (dualToAmbient R M U.unop α)

omit [∀ U, IsMulCommutative (R.val.obj U)] in
theorem dualRestrict_comp (M : _root_.SheafOfModules R) {U V W : Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W)
    (α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    dualRestrict R M (f ≫ g) α =
      dualRestrict R M g (dualRestrict R M f α) := by
  apply dualToAmbient_injective R M W.unop
  exact congrFun ((ambientDual R M).val.map_comp f g) (dualToAmbient R M U.unop α)

omit [∀ U, IsMulCommutative (R.val.obj U)]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})] in
@[simp]
theorem dualRestrict_zero (M : _root_.SheafOfModules R) {U V : Cᵒᵖ} (f : U ⟶ V) :
    dualRestrict R M f 0 = 0 := by
  apply (_root_.SheafOfModules.forget _).map_injective
  ext W x
  rfl

omit [∀ U, IsMulCommutative (R.val.obj U)]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})] in
@[simp]
theorem dualRestrict_add (M : _root_.SheafOfModules R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (α β : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    dualRestrict R M f (α + β) = dualRestrict R M f α + dualRestrict R M f β := by
  apply (_root_.SheafOfModules.forget _).map_injective
  ext W x
  rfl

@[simp]
theorem dualRestrict_smul (M : _root_.SheafOfModules R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (r : R.val.obj U)
    (α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    letI := dualSectionsModule R M U.unop
    letI := dualSectionsModule R M V.unop
    dualRestrict R M f (r • α) = R.val.map f r • dualRestrict R M f α := by
  letI := dualSectionsModule R M U.unop
  letI := dualSectionsModule R M V.unop
  rw [show r • α = α ≫ overUnitScalarEnd R U.unop r from rfl]
  rw [show R.val.map f r • dualRestrict R M f α =
    dualRestrict R M f α ≫
      overUnitScalarEnd R V.unop (R.val.map f r) from rfl]
  apply (_root_.SheafOfModules.forget _).map_injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  dsimp [dualRestrict, _root_.SheafOfModules.overMapUnitIso,
    _root_.SheafOfModules.overMap, _root_.SheafOfModules.pushforward]
  repeat' erw [overUnitScalarEnd_app_apply]
  congr 1
  change R.val.map (W.unop.hom ≫ f.unop).op r =
    R.val.map W.unop.hom.op (R.val.map f r)
  rw [op_comp, ringMap_comp_apply R]
  simp

/-- The additive presheaf of local module-linear functionals on `M`. -/
noncomputable def dualPresheafAb (M : _root_.SheafOfModules R) : Cᵒᵖ ⥤ Ab where
  obj U := AddCommGrp.of
    (M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop))
  map {U V} f := AddCommGrp.ofHom
    { toFun := dualRestrict R M f
      map_zero' := dualRestrict_zero R M f
      map_add' := dualRestrict_add R M f }
  map_id U := by
    apply AddCommGrp.ext
    intro α
    exact dualRestrict_id R M U α
  map_comp f g := by
    apply AddCommGrp.ext
    intro α
    exact dualRestrict_comp R M f g α

/-- The presheaf of `R`-modules whose sections over `U` are the module morphisms
`M|_U → R|_U`. -/
noncomputable def dualPresheaf (M : _root_.SheafOfModules R) :
    PresheafOfModules R.val :=
  letI (U : Cᵒᵖ) : Module (R.val.obj U) ((dualPresheafAb R M).obj U) :=
    dualSectionsModule R M U.unop
  PresheafOfModules.ofPresheaf (dualPresheafAb R M)
    (fun {_ _} f r α ↦ dualRestrict_smul R M f r α)

/-- The module-linear local functionals, viewed as a subpresheaf of the additive
internal Hom. -/
noncomputable def dualSubpresheaf (M : _root_.SheafOfModules R) :
    Subpresheaf (ambientDual R M).val where
  obj U := Set.range (dualToAmbient R M U.unop)
  map f _ := by
    rintro ⟨α, rfl⟩
    exact ⟨dualRestrict R M f α, (ambientDual_map_dualToAmbient R M f α).symm⟩

omit [∀ U, IsMulCommutative (R.val.obj U)] in
/-- If a section `s` of the additive internal Hom over `U` restricts to module-linear
functionals along a `J`-covering sieve, then `s` is itself module-linear. This is the
linearity-descent step in the sheaf condition for the module-linear dual. -/
private theorem dualSubpresheaf_hom_app_smul (M : _root_.SheafOfModules R) {U : Cᵒᵖ}
    (s : (ambientDual R M).val.obj U)
    (hs : (dualSubpresheaf R M).sieveOfSection s ∈ J U.unop)
    (V : (Over U.unop)ᵒᵖ) (r : (R.over U.unop).val.obj V)
    (m : (M.over U.unop).val.obj V) :
    s.val.app V (r • m) =
      r • (show (_root_.SheafOfModules.unit (R.over U.unop)).val.obj V from
        s.val.app V m) := by
  let T : Sieve V.unop :=
    (Sieve.overEquiv V.unop).symm
      (Sieve.pullback (V.unop.hom) ((dualSubpresheaf R M).sieveOfSection s))
  have hT : T ∈ (J.over U.unop) V.unop :=
    J.overEquiv_symm_mem_over V.unop _ (J.pullback_stable (V.unop.hom) hs)
  apply (_root_.SheafOfModules.unit (R.over U.unop)).isSheaf.isSeparated
    V.unop T hT
  intro W i hi
  erw [← CategoryTheory.congr_fun (s.val.naturality i.op) (r • m)]
  change s.val.app (op W)
      ((M.over U.unop).val.map i.op (r • m)) =
    (_root_.SheafOfModules.unit (R.over U.unop)).val.map i.op
      (r • (show (_root_.SheafOfModules.unit (R.over U.unop)).val.obj V from
        s.val.app V m))
  rw [PresheafOfModules.map_smul, PresheafOfModules.map_smul]
  erw [← CategoryTheory.congr_fun (s.val.naturality i.op) m]
  have hi' :
      (Sieve.pullback (V.unop.hom)
        ((dualSubpresheaf R M).sieveOfSection s)) i.left :=
    (Sieve.overEquiv_symm_iff _ i).mp hi
  change (ambientDual R M).val.map (i.left ≫ V.unop.hom).op s ∈
    (dualSubpresheaf R M).obj (op W.left) at hi'
  rcases hi' with ⟨β, hβ⟩
  change s.val.app (op W)
      ((R.over U.unop).val.map i.op r • (M.over U.unop).val.map i.op m) =
    (R.over U.unop).val.map i.op r •
      (show (_root_.SheafOfModules.unit (R.over U.unop)).val.obj (op W) from
        s.val.app (op W) ((M.over U.unop).val.map i.op m))
  rw [Over.w i] at hβ
  have hβ_app := congr_arg
    (fun q => q.val.app (op (Over.mk (𝟙 W.left)))) hβ
  let r' : (R.over W.left).val.obj (op (Over.mk (𝟙 W.left))) :=
    (R.over U.unop).val.map i.op r
  let m' : (M.over W.left).val.obj (op (Over.mk (𝟙 W.left))) :=
    (M.over U.unop).val.map i.op m
  have hβ_smul := CategoryTheory.congr_fun hβ_app (r' • m')
  have hβ_m := CategoryTheory.congr_fun hβ_app m'
  have hleft_smul :
      (dualToAmbient R M W.left β).val.app (op (Over.mk (𝟙 W.left)))
          (r' • m') =
        β.val.app (op (Over.mk (𝟙 W.left))) (r' • m') := rfl
  have hleft_m :
      (dualToAmbient R M W.left β).val.app (op (Over.mk (𝟙 W.left))) m' =
        β.val.app (op (Over.mk (𝟙 W.left))) m' := rfl
  have hright_smul :
      (((ambientDual R M).val.map W.hom.op s).val.app
          (op (Over.mk (𝟙 W.left)))) (r' • m') =
        s.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (r' • m') := rfl
  have hright_m :
      (((ambientDual R M).val.map W.hom.op s).val.app
          (op (Over.mk (𝟙 W.left)))) m' =
        s.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) m' := rfl
  have hβ_canon_smul :
      β.val.app (op (Over.mk (𝟙 W.left))) (r' • m') =
        s.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (r' • m') :=
    hleft_smul.symm.trans (hβ_smul.trans hright_smul)
  have hβ_canon_m :
      β.val.app (op (Over.mk (𝟙 W.left))) m' =
        s.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) m' :=
    hleft_m.symm.trans (hβ_m.trans hright_m)
  let e : (Over.map W.hom).obj (Over.mk (𝟙 W.left)) ≅ W :=
    Over.isoMk (Iso.refl _) (by rfl)
  have hs_canon_smul :
      s.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (r' • m') = s.val.app (op W) (r' • m') := by
    have h := CategoryTheory.congr_fun (s.val.naturality e.hom.op) (r' • m')
    dsimp [e] at h
    change s.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
        (((_root_.SheafOfModules.toSheaf R).obj M).val.map (𝟙 W.left).op
          (r' • m')) =
      ((_root_.SheafOfModules.toSheaf R).obj
          (_root_.SheafOfModules.unit R)).val.map (𝟙 W.left).op
        (s.val.app (op W) (r' • m')) at h
    rw [op_id,
      ((_root_.SheafOfModules.toSheaf R).obj M).val.map_id,
      ((_root_.SheafOfModules.toSheaf R).obj
        (_root_.SheafOfModules.unit R)).val.map_id] at h
    simpa using h
  have hs_canon_m :
      s.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) m' =
        s.val.app (op W) m' := by
    have h := CategoryTheory.congr_fun (s.val.naturality e.hom.op) m'
    dsimp [e] at h
    change s.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
        (((_root_.SheafOfModules.toSheaf R).obj M).val.map (𝟙 W.left).op m') =
      ((_root_.SheafOfModules.toSheaf R).obj
          (_root_.SheafOfModules.unit R)).val.map (𝟙 W.left).op
        (s.val.app (op W) m') at h
    rw [op_id,
      ((_root_.SheafOfModules.toSheaf R).obj M).val.map_id,
      ((_root_.SheafOfModules.toSheaf R).obj
        (_root_.SheafOfModules.unit R)).val.map_id] at h
    simpa using h
  change s.val.app (op W) (r' • m') =
    r' • (show (_root_.SheafOfModules.unit (R.over W.left)).val.obj
      (op (Over.mk (𝟙 W.left))) from s.val.app (op W) m')
  rw [← hs_canon_smul, ← hs_canon_m, ← hβ_canon_smul, ← hβ_canon_m]
  exact (β.val.app (op (Over.mk (𝟙 W.left)))).hom.map_smul r' m'

omit [∀ U, IsMulCommutative (R.val.obj U)] in
/-- Module-linearity of a local functional descends along covering sieves. -/
theorem dualSubpresheaf_isSheaf (M : _root_.SheafOfModules R) :
    Presieve.IsSheaf J (dualSubpresheaf R M).toPresheaf := by
  apply ((dualSubpresheaf R M).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type J (ambientDual R M).val).mp
      (ambientDual R M).cond)).2
  intro U s hs
  let α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop) :=
    { val := PresheafOfModules.homMk s.val (dualSubpresheaf_hom_app_smul R M s hs) }
  exact ⟨α, rfl⟩

/-- Local module-linear functionals identify with the corresponding points of the
module-linear subfunctor of the additive internal Hom. -/
noncomputable def dualToSubpresheafEquiv (M : _root_.SheafOfModules R) (U : Cᵒᵖ) :
    ((dualPresheafAb R M).obj U : Type u) ≃
      (dualSubpresheaf R M).toPresheaf.obj U where
  toFun α := ⟨dualToAmbient R M U.unop α, ⟨α, rfl⟩⟩
  invFun x := x.2.choose
  left_inv α := by
    apply dualToAmbient_injective R M U.unop
    exact (Set.mem_range.mp (show dualToAmbient R M U.unop α ∈
      Set.range (dualToAmbient R M U.unop) from ⟨α, rfl⟩)).choose_spec
  right_inv x := by
    apply Subtype.ext
    exact x.2.choose_spec

/-- The underlying type-valued presheaf of local linear functionals is isomorphic to
the module-linear subfunctor of the additive internal Hom. -/
noncomputable def dualPresheafToSubpresheafIso (M : _root_.SheafOfModules R) :
    dualPresheafAb R M ⋙ forget Ab ≅ (dualSubpresheaf R M).toPresheaf :=
  NatIso.ofComponents
    (fun U ↦ (dualToSubpresheafEquiv R M U).toIso)
    (fun f ↦ by
      ext α
      apply Subtype.ext
      exact ambientDual_map_dualToAmbient R M f α)

/-- The sheaf dual `Hom_R(M, R)`. -/
noncomputable def dual (M : _root_.SheafOfModules R) :
    _root_.SheafOfModules R where
  val := dualPresheaf R M
  isSheaf := by
    apply (Presheaf.isSheaf_iff_isSheaf_forget J
      (dualPresheaf R M).presheaf (forget _)).mpr
    apply (isSheaf_iff_isSheaf_of_type J _).mpr
    exact Presieve.isSheaf_iso J (dualPresheafToSubpresheafIso R M).symm
      (dualSubpresheaf_isSheaf R M)

@[simp]
theorem dual_val (M : _root_.SheafOfModules R) :
    (dual R M).val = dualPresheaf R M :=
  rfl


end KltDP.SheafOfModules
