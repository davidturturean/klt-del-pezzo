/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Ported from Vilin97/MazurTheorem 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/AlgebraicGeometry/SchemeModuleCohomology/LocalKilling.lean.
The source is preserved in the production reuse dossier. The pinned sheaf
projections, exact project restriction, finite product cone and compactness
API replace their modern counterparts. Degree-two/three-only wrappers are
omitted; the all-degree inductive local-killing theorem and H1 base are kept.
-/
import KltDP.Geometry.AffineCohomologyCover
import KltDP.Geometry.OpenRestrictionExtOne
import KltDP.Geometry.SeparatedAffineIntersections
import KltDP.Compatibility.GrothendieckVanishing.FlasqueVanishing
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Local killing for actual affine module cohomology

This is a source port draft. VM elaboration and the compiled dependency
audit remain pending. The recursive affine-syzygy condition is an ordinary
section-surjectivity predicate, discharged by the later degree induction.
No vanishing statement is assumed in this file.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open KltDP.Geometry.ModuleCohomology

namespace KltDP.Geometry.AffineCohomologyPort.LocalKilling

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem image_preimage_le {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (W : X.Opens) : f ''ᵁ f ⁻¹ᵁ W ≤ W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inter]
  exact inf_le_right

private theorem exists_isAffineOpen_mem_and_subset {X : Scheme.{u}}
    {W : X.Opens} {x : X} (hx : x ∈ W) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ W :=
  (Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X)) hx

private abbrev AbSheaf (X : Scheme.{u}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}

private abbrev ExtH {X : Scheme.{u}}
    (F : AbSheaf X) (n : ℕ) : Type u :=
  Abelian.Ext
    ((CategoryTheory.constantSheaf
      (Opens.grothendieckTopology X) AddCommGrp.{u}).obj
        (AddCommGrp.of (ULift ℤ))) F n

private noncomputable def openSheafPullback
    {X : Scheme.{u}} (U : X.Opens) :
    AbSheaf X ⥤ AbSheaf U :=
  OpenRestrictionExtOne.res U.ι

private noncomputable def openSheafPushforward
    {X : Scheme.{u}} (U : X.Opens) :
    AbSheaf U ⥤ AbSheaf X :=
  TopCat.Sheaf.pushforward AddCommGrp.{u} U.ι.base

private noncomputable def openRestrictionPushforward
    {X : Scheme.{u}} (U : X.Opens) :
    AbSheaf X ⥤ AbSheaf X :=
  openSheafPullback U ⋙ openSheafPushforward U

private noncomputable def openRestrictionPushforwardUnit
    {X : Scheme.{u}} (U : X.Opens) :
    𝟭 (AbSheaf X) ⟶
      openRestrictionPushforward U where
  app F :=
    { val :=
        { app V := F.1.map
            (homOfLE (image_preimage_le U.ι V.unop)).op
          naturality := by
            intro V W i
            change F.1.map i ≫ F.1.map _ =
              F.1.map _ ≫ F.1.map _
            calc
              _ = F.1.map (i ≫ _) := (F.1.map_comp _ _).symm
              _ = F.1.map (_ ≫ _) := congrArg F.1.map (Subsingleton.elim _ _)
              _ = _ := F.1.map_comp _ _ } }
  naturality F G f := by
    apply CategoryTheory.Sheaf.hom_ext
    ext V x
    change (f.val.app V ≫ G.1.map _).hom x =
      (F.1.map _ ≫ f.val.app _).hom x
    exact congrArg (fun k ↦ k.hom x)
      (f.val.naturality
        (homOfLE (image_preimage_le U.ι V.unop)).op).symm

private noncomputable def openRestrictionPushforwardSection
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X)
    (t : F.1.obj (op U)) :
    ((openRestrictionPushforward U).obj F).1.obj
      (op (⊤ : Opens X)) := by
  let W := U.ι.opensFunctor.obj
    ((Opens.map U.ι.base).obj (⊤ : Opens X))
  change F.1.obj (op W)
  have hW : W = U := by
    ext x
    simp [W]
  exact F.1.map (eqToHom hW).op t

private theorem openRestrictionPushforwardSection_map
    {X : Scheme.{u}} (U : X.Opens) {F G : AbSheaf X}
    (f : F ⟶ G) (t : F.1.obj (op U)) :
    (((openRestrictionPushforward U).map f).val.app (op (⊤ : Opens X)))
        (openRestrictionPushforwardSection U F t) =
      openRestrictionPushforwardSection U G (f.val.app (op U) t) := by
  let W := U.ι.opensFunctor.obj
    ((Opens.map U.ι.base).obj (⊤ : Opens X))
  have hW : W = U := by
    ext x
    simp [W]
  change f.val.app (op W) (F.1.map (eqToHom hW).op t) =
    G.1.map (eqToHom hW).op (f.val.app (op U) t)
  exact congrArg (fun k ↦ k.hom t)
    (f.val.naturality (eqToHom hW).op)

private theorem openRestrictionPushforwardUnit_section
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X)
    (s : F.1.obj (op (⊤ : Opens X))) :
    ((openRestrictionPushforwardUnit U).app F).val.app
        (op (⊤ : Opens X)) s =
      openRestrictionPushforwardSection U F
        (F.1.map (homOfLE le_top).op s) := by
  have hW : U.ι ''ᵁ (U.ι ⁻¹ᵁ (⊤ : Opens X)) = U := by
    ext x
    simp
  change F.1.map (homOfLE (image_preimage_le U.ι (⊤ : Opens X))).op s =
    F.1.map (eqToHom hW).op (F.1.map (homOfLE le_top).op s)
  have hk : (homOfLE (image_preimage_le U.ι (⊤ : Opens X))).op =
      (homOfLE le_top).op ≫ (eqToHom hW).op :=
    Subsingleton.elim _ _
  rw [hk, F.1.map_comp, ConcreteCategory.comp_apply]

private noncomputable def openRestrictionPushforwardHZeroOfSection
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X)
    (t : F.1.obj (op U)) :
    ExtH ((openRestrictionPushforward U).obj F) 0 :=
  (CategoryTheory.Sheaf.H.equiv₀
    ((openRestrictionPushforward U).obj F)
    (isTerminalTop : IsTerminal (⊤ : Opens X))).symm
      (openRestrictionPushforwardSection U F t)

private theorem openRestrictionPushforwardHZeroOfSection_map
    {X : Scheme.{u}} (U : X.Opens) {F G : AbSheaf X}
    (f : F ⟶ G) (t : F.1.obj (op U)) :
    (openRestrictionPushforwardHZeroOfSection U F t).comp
        (Abelian.Ext.mk₀ ((openRestrictionPushforward U).map f)) rfl =
      openRestrictionPushforwardHZeroOfSection U G
        (f.val.app (op U) t) := by
  change CategoryTheory.Sheaf.H.map
      ((openRestrictionPushforward U).map f) 0
        (openRestrictionPushforwardHZeroOfSection U F t) = _
  apply (CategoryTheory.Sheaf.H.equiv₀
    ((openRestrictionPushforward U).obj G)
    (isTerminalTop : IsTerminal (⊤ : Opens X))).injective
  rw [← CategoryTheory.Sheaf.H.equiv₀_naturality]
  dsimp [openRestrictionPushforwardHZeroOfSection]
  simp only [AddEquiv.apply_symm_apply]
  exact openRestrictionPushforwardSection_map U f t

private theorem openRestrictionPushforwardUnit_HZero
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X)
    (q : ExtH F 0) :
    q.comp (Abelian.Ext.mk₀
        ((openRestrictionPushforwardUnit U).app F)) rfl =
      openRestrictionPushforwardHZeroOfSection U F
        (F.1.map (homOfLE le_top).op
          (CategoryTheory.Sheaf.H.equiv₀ F
            (isTerminalTop : IsTerminal (⊤ : Opens X)) q)) := by
  change CategoryTheory.Sheaf.H.map
      ((openRestrictionPushforwardUnit U).app F) 0 q = _
  apply (CategoryTheory.Sheaf.H.equiv₀
    ((openRestrictionPushforward U).obj F)
    (isTerminalTop : IsTerminal (⊤ : Opens X))).injective
  rw [← CategoryTheory.Sheaf.H.equiv₀_naturality]
  dsimp [openRestrictionPushforwardHZeroOfSection]
  rw [AddEquiv.apply_symm_apply]
  exact openRestrictionPushforwardUnit_section U F _

private noncomputable instance openSheafPullback_preservesFiniteLimits
    {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (openSheafPullback U) :=
  OpenRestrictionExtOne.res_preservesFiniteLimits U.ι

private noncomputable instance openSheafPushforward_preservesFiniteLimits
    {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (openSheafPushforward U) := by
  let E₁ := openSheafPushforward U ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrp.{u}
  let E₂ := sheafToPresheaf
      (Opens.grothendieckTopology U) AddCommGrp.{u} ⋙
    TopCat.Presheaf.pushforward AddCommGrp.{u} U.ι.base
  let e : E₁ ≅ E₂ :=
    TopCat.Sheaf.pushforwardForgetIso AddCommGrp.{u} U.ι.base
  haveI : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology U)
        AddCommGrp.{u}) := by infer_instance
  haveI : PreservesFiniteLimits
      (TopCat.Presheaf.pushforward AddCommGrp.{u} U.ι.base) := by
    dsimp [TopCat.Presheaf.pushforward]
    exact ⟨fun J _ _ ↦ whiskeringLeft_preservesLimitsOfShape J _⟩
  haveI : PreservesFiniteLimits E₂ := by infer_instance
  haveI : PreservesFiniteLimits E₁ :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrp.{u})

private noncomputable instance openRestrictionPushforward_preservesFiniteLimits
    {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (openRestrictionPushforward U) := by
  letI : PreservesFiniteLimits
      (openSheafPullback U) :=
    openSheafPullback_preservesFiniteLimits U
  letI : PreservesFiniteLimits
      (openSheafPushforward U) := by
    exact openSheafPushforward_preservesFiniteLimits U
  exact comp_preservesFiniteLimits _ _

private theorem toSheaf_restrictAdjunction_unit
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map
        ((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app M) =
      (openRestrictionPushforwardUnit U).app
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := rfl

private theorem zariskiFunctor_map_restrictAdjunction_unit_eq_zero
    {X : Scheme.{u}} {n : ℕ} (U : X.Opens) (M : X.Modules) (c : H M n)
    (hc : (c.comp (Abelian.Ext.mk₀
      ((openRestrictionPushforwardUnit U).app
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))) rfl :
          ExtH ((openRestrictionPushforward U).obj
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) n) = 0) :
    (zariskiFunctor X n).map
      ((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app M) c = 0 := by
  exact hc

private theorem openRestrictionPushforward_map_mono {X : Scheme.{u}}
    (U : X.Opens)
    {F G : AbSheaf X} (f : F ⟶ G) [Mono f] :
    Mono ((openRestrictionPushforward U).map f) := by
  haveI : Mono f.val := by
    change Mono ((sheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrp.{u}).map f)
    infer_instance
  haveI hmono : Mono ((openRestrictionPushforward U).map f).val := by
    exact (NatTrans.mono_iff_mono_app _).mpr fun V ↦ by
      change Mono (f.val.app _)
      infer_instance
  exact Functor.mono_of_mono_map
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) hmono

private theorem openRestrictionPushforward_map_epi_of_affine_app_surjective
    {R : CommRingCat.{u}} (U : (Spec R).Opens) (hU : IsAffineOpen U)
    {F G : AbSheaf (Spec R)} (f : F ⟶ G)
    (hf : ∀ (W : (Spec R).Opens), IsAffineOpen W →
      Function.Surjective (f.val.app (op W))) :
    Epi ((openRestrictionPushforward U).map f) := by
  apply (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrp.{u})
    ((openRestrictionPushforward U).map f)).1
  change TopCat.Presheaf.IsLocallySurjective ((openRestrictionPushforward U).map f).val
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro W t x hxW
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
  let A := U.ι.opensFunctor.obj
    ((Opens.map U.ι.base).obj V)
  have hA : A = U ⊓ V := by
    ext y
    change (∃ z : U, z.1 ∈ V ∧ z.1 = y) ↔ y ∈ U ∧ y ∈ V
    constructor
    · rintro ⟨z, hzV, rfl⟩
      exact ⟨z.2, hzV⟩
    · rintro ⟨hyU, hyV⟩
      exact ⟨⟨y, hyU⟩, hyV, rfl⟩
  have hAaffine : IsAffineOpen A := by
    rw [hA]
    exact SeparatedAffineIntersections.isAffineOpen_inf hU hV
  let tV := ((openRestrictionPushforward U).obj G).1.map
    (homOfLE hVW).op t
  obtain ⟨s, hs⟩ := hf A hAaffine tV
  refine ⟨V, homOfLE hVW, ⟨s, ?_⟩, hxV⟩
  exact hs

private theorem openRestrictionPushforward_cokernelComparison_mono
    {X : Scheme.{u}} (U : X.Opens)
    {F G : AbSheaf X} (f : F ⟶ G) [Mono f] :
    Mono (cokernelComparison f (openRestrictionPushforward U)) := by
  let E := openRestrictionPushforward U
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.Exact := ShortComplex.exact_cokernel f
  have hT : (S.map E).Exact :=
    hS.map_of_mono_of_preservesKernel E (by infer_instance) (by infer_instance)
  dsimp [S] at hT
  change (ShortComplex.mk (E.map f) (E.map (cokernel.π f)) _).Exact at hT
  let e : cokernel (E.map f) ≅ image (E.map (cokernel.π f)) :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (E.map f))
      hT.isColimitImage
  have he_fac : cokernel.π (E.map f) ≫ e.hom =
      factorThruImage (E.map (cokernel.π f)) := by
    simpa [e] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (cokernelIsCokernel (E.map f)) hT.isColimitImage
          WalkingParallelPair.one)
  have he : cokernelComparison f E =
      e.hom ≫ image.ι (E.map (cokernel.π f)) := by
    rw [← cancel_epi (cokernel.π (E.map f))]
    rw [π_comp_cokernelComparison]
    symm
    rw [← Category.assoc, he_fac, image.fac]
  rw [he]
  infer_instance

private theorem openRestrictionPushforward_cokernelComparison_isIso_of_affine_app_surjective
    {R : CommRingCat.{u}} (U : (Spec R).Opens) (hU : IsAffineOpen U)
    {F G : AbSheaf (Spec R)} (f : F ⟶ G) [Mono f]
    (hf : ∀ (W : (Spec R).Opens), IsAffineOpen W →
      Function.Surjective ((cokernel.π f).val.app (op W))) :
    IsIso (cokernelComparison f (openRestrictionPushforward U)) := by
  let E := openRestrictionPushforward U
  let μ := cokernelComparison f E
  letI : Mono μ := by
    dsimp [μ, E]
    exact openRestrictionPushforward_cokernelComparison_mono U f
  letI : Epi (E.map (cokernel.π f)) := by
    dsimp [E]
    exact openRestrictionPushforward_map_epi_of_affine_app_surjective
      U hU (cokernel.π f) hf
  letI : Epi μ := by
    exact epi_of_epi_fac (π_comp_cokernelComparison f E)
  exact isIso_of_mono_of_epi μ

private theorem ext_postcomp_mk₀_injective_of_isIso
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    (L : C) {M N : C}
    (f : M ⟶ N) [IsIso f] (n : ℕ) :
    Function.Injective (fun c : Abelian.Ext L M n =>
      c.comp (Abelian.Ext.mk₀ f) (add_zero n)) := by
  intro x y hxy
  have hxy' := congrArg
    (fun z ↦ z.comp (Abelian.Ext.mk₀ (inv f)) rfl) hxy
  change
    (x.comp (Abelian.Ext.mk₀ f) rfl).comp
        (Abelian.Ext.mk₀ (inv f)) rfl =
      (y.comp (Abelian.Ext.mk₀ f) rfl).comp
        (Abelian.Ext.mk₀ (inv f)) rfl at hxy'
  simpa only [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, IsIso.hom_inv_id,
    Abelian.Ext.comp_mk₀_id] using hxy'

private theorem ext_comp_mk₀_eq_zero_of_isIso
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    {L M N : C} (f : M ⟶ N) [IsIso f]
    {n : ℕ} (q : Abelian.Ext L M n)
    (hq : q.comp (Abelian.Ext.mk₀ f) rfl = 0) : q = 0 :=
  ext_postcomp_mk₀_injective_of_isIso L f n
    (hq.trans (Abelian.Ext.zero_comp L n (Abelian.Ext.mk₀ f) n rfl).symm)

private theorem ext_comp_mk₀_assoc
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    {L M N P : C} {n : ℕ}
    (q : Abelian.Ext L M n) (f : M ⟶ N) (g : N ⟶ P) :
    (q.comp (Abelian.Ext.mk₀ f) rfl).comp (Abelian.Ext.mk₀ g) rfl =
      q.comp (Abelian.Ext.mk₀ (f ≫ g)) rfl := by
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

private theorem ext_boundary_naturality
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    {Z : C} {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    {n : ℕ} (q : Abelian.Ext Z S.X₃ n) :
    (q.comp hS.extClass rfl).comp (Abelian.Ext.mk₀ φ.τ₁) rfl =
      (q.comp (Abelian.Ext.mk₀ φ.τ₃) rfl).comp hT.extClass rfl := by
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero, hS.extClass_naturality hT φ]
  exact (Abelian.Ext.comp_assoc q (Abelian.Ext.mk₀ φ.τ₃) hT.extClass rfl rfl rfl).symm

private theorem ext_boundary_eq_zero_of_lift
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    {Z : C} {S : ShortComplex C}
    (hS : S.ShortExact) (q : Abelian.Ext Z S.X₃ 0) (t : Abelian.Ext Z S.X₂ 0)
    (hqt : q = t.comp (Abelian.Ext.mk₀ S.g) rfl) : q.comp hS.extClass rfl = 0 := by
  rw [hqt, Abelian.Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass, Abelian.Ext.comp_zero]

private theorem ext_postcomp_mk₀_injective_of_mono
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    (Z : C) {F G : C} (f : F ⟶ G) [Mono f] :
    Function.Injective (fun c : Abelian.Ext Z F 0 =>
      c.comp (Abelian.Ext.mk₀ f) (zero_add 0)) := by
  intro x y h
  apply Abelian.Ext.homEquiv₀.injective
  apply (cancel_mono f).mp
  apply Abelian.Ext.homEquiv₀.symm.injective
  change Abelian.Ext.mk₀ (Abelian.Ext.homEquiv₀ x ≫ f) =
    Abelian.Ext.mk₀ (Abelian.Ext.homEquiv₀ y ≫ f)
  rw [← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.mk₀_homEquiv₀_apply, Abelian.Ext.mk₀_homEquiv₀_apply]
  exact h

private theorem ext_boundary_map_zero_of_isIso
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    {Z N : C} {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (μ : T.X₃ ⟶ N) [IsIso μ] {n : ℕ}
    (c : Abelian.Ext Z S.X₁ (n + 1)) (q : Abelian.Ext Z S.X₃ n)
    (hq : q.comp hS.extClass rfl = c)
    (hqμ : q.comp (Abelian.Ext.mk₀ (φ.τ₃ ≫ μ)) rfl = 0) :
    c.comp (Abelian.Ext.mk₀ φ.τ₁) rfl = 0 := by
  have hqφ : q.comp (Abelian.Ext.mk₀ φ.τ₃) rfl = 0 :=
    ext_comp_mk₀_eq_zero_of_isIso μ _ ((ext_comp_mk₀_assoc q φ.τ₃ μ).trans hqμ)
  exact ((congrArg (fun a => a.comp (Abelian.Ext.mk₀ φ.τ₁) rfl) hq.symm).trans
    (ext_boundary_naturality hS hT φ q)).trans
      ((congrArg (fun a => a.comp hT.extClass rfl) hqφ).trans
        (Abelian.Ext.zero_comp Z n hT.extClass (n + 1) rfl))

private theorem ext_boundary_map_zero_of_lift
    {C : Type (u + 1)} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    {Z N : C} {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (μ : T.X₃ ⟶ N) [Mono μ]
    (c : Abelian.Ext Z S.X₁ 1) (q : Abelian.Ext Z S.X₃ 0)
    (hq : q.comp hS.extClass rfl = c) (t : Abelian.Ext Z T.X₂ 0)
    (ht : t.comp (Abelian.Ext.mk₀ (T.g ≫ μ)) rfl =
      q.comp (Abelian.Ext.mk₀ (φ.τ₃ ≫ μ)) rfl) :
    c.comp (Abelian.Ext.mk₀ φ.τ₁) rfl = 0 := by
  have hqφ : q.comp (Abelian.Ext.mk₀ φ.τ₃) rfl =
      t.comp (Abelian.Ext.mk₀ T.g) rfl :=
    ext_postcomp_mk₀_injective_of_mono Z μ
      ((ext_comp_mk₀_assoc q φ.τ₃ μ).trans
        (ht.symm.trans (ext_comp_mk₀_assoc t T.g μ).symm))
  exact ((congrArg (fun a => a.comp (Abelian.Ext.mk₀ φ.τ₁) rfl) hq.symm).trans
    (ext_boundary_naturality hS hT φ q)).trans
      (ext_boundary_eq_zero_of_lift hT _ t hqφ)

private noncomputable abbrev injectiveCokernelSequence
    {X : Scheme.{u}} (F : AbSheaf X) :
    ShortComplex (AbSheaf X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))

private theorem injectiveCokernelSequence_shortExact
    {X : Scheme.{u}} (F : AbSheaf X) :
    (injectiveCokernelSequence F).ShortExact := by
  letI : Mono (injectiveCokernelSequence F).f := by
    change Mono (Injective.ι F)
    infer_instance
  letI : Epi (injectiveCokernelSequence F).g := by
    change Epi (cokernel.π (Injective.ι F))
    infer_instance
  exact ShortComplex.ShortExact.mk
    (ShortComplex.exact_cokernel (Injective.ι F))

/-- The exact affine section-surjectivity data needed for a finite number of
injective-cokernel dimension shifts. -/
inductive AffineSyzygyAppSurjective {R : CommRingCat.{u}} :
    AbSheaf (Spec R) → ℕ → Prop
  | zero (F) : AffineSyzygyAppSurjective F 0
  | succ {F : AbSheaf (Spec R)} {n : ℕ}
      (head : ∀ (W : (Spec R).Opens), IsAffineOpen W →
        Function.Surjective
          ((cokernel.π (Injective.ι F)).val.app (op W)))
      (tail : AffineSyzygyAppSurjective
        (cokernel (Injective.ι F)) n) :
      AffineSyzygyAppSurjective F (n + 1)

private noncomputable abbrev openInjectiveCokernelSequence
    {X : Scheme.{u}} (U : X.Opens)
    (F : AbSheaf X) :
    ShortComplex (AbSheaf X) :=
  let E := openRestrictionPushforward U
  ShortComplex.mk (E.map (Injective.ι F))
    (cokernel.π (E.map (Injective.ι F)))
    (cokernel.condition (E.map (Injective.ι F)))

private theorem openInjectiveCokernelSequence_shortExact
    {X : Scheme.{u}} (U : X.Opens)
    (F : AbSheaf X) :
    (openInjectiveCokernelSequence U F).ShortExact := by
  letI : Mono ((openRestrictionPushforward U).map (Injective.ι F)) :=
    openRestrictionPushforward_map_mono U (Injective.ι F)
  letI : Mono (openInjectiveCokernelSequence U F).f := by
    change Mono ((openRestrictionPushforward U).map (Injective.ι F))
    infer_instance
  letI : Epi (openInjectiveCokernelSequence U F).g := by
    change Epi (cokernel.π
      ((openRestrictionPushforward U).map (Injective.ι F)))
    infer_instance
  exact ShortComplex.ShortExact.mk
    (ShortComplex.exact_cokernel
      ((openRestrictionPushforward U).map (Injective.ι F)))

private noncomputable def openInjectiveCokernelMap
    {X : Scheme.{u}} (U : X.Opens)
    (F : AbSheaf X) :
    cokernel (Injective.ι F) ⟶
      cokernel ((openRestrictionPushforward U).map (Injective.ι F)) :=
  cokernel.map (Injective.ι F)
    ((openRestrictionPushforward U).map (Injective.ι F))
    ((openRestrictionPushforwardUnit U).app F)
    ((openRestrictionPushforwardUnit U).app (Injective.under F))
    ((openRestrictionPushforwardUnit U).naturality (Injective.ι F))

private noncomputable def injectiveCokernelSequenceToOpen
    {X : Scheme.{u}} (U : X.Opens)
    (F : AbSheaf X) :
    injectiveCokernelSequence F ⟶ openInjectiveCokernelSequence U F where
  τ₁ := (openRestrictionPushforwardUnit U).app F
  τ₂ := (openRestrictionPushforwardUnit U).app (Injective.under F)
  τ₃ := openInjectiveCokernelMap U F
  comm₁₂ := by
    simpa [injectiveCokernelSequence, openInjectiveCokernelSequence] using
      ((openRestrictionPushforwardUnit U).naturality (Injective.ι F)).symm
  comm₂₃ := by
    simp [injectiveCokernelSequence, openInjectiveCokernelSequence,
      openInjectiveCokernelMap]

private theorem openInjectiveCokernelMap_comp_cokernelComparison
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X) :
    openInjectiveCokernelMap U F ≫
        cokernelComparison (Injective.ι F)
          (openRestrictionPushforward U) =
      (openRestrictionPushforwardUnit U).app
        (cokernel (Injective.ι F)) := by
  let E := openRestrictionPushforward U
  let η := openRestrictionPushforwardUnit U
  let i := Injective.ι F
  let π := cokernel.π i
  let ζ := openInjectiveCokernelMap U F
  let μ := cokernelComparison i E
  have hπζ : cokernel.π i ≫ ζ =
      η.app (Injective.under F) ≫ cokernel.π (E.map i) := by
    dsimp [ζ, η, E, i, openInjectiveCokernelMap]
    apply cokernel.π_desc
  rw [← cancel_epi (cokernel.π i)]
  calc
    cokernel.π i ≫ (ζ ≫ μ) =
        (cokernel.π i ≫ ζ) ≫ μ := Category.assoc _ _ _ |>.symm
    _ = (η.app (Injective.under F) ≫
        cokernel.π (E.map i)) ≫ μ := by rw [hπζ]
    _ = η.app (Injective.under F) ≫
        (cokernel.π (E.map i) ≫ μ) := Category.assoc _ _ _
    _ = η.app (Injective.under F) ≫ E.map π := by
      rw [π_comp_cokernelComparison]
    _ = cokernel.π i ≫ η.app (cokernel i) :=
      (η.naturality (cokernel.π i)).symm

private theorem openRestrictionPushforwardUnit_HSucc_eq_zero_of_cokernel_killed
    {X : Scheme.{u}} {F : AbSheaf X} {n : ℕ}
    (c : ExtH F (n + 1))
    (q : ExtH (cokernel (Injective.ι F)) n)
    (hq : q.comp (injectiveCokernelSequence_shortExact F).extClass rfl = c)
    (U : X.Opens)
    (hqU : q.comp (Abelian.Ext.mk₀
      ((openRestrictionPushforwardUnit U).app
        (cokernel (Injective.ι F)))) rfl = 0)
    [IsIso (cokernelComparison (Injective.ι F)
      (openRestrictionPushforward U))] :
    (c.comp (Abelian.Ext.mk₀
      ((openRestrictionPushforwardUnit U).app F)) rfl :
        ExtH ((openRestrictionPushforward U).obj F) (n + 1)) = 0 := by
  let E := openRestrictionPushforward U
  let μ := cokernelComparison (Injective.ι F) E
  let φ := injectiveCokernelSequenceToOpen U F
  have hqμ : q.comp (Abelian.Ext.mk₀ (φ.τ₃ ≫ μ)) rfl = 0 :=
    (congrArg (fun a => q.comp (Abelian.Ext.mk₀ a) rfl)
      (openInjectiveCokernelMap_comp_cokernelComparison U F)).trans hqU
  exact ext_boundary_map_zero_of_isIso
    (injectiveCokernelSequence_shortExact F)
    (openInjectiveCokernelSequence_shortExact U F) φ μ c q hq hqμ

private theorem openRestrictionPushforwardUnit_HOne_eq_zero_of_lift
    {X : Scheme.{u}} {F : AbSheaf X}
    (c : ExtH F 1)
    (q : ExtH (cokernel (Injective.ι F)) 0)
    (hq : q.comp (injectiveCokernelSequence_shortExact F).extClass rfl = c)
    (U : X.Opens)
    (t : ExtH
      ((openRestrictionPushforward U).obj (Injective.under F)) 0)
    (ht : t.comp
        (Abelian.Ext.mk₀ ((openRestrictionPushforward U).map
          (cokernel.π (Injective.ι F)))) rfl =
      q.comp (Abelian.Ext.mk₀
        ((openRestrictionPushforwardUnit U).app
          (cokernel (Injective.ι F)))) rfl) :
    (c.comp (Abelian.Ext.mk₀
      ((openRestrictionPushforwardUnit U).app F)) rfl :
        ExtH ((openRestrictionPushforward U).obj F) 1) =
      (0 : ExtH ((openRestrictionPushforward U).obj F) 1) := by
  let E := openRestrictionPushforward U
  let μ := cokernelComparison (Injective.ι F) E
  let φ := injectiveCokernelSequenceToOpen U F
  letI : Mono μ := openRestrictionPushforward_cokernelComparison_mono U (Injective.ι F)
  have htμ : t.comp (Abelian.Ext.mk₀
      ((openInjectiveCokernelSequence U F).g ≫ μ)) rfl =
      q.comp (Abelian.Ext.mk₀ (φ.τ₃ ≫ μ)) rfl :=
    (congrArg (fun a => t.comp (Abelian.Ext.mk₀ a) rfl)
      (π_comp_cokernelComparison (Injective.ι F) E)).trans
        (ht.trans (congrArg (fun a => q.comp (Abelian.Ext.mk₀ a) rfl)
          (openInjectiveCokernelMap_comp_cokernelComparison U F)).symm)
  exact ext_boundary_map_zero_of_lift
    (injectiveCokernelSequence_shortExact F)
    (openInjectiveCokernelSequence_shortExact U F) φ μ c q hq t htμ

private theorem openRestrictionPushforwardUnit_HOne_eq_zero_of_section_lift
    {X : Scheme.{u}} {F : AbSheaf X}
    (c : ExtH F 1)
    (q : ExtH (cokernel (Injective.ι F)) 0)
    (hq : q.comp (injectiveCokernelSequence_shortExact F).extClass rfl = c)
    (U : X.Opens)
    (t : (Injective.under F).1.obj (op U))
    (ht : (cokernel.π (Injective.ι F)).val.app (op U) t =
      (cokernel (Injective.ι F)).1.map (homOfLE le_top).op
        (CategoryTheory.Sheaf.H.equiv₀ (cokernel (Injective.ι F))
          (isTerminalTop : IsTerminal (⊤ : Opens X)) q)) :
    (c.comp (Abelian.Ext.mk₀
      ((openRestrictionPushforwardUnit U).app F)) rfl :
        ExtH ((openRestrictionPushforward U).obj F) 1) = 0 := by
  apply openRestrictionPushforwardUnit_HOne_eq_zero_of_lift c q hq U
    (openRestrictionPushforwardHZeroOfSection U (Injective.under F) t)
  rw [openRestrictionPushforwardHZeroOfSection_map,
    openRestrictionPushforwardUnit_HZero]
  exact congrArg
    (openRestrictionPushforwardHZeroOfSection U (cokernel (Injective.ι F))) ht

private theorem exists_injectiveCokernel_class
    {X : Scheme.{u}} {F : AbSheaf X} {n : ℕ} (c : ExtH F (n + 1)) :
    ∃ q : ExtH (cokernel (Injective.ι F)) n,
      q.comp (injectiveCokernelSequence_shortExact F).extClass rfl = c := by
  let Z := (CategoryTheory.constantSheaf
    (Opens.grothendieckTopology X) AddCommGrp.{u}).obj
      (AddCommGrp.of (ULift ℤ))
  have hc : c.comp (Abelian.Ext.mk₀ (Injective.ι F)) rfl = 0 :=
    Abelian.Ext.eq_zero_of_injective _
  exact Abelian.Ext.covariant_sequence_exact₁ Z
    (injectiveCokernelSequence_shortExact F) c hc rfl

private theorem exists_affineOpen_HOne_killing
    {X : Scheme.{u}} {F : AbSheaf X}
    (c : ExtH F 1)
    (q : ExtH (cokernel (Injective.ι F)) 0)
    (hq : q.comp (injectiveCokernelSequence_shortExact F).extClass rfl = c)
    (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      (c.comp (Abelian.Ext.mk₀
        ((openRestrictionPushforwardUnit U).app F)) rfl :
          ExtH ((openRestrictionPushforward U).obj F) 1) = 0 := by
  let π := cokernel.π (Injective.ι F)
  have hπepi : Epi π := by
    dsimp [π]
    infer_instance
  let s := CategoryTheory.Sheaf.H.equiv₀ (cokernel (Injective.ι F))
    (isTerminalTop : IsTerminal (⊤ : Opens X)) q
  have hlocal : TopCat.Presheaf.IsLocallySurjective π.val :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrp.{u}) π).2 hπepi
  have hex := (TopCat.Presheaf.isLocallySurjective_iff π.val).1 hlocal
    (⊤ : Opens X) s x (by simp)
  rcases hex with ⟨V, hVtop, hpre, hxV⟩
  rcases hpre with ⟨t, ht⟩
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  have hUV' : U ≤ V := hUV
  let tU := (Injective.under F).1.map (homOfLE hUV').op t
  have htU : π.val.app (op U) tU =
      (cokernel (Injective.ι F)).1.map (homOfLE le_top).op s := by
    have hk : hVtop.op ≫ (homOfLE hUV').op =
        (homOfLE le_top).op := Subsingleton.elim _ _
    calc
      _ = (cokernel (Injective.ι F)).1.map (homOfLE hUV').op (π.val.app (op V) t) :=
        ConcreteCategory.congr_hom (π.val.naturality (homOfLE hUV').op) t
      _ = (cokernel (Injective.ι F)).1.map (homOfLE hUV').op
          ((cokernel (Injective.ι F)).1.map hVtop.op s) :=
        congrArg (fun a => (cokernel (Injective.ι F)).1.map (homOfLE hUV').op a) ht
      _ = (cokernel (Injective.ι F)).1.map (hVtop.op ≫ (homOfLE hUV').op) s :=
        (ConcreteCategory.congr_hom ((cokernel (Injective.ι F)).1.map_comp _ _) s).symm
      _ = _ := congrArg (fun a => (cokernel (Injective.ι F)).1.map a s) hk
  refine ⟨U, hU, hxU, ?_⟩
  exact openRestrictionPushforwardUnit_HOne_eq_zero_of_section_lift
    c q hq U tU htU

private theorem exists_affineOpen_H_succ_killing_of_affine_syzygy_app_surjective
    {R : CommRingCat.{u}} {F : AbSheaf (Spec R)} (n : ℕ)
    (c : ExtH F (n + 1))
    (hsurjective : AffineSyzygyAppSurjective F n)
    (x : Spec R) :
    ∃ U : (Spec R).Opens, IsAffineOpen U ∧ x ∈ U ∧
      (c.comp (Abelian.Ext.mk₀
        ((openRestrictionPushforwardUnit U).app F)) rfl :
          ExtH ((openRestrictionPushforward U).obj F) (n + 1)) = 0 := by
  induction n generalizing F with
  | zero =>
      obtain ⟨q, hq⟩ := exists_injectiveCokernel_class (F := F) c
      exact exists_affineOpen_HOne_killing c q hq x
  | succ n ih =>
      cases hsurjective with
      | succ hfirst htail =>
          obtain ⟨q, hq⟩ := exists_injectiveCokernel_class (F := F) c
          obtain ⟨U, hU, hxU, hqU⟩ := ih q htail
          letI : IsIso (cokernelComparison (Injective.ι F)
              (openRestrictionPushforward U)) :=
            openRestrictionPushforward_cokernelComparison_isIso_of_affine_app_surjective
              U hU (Injective.ι F) hfirst
          exact ⟨U, hU, hxU,
            openRestrictionPushforwardUnit_HSucc_eq_zero_of_cokernel_killed
              c q hq U hqU⟩

private theorem zariskiFunctor_map_toAffineCoverModule_eq_zero
    {R : CommRingCat.{u}} {I : Type u} [Finite I]
    {n : ℕ} (M : (Spec R).Modules) (U : I → (Spec R).Opens) (c : H M n)
    (hc : ∀ i, (zariskiFunctor (Spec R) n).map
      ((SchemeModuleRestriction.restrictionAdjunction (U i).ι).unit.app M) c = 0) :
    (zariskiFunctor (Spec R) n).map (toAffineCoverModule M U) c = 0 := by
  let G := zariskiFunctor (Spec R) n
  let F : I → (Spec R).Modules := fun i =>
    (SchemeModuleRestriction.restriction (U i).ι ⋙ schemeModulePushforward (U i).ι).obj M
  letI : PreservesFiniteProducts G := by
    constructor
    intro k
    exact preservesProductsOfShape_of_preservesBiproductsOfShape G
  apply Concrete.isLimit_ext (Discrete.functor F ⋙ G)
    (isLimitOfPreserves G (limit.isLimit (Discrete.functor F))) _ _
  intro i
  change G.map (Pi.π F i.as) (G.map (toAffineCoverModule M U) c) = G.map (Pi.π F i.as) 0
  rw [map_zero]
  have hcomp := ConcreteCategory.congr_hom
    (G.map_comp (toAffineCoverModule M U) (Pi.π F i.as)) c
  calc
    _ = G.map (toAffineCoverModule M U ≫ Pi.π F i.as) c := hcomp.symm
    _ = 0 := (congrArg (fun a => G.map a c)
      (toAffineCoverModule_comp_pi M U i.as)).trans (hc i.as)

private theorem finite_subcover {X : Scheme.{u}} [CompactSpace X]
    {I : Type u} (U : I → X.Opens) (hU : IsOpenCover U) :
    ∃ s : Finset I, IsOpenCover (fun i : s => U i.1) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (U i : Set X)) (fun i => (U i).isOpen)
    (fun x _ => Set.mem_iUnion.mpr (hU.exists_mem x))
  refine ⟨s, IsOpenCover.mk ?_⟩
  apply le_antisymm le_top
  intro x _
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩

/-- A positive-degree class is killed on a finite affine cover from the
section-surjectivity data for the preceding injective syzygies. -/
theorem schemeHSucc_finiteAffineKillingCover_of_affine_syzygy_app_surjective
    {R : CommRingCat.{u}} (M : (Spec R).Modules) (n : ℕ)
    (c : H M (n + 1))
    (hsurjective : AffineSyzygyAppSurjective
      ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M) n) :
    ∃ (I : Type u) (U : I → (Spec R).Opens),
      Finite I ∧
      IsOpenCover U ∧
      (∀ i, IsAffine (U i)) ∧
      (∀ i, (zariskiFunctor (Spec R) (n + 1)).map
        ((SchemeModuleRestriction.restrictionAdjunction (U i).ι).unit.app M) c = 0) ∧
      (zariskiFunctor (Spec R) (n + 1)).map
        (toAffineCoverModule M U) c = 0 := by
  let F := (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M
  choose U hUaffine hxU hUkills using fun x : Spec R ↦
    exists_affineOpen_H_succ_killing_of_affine_syzygy_app_surjective
      n c hsurjective x
  have hUcover : IsOpenCover U := by
    apply IsOpenCover.mk
    apply le_antisymm le_top
    rw [← SetLike.coe_subset_coe]
    intro x hx
    rw [Opens.coe_iSup]
    exact Set.mem_iUnion.2 ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := finite_subcover U hUcover
  let V : s → (Spec R).Opens := fun i ↦ U i.1
  have hVkills (i : s) :
      (zariskiFunctor (Spec R) (n + 1)).map
        ((SchemeModuleRestriction.restrictionAdjunction (V i).ι).unit.app M) c = 0 := by
    exact zariskiFunctor_map_restrictAdjunction_unit_eq_zero
      (V i) M c (hUkills i.1)
  letI : Finite s := inferInstance
  refine ⟨s, V, inferInstance, hs, fun i ↦ hUaffine i.1,
    hVkills, ?_⟩
  exact zariskiFunctor_map_toAffineCoverModule_eq_zero M V c hVkills

/-- Every degree-one Zariski cohomology class on an affine spectrum is
killed by restriction to the members of a finite affine open cover.  The
last conclusion records the same vanishing for the induced map to the
finite product of restriction-pushforwards. -/
theorem schemeHOne_finiteAffineKillingCover
    {R : CommRingCat.{u}} (M : (Spec R).Modules) (c : H M 1) :
    ∃ (I : Type u) (U : I → (Spec R).Opens),
      Finite I ∧
      IsOpenCover U ∧
      (∀ i, IsAffine (U i)) ∧
      (∀ i, (zariskiFunctor (Spec R) 1).map
        ((SchemeModuleRestriction.restrictionAdjunction (U i).ι).unit.app M) c = 0) ∧
      (zariskiFunctor (Spec R) 1).map (toAffineCoverModule M U) c = 0 := by
  let F := (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M
  obtain ⟨q, hq⟩ := exists_injectiveCokernel_class (F := F) c
  choose U hUaffine hxU hUkills using fun x : Spec R ↦
    exists_affineOpen_HOne_killing c q hq x
  have hUcover : IsOpenCover U := by
    apply IsOpenCover.mk
    apply le_antisymm le_top
    rw [← SetLike.coe_subset_coe]
    intro x hx
    rw [Opens.coe_iSup]
    exact Set.mem_iUnion.2 ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := finite_subcover U hUcover
  let V : s → (Spec R).Opens := fun i ↦ U i.1
  have hVkills (i : s) :
      (zariskiFunctor (Spec R) 1).map
        ((SchemeModuleRestriction.restrictionAdjunction (V i).ι).unit.app M) c = 0 := by
    exact zariskiFunctor_map_restrictAdjunction_unit_eq_zero
      (V i) M c (hUkills i.1)
  letI : Finite s := inferInstance
  refine ⟨s, V, inferInstance, hs, fun i ↦ hUaffine i.1,
    hVkills, ?_⟩
  exact zariskiFunctor_map_toAffineCoverModule_eq_zero M V c hVkills

end KltDP.Geometry.AffineCohomologyPort.LocalKilling
