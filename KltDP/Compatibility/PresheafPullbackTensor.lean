/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

Selective port of MazurTheorem 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/AINTLIB/Picard/Pullback.lean:1035-1437, retaining
AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684. The original unit proof,
full monoidal packaging, and categorical localization descent are omitted.
-/
import KltDP.Compatibility.PresheafPushforwardLax
import KltDP.Compatibility.FreePresheafTensor
import KltDP.Compatibility.PullbackFreeYoneda
import KltDP.Compatibility.FreeYonedaDetection
import KltDP.Compatibility.PresheafTensorColimits

/-!
# Tensor compatibility for the actual presheaf pullback of a scheme morphism

The oplax comparison is identified with an explicit isomorphism on free
representable pairs. The actual inverse-image map preserves intersections
of opens. The canonical free-representable presentation then extends
invertibility to every pair of module presheaves.

All functors, units, section maps and tensors are those already constructed.
No compatibility isomorphism is supplied as a premise of the scheme theorem.
-/

noncomputable section

universe v₃ u₃ u

open CategoryTheory MonoidalCategory Functor

namespace PresheafOfModules

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section PullbackFreeYonedaMonoidal

open CategoryTheory.Limits

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶
    F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat))

/-- Full evaluation of the transported adjunction unit at a free-yoneda module on an
arbitrary generator: the restriction along `h` of the corepresentability comparison's
generator image. -/
lemma factoredUnit_app_freeMk (U : C) {W : C} (h : W ⟶ U) :
    ((((pullbackPushforwardAdjunction.{u} φ).ofNatIsoRight
        (pushforwardIsoFactored φ)).unit.app
          ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))).app
          (Opposite.op W)) (ModuleCat.freeMk h) =
      ((pushforwardFactored φ).obj ((pullback.{u} φ).obj
          ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)))).map h.op
        (freeYonedaEquiv (X := F.obj U)
          (M := (pullback.{u} φ).obj
            ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)))
          ((pullbackFreeYonedaIso φ U).inv)) := by
  let η := ((pullbackPushforwardAdjunction.{u} φ).ofNatIsoRight
    (pushforwardIsoFactored φ)).unit.app
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
  have hgen : freeYonedaEquiv η =
      freeYonedaEquiv ((pullbackFreeYonedaIso φ U).inv) := by
    rw [freeYonedaEquiv_apply, freeYonedaEquiv_apply]
    have hη := factoredAdjunction_unit_app_app φ
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
      (Opposite.op U) (ModuleCat.freeMk (𝟙 U))
    have hfree := freeYonedaEquiv_unit_app φ U
    rw [freeYonedaEquiv_apply, freeYonedaEquiv_apply] at hfree
    exact hη.trans hfree
  exact (app_freeMk η h).trans (congrArg _ hgen)

/-- Evaluate the corepresentability comparison followed by the actual identity
comparison to factored pushforward before substituting large pullback objects. -/
private lemma freeYonedaEquiv_factored_homEquiv {U : C}
    {N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (g : (free (R ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj (F.obj U)) ⟶ N) :
    freeYonedaEquiv
      ((pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ U).homEquiv g ≫
        (pushforwardIsoFactored φ).hom.app N) = freeYonedaEquiv g := by
  rw [freeYonedaEquiv_comp, pushforwardIsoFactored_hom_app_app,
    freeYonedaEquiv_apply]
  exact corepresentableBy_homEquiv_app_generator φ g

/-- The doctrinal tensor comparison in the first variable, as a natural transformation. -/
noncomputable def δRightNat [(pushforward.{u} φ).IsRightAdjoint]
    (Q : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    (MonoidalCategory.tensorRight Q ⋙ pullback.{u} φ) ⟶
      pullback.{u} φ ⋙ MonoidalCategory.tensorRight ((pullback.{u} φ).obj Q) :=
  letI := pullbackOplaxMonoidal φ
  { app := fun P => Functor.OplaxMonoidal.δ (pullback.{u} φ) P Q
    naturality := fun {_P _P'} g =>
      (Functor.OplaxMonoidal.δ_natural_left (pullback.{u} φ) g Q).symm }

/-- The doctrinal tensor comparison in the second variable, as a natural transformation. -/
noncomputable def δLeftNat [(pushforward.{u} φ).IsRightAdjoint]
    (P : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    (MonoidalCategory.tensorLeft P ⋙ pullback.{u} φ) ⟶
      pullback.{u} φ ⋙ MonoidalCategory.tensorLeft ((pullback.{u} φ).obj P) :=
  letI := pullbackOplaxMonoidal φ
  { app := fun Q => Functor.OplaxMonoidal.δ (pullback.{u} φ) P Q
    naturality := fun {_Q _Q'} g =>
      (Functor.OplaxMonoidal.δ_natural_right (pullback.{u} φ) P g).symm }

/-- **[D-PresPB′-general], leaf G3 (generic extension).** If the doctrinal tensor
comparison of the presheaf pullback is invertible on free-yoneda pairs, it is invertible
on all pairs: extend along the canonical free-yoneda presentation in each variable in
turn, using that both sides are compositions of colimit-preserving functors
(`pullback` is a left adjoint; tensoring preserves colimits pointwise). -/
theorem isIso_pullback_δ_of_freeYoneda [(pushforward.{u} φ).IsRightAdjoint]
    (hbase : ∀ X₁ X₂ : C,
      letI := pullbackOplaxMonoidal φ
      IsIso (Functor.OplaxMonoidal.δ (pullback.{u} φ)
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₁))
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂))))
    (P Q : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    letI := pullbackOplaxMonoidal φ
    IsIso (Functor.OplaxMonoidal.δ (pullback.{u} φ) P Q) := by
  letI := pullbackOplaxMonoidal φ
  haveI hpb : PreservesColimitsOfSize.{u, u} (pullback.{u} φ) :=
    (pullbackPushforwardAdjunction.{u} φ).leftAdjoint_preservesColimits
  haveI hpb0 : PreservesColimitsOfShape WalkingParallelPair (pullback.{u} φ) :=
    ((pullbackPushforwardAdjunction.{u} φ).leftAdjoint_preservesColimits :
      PreservesColimitsOfSize.{0, 0} (pullback.{u} φ)).preservesColimitsOfShape
  have pass1 : ∀ (P' : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) (X₂ : C),
      IsIso (Functor.OplaxMonoidal.δ (pullback.{u} φ) P'
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂))) := by
    intro P' X₂
    haveI := preservesColimitsOfSize_tensorRight_aux
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂))
    haveI := preservesColimitsOfSize_tensorRight_aux
      ((pullback.{u} φ).obj ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂)))
    haveI := preservesColimitsOfShape_tensorRight
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂))
      WalkingParallelPair
    haveI := preservesColimitsOfShape_tensorRight
      ((pullback.{u} φ).obj ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂)))
      WalkingParallelPair
    exact isIso_app_of_isIso_app_freeYoneda (δRightNat φ
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X₂)))
      (fun X₁ => hbase X₁ X₂) P'
  haveI := preservesColimitsOfSize_tensorLeft_aux P
  haveI := preservesColimitsOfSize_tensorLeft_aux ((pullback.{u} φ).obj P)
  haveI := preservesColimitsOfShape_tensorLeft P WalkingParallelPair
  haveI := preservesColimitsOfShape_tensorLeft ((pullback.{u} φ).obj P)
    WalkingParallelPair
  exact isIso_app_of_isIso_app_freeYoneda (δLeftNat φ P) (fun X₂ => pass1 P X₂) Q

end PullbackFreeYonedaMonoidal

section SchemePullbackMonoidal

open AlgebraicGeometry TopologicalSpace

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)

/-- The comparison morphism of `RingCat`-valued structure presheaves induced by a scheme
morphism `f : Y ⟶ X`, spelled at the `CommRingCat`-derived clothing
`X.sheaf.val ⋙ forget₂ CommRingCat RingCat ⟶ (Opens.map f.base).op ⋙ (Y.sheaf.val ⋙ …)`
at which the presheaf-of-modules monoidal structures are found by instance search on both
sides of the pullback. -/
noncomputable def schemeRingPresheafHom :
    (X.sheaf.val ⋙ forget₂ CommRingCat RingCat :
        (Opens ↥X)ᵒᵖ ⥤ RingCat.{u}) ⟶
      (Opens.map f.base).op ⋙ (Y.sheaf.val ⋙ forget₂ CommRingCat RingCat) :=
  CategoryTheory.whiskerRight f.c (forget₂ CommRingCat RingCat)

/-- Generator evaluation of the lattice-miracle isomorphism: the inverse sends the
generator of `freeY (U₁ ⊓ U₂)` to the tensor of the two restricted generators. -/
lemma freeYonedaTensorIso_inv_app_generator (U₁ U₂ : X.Opens) :
    (freeYonedaTensorIso U₁ U₂).inv.app (Opposite.op (U₁ ⊓ U₂))
        (ModuleCat.freeMk (𝟙 (U₁ ⊓ U₂))) =
      (ModuleCat.freeMk (homOfLE inf_le_left) ⊗ₜ ModuleCat.freeMk (homOfLE inf_le_right) :
        (((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁) ⊗
          (free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂)).obj
            (Opposite.op (U₁ ⊓ U₂)))) := by
  change ((freeTensorIso X.sheaf.val (yoneda.obj U₁) (yoneda.obj U₂)).hom.app _
    (((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).map
      (yonedaMeetIso U₁ U₂).inv).app _ (ModuleCat.freeMk (𝟙 (U₁ ⊓ U₂))))) = _
  rw [free_map_app_freeMk]
  change (freeTensorDesc X.sheaf.val (yoneda.obj U₁) (yoneda.obj U₂)).app _ _ = _
  rw [freeTensorDesc_app]
  erw [freeTensorμ_inv_freeMk]
  rfl

/-- Evaluate an isomorphism composite before specializing to the pullback objects.
This keeps the generator chase from searching through the concrete category instances
of the expanded tensor and pullback constructions. -/
private lemma isoTrans_hom_app_apply {C : Type u} [SmallCategory C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {P Q N : PresheafOfModules.{u} R}
    (e : P ≅ Q) (e' : Q ≅ N) (V : Cᵒᵖ) (x : P.obj V) :
    (e.trans e').hom.app V x = e'.hom.app V (e.hom.app V x) :=
  rfl

private theorem freeYonedaEquiv_pullbackδ_canonical (U₁ U₂ : X.Opens) :
    letI := pushforwardFactoredLaxMonoidal (schemeRingPresheafHom f)
    freeYonedaEquiv
      ((freeYonedaTensorIso U₁ U₂).inv ≫
        (((pullbackPushforwardFactoredAdjunction
              (schemeRingPresheafHom f)).unit.app
            ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj
              (yoneda.obj U₁)) ⊗
          (pullbackPushforwardFactoredAdjunction
              (schemeRingPresheafHom f)).unit.app
            ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj
              (yoneda.obj U₂))) ≫
        Functor.LaxMonoidal.μ (pushforwardFactored (schemeRingPresheafHom f))
          ((pullback (schemeRingPresheafHom f)).obj
            ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj
              (yoneda.obj U₁)))
          ((pullback (schemeRingPresheafHom f)).obj
            ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj
              (yoneda.obj U₂))))) =
      freeYonedaEquiv
        ((pushforwardCompCoyonedaFreeYonedaCorepresentableBy
            (schemeRingPresheafHom f) (U₁ ⊓ U₂)).homEquiv
          (((freeYonedaTensorIso ((Opens.map f.base).obj U₁)
              ((Opens.map f.base).obj U₂)).symm.trans
            (MonoidalCategory.tensorIso
              (pullbackFreeYonedaIso (schemeRingPresheafHom f) U₁).symm
              (pullbackFreeYonedaIso (schemeRingPresheafHom f) U₂).symm)).hom) ≫
        (pushforwardIsoFactored (schemeRingPresheafHom f)).hom.app
          ((pullback (schemeRingPresheafHom f)).obj
              ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj
                (yoneda.obj U₁)) ⊗
            (pullback (schemeRingPresheafHom f)).obj
              ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj
                (yoneda.obj U₂)))) := by
  letI := pushforwardFactoredLaxMonoidal (schemeRingPresheafHom f)
  conv_rhs =>
    rw [freeYonedaEquiv_factored_homEquiv (schemeRingPresheafHom f)]
  rw [freeYonedaEquiv_apply, freeYonedaEquiv_apply]
  erw [comp_app, comp_app, ModuleCat.comp_apply, ModuleCat.comp_apply,
    freeYonedaTensorIso_inv_app_generator]
  have hcompose := isoTrans_hom_app_apply
    (freeYonedaTensorIso (X := Y) ((Opens.map f.base).obj U₁)
      ((Opens.map f.base).obj U₂)).symm
    (MonoidalCategory.tensorIso
      (pullbackFreeYonedaIso (schemeRingPresheafHom f) U₁).symm
      (pullbackFreeYonedaIso (schemeRingPresheafHom f) U₂).symm)
    (Opposite.op ((Opens.map f.base).obj (U₁ ⊓ U₂)))
    (ModuleCat.freeMk (𝟙 ((Opens.map f.base).obj (U₁ ⊓ U₂))))
  refine Eq.trans ?_ hcompose.symm
  rw [Iso.symm_hom, tensorIso_hom, Iso.symm_hom, Iso.symm_hom]
  have hgen : (freeYonedaTensorIso (X := Y) ((Opens.map f.base).obj U₁)
      ((Opens.map f.base).obj U₂)).inv.app
        (Opposite.op ((Opens.map f.base).obj (U₁ ⊓ U₂)))
        (ModuleCat.freeMk (𝟙 ((Opens.map f.base).obj (U₁ ⊓ U₂)))) =
      (ModuleCat.freeMk ((Opens.map f.base).map
          (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))) ⊗ₜ
        ModuleCat.freeMk ((Opens.map f.base).map
          (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂))) :
        (((free (Y.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj
            (yoneda.obj ((Opens.map f.base).obj U₁)) ⊗
          (free (Y.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj
            (yoneda.obj ((Opens.map f.base).obj U₂))).obj
              (Opposite.op ((Opens.map f.base).obj (U₁ ⊓ U₂))))) :=
    freeYonedaTensorIso_inv_app_generator (X := Y)
      ((Opens.map f.base).obj U₁) ((Opens.map f.base).obj U₂)
  erw [hgen]
  have htUnits := tensorHom_app_tmul (T := X.sheaf.val)
    ((pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).unit.app
      ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁)))
    ((pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).unit.app
      ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂)))
    (Opposite.op (U₁ ⊓ U₂))
    (ModuleCat.freeMk (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)))
    (ModuleCat.freeMk (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)))
  have htPullback := tensorHom_app_tmul (T := Y.sheaf.val)
    ((pullbackFreeYonedaIso (schemeRingPresheafHom f) U₁).inv)
    ((pullbackFreeYonedaIso (schemeRingPresheafHom f) U₂).inv)
    (Opposite.op ((Opens.map f.base).obj (U₁ ⊓ U₂)))
    (ModuleCat.freeMk ((Opens.map f.base).map
      (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))))
    (ModuleCat.freeMk ((Opens.map f.base).map
      (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂))))
  refine Eq.trans (congrArg _ htUnits) ?_
  have hu₁ := factoredUnit_app_freeMk (schemeRingPresheafHom f) U₁
    (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
  have hu₂ := factoredUnit_app_freeMk (schemeRingPresheafHom f) U₂
    (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂))
  have hι₁ := app_freeMk ((pullbackFreeYonedaIso (schemeRingPresheafHom f) U₁).inv)
    ((Opens.map f.base).map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)))
  have hι₂ := app_freeMk ((pullbackFreeYonedaIso (schemeRingPresheafHom f) U₂).inv)
    ((Opens.map f.base).map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)))
  let M₁ := (pullback.{u} (schemeRingPresheafHom f)).obj
    ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁))
  let M₂ := (pullback.{u} (schemeRingPresheafHom f)).obj
    ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂))
  let x₁ := ((pushforwardFactored (schemeRingPresheafHom f)).obj M₁).map
    (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op
    (freeYonedaEquiv (X := (Opens.map f.base).obj U₁) (M := M₁)
      ((pullbackFreeYonedaIso (schemeRingPresheafHom f) U₁).inv))
  let x₂ := ((pushforwardFactored (schemeRingPresheafHom f)).obj M₂).map
    (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op
    (freeYonedaEquiv (X := (Opens.map f.base).obj U₂) (M := M₂)
      ((pullbackFreeYonedaIso (schemeRingPresheafHom f) U₂).inv))
  refine Eq.trans (congrArg _ (congrArg₂ (fun a b => a ⊗ₜ b) hu₁ hu₂)) ?_
  refine Eq.trans (pushforwardFactoredμ_expanded_app_tmul
    (C := X.Opens) (D := Y.Opens) (F := Opens.map f.base)
    (R := Y.sheaf.val) (S := X.sheaf.val) (φ := schemeRingPresheafHom f)
    (M := M₁) (N := M₂) (V := Opposite.op (U₁ ⊓ U₂))
    (x := x₁) (y := x₂)) ?_
  exact (congrArg₂ (fun a b => a ⊗ₜ b) hι₁.symm hι₂.symm).trans htPullback.symm

/-- **[D-PresPB′-general], leaf G3-pre (δ on free-yoneda pairs).** The tensor comparison
`δ : f^*ᵖ(P ⊗ Q) ⟶ f^*ᵖP ⊗ f^*ᵖQ` of the doctrinal oplax structure on the presheaf
pullback of a scheme morphism is an isomorphism on free-yoneda pairs, *before
sheafification*: both sides are the free-yoneda on `f⁻¹(U₁ ⊓ U₂) = f⁻¹U₁ ⊓ f⁻¹U₂`
(the lattice miracle `freeYonedaTensorIso` upstairs and downstairs +
`pullbackFreeYonedaIso`), and `δ` matches the canonical isomorphism on the one
generator that determines it. -/
theorem isIso_pullback_δ_freeYoneda (U₁ U₂ : X.Opens) :
    letI := pullbackOplaxMonoidal (schemeRingPresheafHom f)
    IsIso (Functor.OplaxMonoidal.δ (pullback.{u} (schemeRingPresheafHom f))
      ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁))
      ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂))) := by
  letI := pullbackOplaxMonoidal (schemeRingPresheafHom f)
  letI := pushforwardFactoredLaxMonoidal (schemeRingPresheafHom f)
  let e := ((pullback.{u} (schemeRingPresheafHom f)).mapIso
    (freeYonedaTensorIso U₁ U₂)).trans
      ((pullbackFreeYonedaIso (schemeRingPresheafHom f) (U₁ ⊓ U₂)).trans
        ((freeYonedaTensorIso ((Opens.map f.base).obj U₁)
          ((Opens.map f.base).obj U₂)).symm.trans
            (MonoidalCategory.tensorIso
              (pullbackFreeYonedaIso (schemeRingPresheafHom f) U₁).symm
              (pullbackFreeYonedaIso (schemeRingPresheafHom f) U₂).symm)))
  have key : Functor.OplaxMonoidal.δ (pullback.{u} (schemeRingPresheafHom f))
      ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁))
      ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂)) =
      e.hom := by
    dsimp only [e]
    apply ((pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).homEquiv
      _ _).injective
    rw [show Functor.OplaxMonoidal.δ (pullback.{u} (schemeRingPresheafHom f))
        ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁))
        ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂)) =
      ((pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).homEquiv
        ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁) ⊗
          (free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂))
        ((pullback.{u} (schemeRingPresheafHom f)).obj
            ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁)) ⊗
          (pullback.{u} (schemeRingPresheafHom f)).obj
            ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂)))).symm
        (((pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).unit.app
            ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁)) ⊗
          (pullbackPushforwardFactoredAdjunction (schemeRingPresheafHom f)).unit.app
            ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂))) ≫
          Functor.LaxMonoidal.μ (pushforwardFactored (schemeRingPresheafHom f))
            ((pullback.{u} (schemeRingPresheafHom f)).obj
              ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁)))
            ((pullback.{u} (schemeRingPresheafHom f)).obj
              ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂))))
      from rfl]
    rw [Equiv.apply_symm_apply, Iso.trans_hom, Functor.mapIso_hom,
      Adjunction.homEquiv_naturality_left, ← Iso.inv_comp_eq]
    dsimp only [pullbackPushforwardFactoredAdjunction]
    erw [Adjunction.homEquiv_ofNatIsoRight_apply, Iso.trans_hom,
      homEquiv_pullbackFreeYonedaIso_hom_comp]
    apply freeYonedaEquiv.injective
    exact freeYonedaEquiv_pullbackδ_canonical f U₁ U₂
  refine ⟨e.inv, ?_, ?_⟩
  · rw [key]
    exact e.hom_inv_id
  · rw [key]
    exact e.inv_hom_id

/-- **[D-PresPB′-general], leaf G3 (scheme form, all pairs).** The doctrinal tensor
comparison of the presheaf pullback of a scheme morphism is an isomorphism on all pairs:
the free-yoneda base case is the lattice miracle (`isIso_pullback_δ_freeYoneda`), extended
along the canonical presentation by `isIso_pullback_δ_of_freeYoneda`. -/
theorem isIso_pullback_δ
    (P Q : PresheafOfModules.{u} (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) :
    letI := pullbackOplaxMonoidal (schemeRingPresheafHom f)
    IsIso (Functor.OplaxMonoidal.δ (pullback.{u} (schemeRingPresheafHom f)) P Q) :=
  isIso_pullback_δ_of_freeYoneda (schemeRingPresheafHom f)
    (fun U₁ U₂ => isIso_pullback_δ_freeYoneda f U₁ U₂) P Q

end SchemePullbackMonoidal

end PresheafOfModules
