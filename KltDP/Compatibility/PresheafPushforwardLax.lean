/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import KltDP.Compatibility.AdjunctionOplaxMonoidal
import KltDP.Compatibility.PresheafRestrictionTensor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback

/-!
# Lax pushforward and its actual pullback mate

Bounded port from `Vilin97/MazurTheorem`, revision
`9327963d4ec14fba49c7b14b004fd00707ffc2e9`,
`MazurTorsion/Upstream/AINTLIB/Picard/Pullback.lean`, lines 135–479.
The complete source file has SHA-256
`98174cd151ac13b0688ebd13d10445d55bbdb050fee24198fc12556294e58938`.
That source adapts Chris Birkbeck's AINTLIB construction under Apache 2.0.

Restriction of scalars uses the actual ring map on sections. Its tensor
map sends each pure tensor to the same pure tensor over the target ring.
Precomposition uses the existing `PresheafRestrictionTensor` port. The
resulting oplax maps are mates under the pinned pullback adjunction.
No invertibility of either comparison map is asserted here.

Adaptations to the pin: primed monoidal structure fields, four explicit
arguments to `TensorProduct.mapOfCompatibleSMul`, and a direct adjunction
computation in place of the newer `Adjunction.IsMonoidal` interface.
-/

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace PresheafOfModules

section RestrictScalarsLax

variable {C : Type u₁} [Category.{v₁} C] {T₁ T₂ : Cᵒᵖ ⥤ CommRingCat.{u}}
  (ψ : T₁ ⋙ forget₂ CommRingCat RingCat ⟶ T₂ ⋙ forget₂ CommRingCat RingCat)

/-- **[D-PresPB′-general], leaf B1a (unit component).** The unit comparison of the lax
monoidal structure on presheaf-level restriction of scalars, at a section: the ring map
`ψ.app U` itself, as a linear map into the restricted module. -/
noncomputable def restrictScalarsLaxεApp (U : Cᵒᵖ) :
    ((𝟙_ (PresheafOfModules.{u} (T₁ ⋙ forget₂ CommRingCat RingCat))).obj U) ⟶
      ((restrictScalars ψ).obj
        (𝟙_ (PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)))).obj U :=
  ModuleCat.ofHom
    (X := (𝟙_ (PresheafOfModules.{u} (T₁ ⋙ forget₂ CommRingCat RingCat))).obj U)
    (Y := ((restrictScalars ψ).obj
      (𝟙_ (PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)))).obj U)
    { toFun := fun x => (ψ.app U).hom x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => (ψ.app U).hom.map_mul r x }

@[simp]
lemma restrictScalarsLaxεApp_apply (U : Cᵒᵖ)
    (x : ((𝟙_ (PresheafOfModules.{u} (T₁ ⋙ forget₂ CommRingCat RingCat))).obj U)) :
    restrictScalarsLaxεApp ψ U x = (ψ.app U).hom x :=
  rfl

/-- **[D-PresPB′-general], leaf B1a (tensorator component).** The tensorator of the lax
monoidal structure on presheaf-level restriction of scalars, at a section:
`x ⊗ₜ y ↦ x ⊗ₜ y` from the tensor over the downstairs ring to the (restricted) tensor over
the upstairs ring (`TensorProduct.mapOfCompatibleSMul` — the lax direction needs no
bijectivity: the downstairs action slides in the upstairs tensor because it factors
through `ψ`). -/
noncomputable def restrictScalarsLaxμApp
    (P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ) :
    (((restrictScalars ψ).obj P ⊗ (restrictScalars ψ).obj Q).obj U) ⟶
      (((restrictScalars ψ).obj (P ⊗ Q)).obj U) := by
  letI : Module ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) :=
    Module.compHom _ ((ψ.app U).hom)
  letI : Module ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(Q.obj U) :=
    Module.compHom _ ((ψ.app U).hom)
  letI : Algebra ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U) := ((ψ.app U).hom).toAlgebra
  haveI : IsScalarTower ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) :=
    ⟨fun r s m => mul_smul ((ψ.app U).hom r) s m⟩
  haveI : IsScalarTower ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(Q.obj U) :=
    ⟨fun r s n => mul_smul ((ψ.app U).hom r) s n⟩
  haveI : SMulCommClass ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) :=
    ⟨fun s r m => by
      change s • (ψ.app U).hom r • m = (ψ.app U).hom r • s • m
      rw [smul_comm]⟩
  haveI : SMulCommClass ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) :=
    ⟨fun r r' m => by
      change (ψ.app U).hom r • (ψ.app U).hom r' • m =
        (ψ.app U).hom r' • (ψ.app U).hom r • m
      rw [smul_comm]⟩
  exact ModuleCat.ofHom
    (X := (((restrictScalars ψ).obj P ⊗ (restrictScalars ψ).obj Q).obj U))
    (Y := (((restrictScalars ψ).obj (P ⊗ Q)).obj U))
    (TensorProduct.mapOfCompatibleSMul ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) ↑(Q.obj U))

@[simp]
lemma restrictScalarsLaxμApp_tmul
    (P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ)
    (p : ↑(((restrictScalars ψ).obj P).obj U)) (q : ↑(((restrictScalars ψ).obj Q).obj U)) :
    restrictScalarsLaxμApp ψ P Q U (p ⊗ₜ q) =
      (p ⊗ₜ q : ↑(((restrictScalars ψ).obj (P ⊗ Q)).obj U)) :=
  rfl

private lemma restrictScalars_map_app_apply
    {P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)}
    (g : P ⟶ Q) (U : Cᵒᵖ) (p : ((restrictScalars ψ).obj P).obj U) :
    ((restrictScalars ψ).map g).app U p = g.app U p :=
  rfl

/-- **[D-PresPB′-general], leaf B1a (unit).** The unit comparison as a morphism of presheaves
of modules; naturality is the naturality of `ψ`. -/
noncomputable def restrictScalarsLaxε :
    (𝟙_ (PresheafOfModules.{u} (T₁ ⋙ forget₂ CommRingCat RingCat))) ⟶
      (restrictScalars ψ).obj
        (𝟙_ (PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat))) where
  app U := restrictScalarsLaxεApp ψ U
  naturality {U V} f := by
    ext
    simp only [Functor.comp_obj, CommRingCat.forgetToRingCat_obj, Functor.comp_map,
      CommRingCat.forgetToRingCat_map_hom, ModuleCat.hom_comp]
    have h := RingHom.congr_fun (congrArg RingCat.Hom.hom (ψ.naturality f)) 1
    simp only [RingCat.hom_comp, RingHom.comp_apply] at h
    exact h

/-- **[D-PresPB′-general], leaf B1a (tensorator).** The tensorator as a morphism of
presheaves of modules; naturality is a `tmul`-chase (all components are `x ⊗ₜ y ↦ x ⊗ₜ y`). -/
noncomputable def restrictScalarsLaxμ
    (P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) :
    (restrictScalars ψ).obj P ⊗ (restrictScalars ψ).obj Q ⟶
      (restrictScalars ψ).obj (P ⊗ Q) where
  app U := restrictScalarsLaxμApp ψ P Q U
  naturality {U V} f := ModuleCat.MonoidalCategory.tensor_ext (fun p q => by
    erw [Monoidal.tensorObj_map_tmul])

/-- **[D-PresPB′-general], leaf B1a.** Presheaf-level restriction of scalars along an
arbitrary morphism of `CommRingCat`-valued ring presheaves is lax monoidal (sectionwise
`x ⊗ₜ y ↦ x ⊗ₜ y`; no iso hypothesis). -/
noncomputable abbrev restrictScalarsLaxMonoidal : (restrictScalars ψ).LaxMonoidal where
  ε' := restrictScalarsLaxε ψ
  μ' P Q := restrictScalarsLaxμ ψ P Q
  μ'_natural_left {P P'} f Q := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun p q => ?_)
    rfl
  μ'_natural_right {Q Q'} P f := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun p q => ?_)
    rfl
  associativity' P Q R' := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext₃' (fun p q r => ?_)
    rfl
  left_unitality' P := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun r p => ?_)
    rfl
  right_unitality' P := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun p r => ?_)
    rfl

private lemma restrictScalarsLaxμ_app_tmul
    (P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ)
    (p : ((restrictScalars ψ).obj P).obj U) (q : ((restrictScalars ψ).obj Q).obj U) :
    letI := restrictScalarsLaxMonoidal ψ
    (Functor.LaxMonoidal.μ (restrictScalars ψ) P Q).app U (p ⊗ₜ q) =
      (p ⊗ₜ q : ((restrictScalars ψ).obj (P ⊗ Q)).obj U) :=
  rfl

end RestrictScalarsLax

section LaxPushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶
    F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat))

private lemma pushforward₀μ_app_tmul
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ)
    (x : ((pushforward₀OfCommRingCat F R).obj M).obj V)
    (y : ((pushforward₀OfCommRingCat F R).obj N).obj V) :
    (Functor.LaxMonoidal.μ (pushforward₀OfCommRingCat F R) M N).app V (x ⊗ₜ y) =
      (x ⊗ₜ y : ((pushforward₀OfCommRingCat F R).obj (M ⊗ N)).obj V) :=
  rfl

/-- The pushforward, spelled as its definitional factorization `pushforward₀ ⋙
restrictScalars` (the spelling at which both factors carry their lax monoidal structures
natively — mathlib's `pushforward₀OfCommRingCat.Monoidal` and our
`restrictScalarsLaxMonoidal`). Componentwise-identity isomorphic to `pushforward φ`. -/
noncomputable abbrev pushforwardFactored :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat) :=
  pushforward₀OfCommRingCat F R ⋙
    restrictScalars (R' := (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) φ

/-- The comparison of the pushforward with its factored spelling (componentwise the
identity). -/
noncomputable def pushforwardIsoFactored :
    pushforward.{u} φ ≅ pushforwardFactored φ :=
  NatIso.ofComponents (fun P => Iso.refl _) (fun f => by simp; rfl)

/-- The comparison with the factored pushforward is the identity natural
isomorphism after unfolding the definition of `pushforward`. -/
lemma pushforwardIsoFactored_eq_refl :
    pushforwardIsoFactored φ = Iso.refl (pushforward φ) := by
  ext P
  rfl

/-- **[D-PresPB′-general], leaf B1 (lax structure on the factored pushforward).** -/
noncomputable abbrev pushforwardFactoredLaxMonoidal : (pushforwardFactored φ).LaxMonoidal :=
  letI : (restrictScalars (R' := (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) φ).LaxMonoidal :=
    restrictScalarsLaxMonoidal (T₂ := F.op ⋙ R) φ
  inferInstanceAs ((pushforward₀OfCommRingCat F R ⋙
    restrictScalars (R' := (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) φ).LaxMonoidal)

lemma pushforwardFactoredμ_expanded_app_tmul
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ)
    (x : ((pushforwardFactored φ).obj M).obj V)
    (y : ((pushforwardFactored φ).obj N).obj V) :
    letI := restrictScalarsLaxMonoidal (T₂ := F.op ⋙ R) φ
    letI := pushforwardFactoredLaxMonoidal φ
    (((restrictScalars (R' := (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) φ).map
      (Functor.LaxMonoidal.μ (pushforward₀OfCommRingCat F R) M N)).app V)
        ((Functor.LaxMonoidal.μ (restrictScalars (R' := (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) φ)
          ((pushforward₀OfCommRingCat F R).obj M)
          ((pushforward₀OfCommRingCat F R).obj N)).app V (x ⊗ₜ y)) =
      (x ⊗ₜ y : ((pushforwardFactored φ).obj (M ⊗ N)).obj V) :=
  rfl

/-- The comparison to the factored pushforward is the identity on elements. -/
lemma pushforwardIsoFactored_hom_app_app
    (P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ)
    (x : ((pushforward.{u} φ).obj P).obj V) :
    ((pushforwardIsoFactored φ).hom.app P).app V x = x :=
  rfl

/-- The transported pullback–pushforward adjunction, against the factored spelling of the
pushforward (at which the lax monoidal structure lives natively). All doctrinal structure
maps of `pullbackOplaxMonoidal` are `homEquiv`-images under *this* adjunction. -/
noncomputable def pullbackPushforwardFactoredAdjunction
    [(pushforward.{u} φ).IsRightAdjoint] :
    pullback.{u} φ ⊣ pushforwardFactored φ :=
  (pullbackPushforwardAdjunction.{u} φ).ofNatIsoRight (pushforwardIsoFactored φ)

/-- Transporting the pullback--pushforward adjunction along the componentwise
identity factored comparison recovers the original adjunction. -/
lemma pullbackPushforwardFactoredAdjunction_eq
    [(pushforward.{u} φ).IsRightAdjoint] :
    pullbackPushforwardFactoredAdjunction φ =
      pullbackPushforwardAdjunction φ := by
  unfold pullbackPushforwardFactoredAdjunction
  rw [pushforwardIsoFactored_eq_refl]
  cases pullbackPushforwardAdjunction φ
  ext
  rfl

/-- The unit of the transported adjunction agrees elementwise with the unit of the
original pullback–pushforward adjunction (the comparison is componentwise the
identity). -/
lemma factoredAdjunction_unit_app_app [(pushforward.{u} φ).IsRightAdjoint]
    (P : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ)
    (z : P.obj V) :
    ((((pullbackPushforwardAdjunction.{u} φ).ofNatIsoRight
        (pushforwardIsoFactored φ)).unit.app P).app V) z =
      (((pullbackPushforwardAdjunction.{u} φ).unit.app P).app V) z :=
  rfl

/-- **[D-PresPB′-general], leaves B1+B2 (data form).** The oplax monoidal structure on the
presheaf pullback along an arbitrary morphism of `CommRingCat`-derived ring presheaves:
doctrinal adjunction (`Adjunction.leftAdjointOplaxMonoidal`) applied to the transported
adjunction. Its `δ_{P,Q} : f^*ᵖ(P⊗Q) ⟶ f^*ᵖP ⊗ f^*ᵖQ` is the comparison map whose
invertibility is the remaining content (leaves G1/G3). -/
noncomputable abbrev pullbackOplaxMonoidal [(pushforward.{u} φ).IsRightAdjoint] :
    (pullback.{u} φ).OplaxMonoidal :=
  letI := pushforwardFactoredLaxMonoidal φ
  (pullbackPushforwardFactoredAdjunction φ).leftAdjointOplaxMonoidal

/-- The unit comparison of the factored pushforward is the ring comparison `φ` on
elements (the `pushforward₀` unit is the identity and the `restrictScalars` one is
`φ.app` itself). -/
lemma pushforwardFactored_ε_app_apply (V : Cᵒᵖ)
    (r : (𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))).obj V) :
    letI := pushforwardFactoredLaxMonoidal φ
    (Functor.LaxMonoidal.ε (pushforwardFactored φ)).app V r =
      ((φ.app V).hom r :
        ((pushforwardFactored φ).obj
          (𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)))).obj V) :=
  rfl

/-- The tensorator of the factored pushforward is `x ⊗ₜ y ↦ x ⊗ₜ y` on elements (the
`pushforward₀` tensorator is the identity and the `restrictScalars` one is
`mapOfCompatibleSMul`). -/
lemma pushforwardFactored_μ_app_tmul
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ)
    (x : ((pushforwardFactored φ).obj M).obj V) (y : ((pushforwardFactored φ).obj N).obj V) :
    letI := pushforwardFactoredLaxMonoidal φ
    (Functor.LaxMonoidal.μ (pushforwardFactored φ) M N).app V (x ⊗ₜ y) =
      (x ⊗ₜ y : ((pushforwardFactored φ).obj (M ⊗ N)).obj V) :=
  rfl

/-- After applying the factored pushforward, the doctrinal pullback tensor comparison
sends the adjunction-unit image of a pure tensor to the pure tensor of the two
adjunction-unit images. -/
theorem pushforwardFactored_map_pullback_δ_unit_tmul
    [(pushforward.{u} φ).IsRightAdjoint]
    (P Q : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
    (V : Cᵒᵖ) (x : P.obj V) (y : Q.obj V) :
    let PB := pullback.{u} φ
    let PF := pushforwardFactored φ
    let adj := pullbackPushforwardFactoredAdjunction φ
    letI : PF.LaxMonoidal := pushforwardFactoredLaxMonoidal φ
    letI : PB.OplaxMonoidal := pullbackOplaxMonoidal φ
    ((PF.map (Functor.OplaxMonoidal.δ PB P Q)).app V)
        ((adj.unit.app (P ⊗ Q)).app V (x ⊗ₜ y)) =
      ((adj.unit.app P).app V x ⊗ₜ (adj.unit.app Q).app V y :
        (PF.obj (PB.obj P ⊗ PB.obj Q)).obj V) := by
  dsimp only
  let PB := pullback.{u} φ
  let PF := pushforwardFactored φ
  let adj := pullbackPushforwardFactoredAdjunction φ
  letI : PF.LaxMonoidal := pushforwardFactoredLaxMonoidal φ
  letI : PB.OplaxMonoidal := pullbackOplaxMonoidal φ
  have h := adj.leftAdjointOplaxMonoidal_unit_app_tensor_comp_map_δ P Q
  have hV :
      (adj.unit.app (P ⊗ Q)).app V ≫
          ((PF.map (Functor.OplaxMonoidal.δ PB P Q)).app V) =
        ((adj.unit.app P ⊗ adj.unit.app Q).app V) ≫
          ((Functor.LaxMonoidal.μ PF (PB.obj P) (PB.obj Q)).app V) := by
    simpa only [comp_app] using congrArg (fun a => a.app V) h
  have happ := congrArg (fun k => k (x ⊗ₜ y)) hV
  change
    ((PF.map (Functor.OplaxMonoidal.δ PB P Q)).app V)
        ((adj.unit.app (P ⊗ Q)).app V (x ⊗ₜ y)) =
      ((Functor.LaxMonoidal.μ PF (PB.obj P) (PB.obj Q)).app V)
        ((adj.unit.app P ⊗ adj.unit.app Q).app V (x ⊗ₜ y)) at happ
  have htensor :
      (adj.unit.app P ⊗ adj.unit.app Q).app V (x ⊗ₜ y) =
        ((adj.unit.app P).app V x ⊗ₜ (adj.unit.app Q).app V y :
          (PF.obj (PB.obj P) ⊗ PF.obj (PB.obj Q)).obj V) :=
    ModuleCat.MonoidalCategory.tensorHom_tmul
      ((adj.unit.app P).app V) ((adj.unit.app Q).app V) x y
  rw [htensor] at happ
  rw [pushforwardFactored_μ_app_tmul] at happ
  exact happ

/-- At an object mapped by the site functor, the doctrinal pullback tensor comparison
sends the adjunction-unit image of a pure tensor to the pure tensor of the two unit
images. -/
theorem pullback_δ_unit_tmul
    [(pushforward.{u} φ).IsRightAdjoint]
    (P Q : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
    (V : Cᵒᵖ) (x : P.obj V) (y : Q.obj V) :
    let PB := pullback.{u} φ
    let adj := pullbackPushforwardFactoredAdjunction φ
    letI : (pushforwardFactored φ).LaxMonoidal :=
      pushforwardFactoredLaxMonoidal φ
    letI : PB.OplaxMonoidal := pullbackOplaxMonoidal φ
    (Functor.OplaxMonoidal.δ PB P Q).app (F.op.obj V)
        (show (PB.obj (P ⊗ Q)).obj (F.op.obj V) from
          (adj.unit.app (P ⊗ Q)).app V (x ⊗ₜ y)) =
      ((show (PB.obj P).obj (F.op.obj V) from
          (adj.unit.app P).app V x) ⊗ₜ
        (show (PB.obj Q).obj (F.op.obj V) from
          (adj.unit.app Q).app V y) :
        (PB.obj P ⊗ PB.obj Q).obj (F.op.obj V)) := by
  dsimp only
  exact pushforwardFactored_map_pullback_δ_unit_tmul φ P Q V x y


end LaxPushforward

end PresheafOfModules
