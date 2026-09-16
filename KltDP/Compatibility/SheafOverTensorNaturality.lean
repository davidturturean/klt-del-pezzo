import KltDP.Compatibility.SheafRestrictionTensor
import KltDP.Compatibility.SheafTensorNaturality

/-!
# Morphism naturality of the original Over-site tensor comparison

The actual comparison `overTensorIso` is a composite of four original
isomorphisms. Naturality follows from the sheafification adjunction unit
and counit, the proved sheaf tensor comparison, and pinned monoidal
precomposition. This yields a criterion for the restriction of an actual
tensor map to be an isomorphism; no local comparison or epimorphism is
assumed for that tensor map.
-/

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace KltDP.SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

section Sheafification

variable (R : Sheaf J RingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [HasWeakSheafify J AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrp.{u}]

/-- The inverse of the original comparison is the sheafified restricted
unit followed by the original counit. -/
theorem overSheafificationIso_inv_eq (U : C) (P : _root_.PresheafOfModules.{u} R.val) :
    (overSheafificationIso R U P).inv =
      (_root_.PresheafOfModules.sheafification (𝟙 (R.over U).val)).map
        ((_root_.PresheafOfModules.pushforward₀ (Over.forget U) R.val).map
          ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.val)).unit.app P)) ≫
        (_root_.PresheafOfModules.sheafificationForgetIso (R.over U)
          (((_root_.PresheafOfModules.sheafification (𝟙 R.val)).obj P).over U)).hom := rfl

/-- Naturality of the inverse actual restriction/sheafification comparison. -/
theorem overSheafificationIso_inv_naturality (U : C)
    {P Q : _root_.PresheafOfModules.{u} R.val} (a : P ⟶ Q) :
    (_root_.PresheafOfModules.sheafification (𝟙 (R.over U).val)).map
        ((_root_.PresheafOfModules.pushforward₀ (Over.forget U) R.val).map a) ≫
        (overSheafificationIso R U Q).inv =
      (overSheafificationIso R U P).inv ≫
        (_root_.SheafOfModules.overFunctor R U).map
          ((_root_.PresheafOfModules.sheafification (𝟙 R.val)).map a) := by
  let L := _root_.PresheafOfModules.sheafification (𝟙 R.val)
  let H := _root_.PresheafOfModules.pushforward₀ (Over.forget U) R.val
  let L' := _root_.PresheafOfModules.sheafification (𝟙 (R.over U).val)
  let F := _root_.SheafOfModules.overFunctor R U
  let η := (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.val)).unit
  have hη : a ≫ η.app Q = η.app P ≫ (L.map a).val :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.val)).unit.naturality a
  have hε : L'.map (H.map (L.map a).val) ≫
      (_root_.PresheafOfModules.sheafificationForgetIso (R.over U) ((L.obj Q).over U)).hom =
    (_root_.PresheafOfModules.sheafificationForgetIso (R.over U) ((L.obj P).over U)).hom ≫
      F.map (L.map a) :=
    SheafTensorNaturality.sheafificationForgetIso_hom_naturality (R.over U)
      (F.map (L.map a))
  change L'.map (H.map a) ≫ (overSheafificationIso R U Q).inv =
    (overSheafificationIso R U P).inv ≫ F.map (L.map a)
  calc
    _ = L'.map (H.map (a ≫ η.app Q)) ≫
        (_root_.PresheafOfModules.sheafificationForgetIso (R.over U)
          ((L.obj Q).over U)).hom := by
      rw [overSheafificationIso_inv_eq]
      simp only [Functor.map_comp, Category.assoc, L, H, L', η]
    _ = L'.map (H.map (η.app P ≫ (L.map a).val)) ≫
        (_root_.PresheafOfModules.sheafificationForgetIso (R.over U)
          ((L.obj Q).over U)).hom := by rw [hη]
    _ = L'.map (H.map (η.app P)) ≫
        (L'.map (H.map (L.map a).val) ≫
          (_root_.PresheafOfModules.sheafificationForgetIso (R.over U)
            ((L.obj Q).over U)).hom) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (overSheafificationIso R U P).inv ≫ F.map (L.map a) := by
      rw [hε, overSheafificationIso_inv_eq]
      simp only [Category.assoc, L, H, L', η]

/-- Naturality of the same original comparison in the forward direction. -/
theorem overSheafificationIso_hom_naturality (U : C)
    {P Q : _root_.PresheafOfModules.{u} R.val} (a : P ⟶ Q) :
    (_root_.SheafOfModules.overFunctor R U).map
        ((_root_.PresheafOfModules.sheafification (𝟙 R.val)).map a) ≫
        (overSheafificationIso R U Q).hom =
      (overSheafificationIso R U P).hom ≫
        (_root_.PresheafOfModules.sheafification (𝟙 (R.over U).val)).map
          ((_root_.PresheafOfModules.pushforward₀ (Over.forget U) R.val).map a) := by
  apply (cancel_mono (overSheafificationIso R U Q).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    overSheafificationIso_inv_naturality, Iso.hom_inv_id_assoc]

end Sheafification

private theorem naturality_four {D : Type*} [Category D]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : D}
    {a₀ : A₀ ⟶ A₁} {a₁ : A₁ ⟶ A₂} {a₂ : A₂ ⟶ A₃} {a₃ : A₃ ⟶ A₄}
    {b₀ : B₀ ⟶ B₁} {b₁ : B₁ ⟶ B₂} {b₂ : B₂ ⟶ B₃} {b₃ : B₃ ⟶ B₄}
    {f₀ : A₀ ⟶ B₀} {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂}
    {f₃ : A₃ ⟶ B₃} {f₄ : A₄ ⟶ B₄}
    (h₀ : f₀ ≫ b₀ = a₀ ≫ f₁) (h₁ : f₁ ≫ b₁ = a₁ ≫ f₂)
    (h₂ : f₂ ≫ b₂ = a₂ ≫ f₃) (h₃ : f₃ ≫ b₃ = a₃ ≫ f₄) :
    f₀ ≫ b₀ ≫ b₁ ≫ b₂ ≫ b₃ = (a₀ ≫ a₁ ≫ a₂ ≫ a₃) ≫ f₄ := by
  calc
    _ = a₀ ≫ f₁ ≫ b₁ ≫ b₂ ≫ b₃ := by
      rw [← Category.assoc f₀ b₀, h₀]
      simp only [Category.assoc]
    _ = a₀ ≫ a₁ ≫ f₂ ≫ b₂ ≫ b₃ := by
      rw [← Category.assoc f₁ b₁, h₁]
      simp only [Category.assoc]
    _ = a₀ ≫ a₁ ≫ a₂ ≫ f₃ ≫ b₃ := by
      rw [← Category.assoc f₂ b₂, h₂]
      simp only [Category.assoc]
    _ = _ := by rw [h₃]; simp only [Category.assoc]

section Tensor

variable (S : Cᵒᵖ ⥤ CommRingCat.{u})
  (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrp.{u}] [HasWeakSheafify J AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrp.{u}]

set_option maxHeartbeats 2400000 in
/-- The accepted actual Over-site tensor comparison is natural in both
original module-sheaf morphisms. -/
theorem overTensorIso_hom_naturality (U : C)
    {M₁ M₂ N₁ N₂ : _root_.SheafOfModules.{u}
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    letI := _root_.PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    letI : MonoidalCategory (_root_.SheafOfModules.{u}
        ((⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).over U)) :=
      _root_.PresheafOfModules.sheafOfModulesMonoidalCategory
        ((Over.forget U).op ⋙ S) (overRingSheafCondition S hS U)
    (_root_.SheafOfModules.overFunctor
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) U).map (f ⊗ g) ≫
        (overTensorIso S hS U M₂ N₂).hom =
      (overTensorIso S hS U M₁ N₁).hom ≫
        ((_root_.SheafOfModules.overFunctor
          (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) U).map f ⊗
          (_root_.SheafOfModules.overFunctor
            (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) U).map g) := by
  letI := _root_.PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  letI : MonoidalCategory (_root_.SheafOfModules.{u}
      ((⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).over U)) :=
    _root_.PresheafOfModules.sheafOfModulesMonoidalCategory
      ((Over.forget U).op ⋙ S) (overRingSheafCondition S hS U)
  let R : Sheaf J RingCat.{u} := ⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩
  letI : MonoidalCategory (_root_.PresheafOfModules.{u} (R.over U).val) :=
    _root_.PresheafOfModules.monoidalCategory (R := (Over.forget U).op ⋙ S)
  let F := _root_.SheafOfModules.overFunctor R U
  let L := _root_.PresheafOfModules.sheafification (𝟙 R.val)
  let H := _root_.PresheafOfModules.pushforward₀OfCommRingCat (Over.forget U) S
  let L' := _root_.PresheafOfModules.sheafification (𝟙 (R.over U).val)
  have h₀ : F.map (f ⊗ g) ≫
      F.map (_root_.PresheafOfModules.sheafTensorIsoSheafification S hS M₂ N₂).hom =
    F.map (_root_.PresheafOfModules.sheafTensorIsoSheafification S hS M₁ N₁).hom ≫
      F.map (L.map (f.val ⊗ g.val)) := by
    rw [← F.map_comp,
      SheafTensorNaturality.sheafTensorIsoSheafification_hom_naturality S hS f g,
      F.map_comp]
  have h₁ := overSheafificationIso_hom_naturality R U (f.val ⊗ g.val)
  have hp : H.map (f.val ⊗ g.val) ≫
      (_root_.PresheafOfModules.overTensorIso S U M₂.val N₂.val).hom =
    (_root_.PresheafOfModules.overTensorIso S U M₁.val N₁.val).hom ≫
      (H.map f.val ⊗ H.map g.val) :=
    (Functor.OplaxMonoidal.δ_natural H f.val g.val).symm
  have h₂ : L'.map (H.map (f.val ⊗ g.val)) ≫
      L'.map (_root_.PresheafOfModules.overTensorIso S U M₂.val N₂.val).hom =
    L'.map (_root_.PresheafOfModules.overTensorIso S U M₁.val N₁.val).hom ≫
      L'.map (H.map f.val ⊗ H.map g.val) := by
    rw [← L'.map_comp, hp, L'.map_comp]
  have hf : (F.map f).val = H.map f.val := rfl
  have hg : (F.map g).val = H.map g.val := rfl
  have h₃ : L'.map (H.map f.val ⊗ H.map g.val) ≫
      (_root_.PresheafOfModules.sheafTensorIsoSheafification
        ((Over.forget U).op ⋙ S) (overRingSheafCondition S hS U)
        (M₂.over U) (N₂.over U)).inv =
    (_root_.PresheafOfModules.sheafTensorIsoSheafification
      ((Over.forget U).op ⋙ S) (overRingSheafCondition S hS U)
      (M₁.over U) (N₁.over U)).inv ≫
        MonoidalCategoryStruct.tensorHom
          (C := _root_.SheafOfModules.{u}
            ((⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).over U))
          (F.map f) (F.map g) := by
    simpa only [hf, hg] using
      SheafTensorNaturality.sheafTensorIsoSheafification_inv_naturality
        ((Over.forget U).op ⋙ S) (overRingSheafCondition S hS U) (F.map f) (F.map g)
  simpa only [overTensorIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc] using naturality_four h₀ h₁ h₂ h₃

set_option maxHeartbeats 800000 in
/-- When two original maps restrict to isomorphisms, their original
tensor map restricts to an isomorphism through the proved naturality square. -/
theorem isIso_over_map_tensorHom (U : C)
    {M₁ M₂ N₁ N₂ : _root_.SheafOfModules.{u}
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    [IsIso ((_root_.SheafOfModules.overFunctor
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) U).map f)]
    [IsIso ((_root_.SheafOfModules.overFunctor
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) U).map g)] :
    letI := _root_.PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    IsIso ((_root_.SheafOfModules.overFunctor
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) U).map (f ⊗ g)) := by
  letI := _root_.PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  letI : MonoidalCategory (_root_.SheafOfModules.{u}
      ((⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).over U)) :=
    _root_.PresheafOfModules.sheafOfModulesMonoidalCategory
      ((Over.forget U).op ⋙ S) (overRingSheafCondition S hS U)
  let F := _root_.SheafOfModules.overFunctor
    (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) U
  have h : F.map (f ⊗ g) ≫ (overTensorIso S hS U M₂ N₂).hom =
      (overTensorIso S hS U M₁ N₁).hom ≫ (F.map f ⊗ F.map g) :=
    overTensorIso_hom_naturality S hS U f g
  haveI : IsIso (F.map (f ⊗ g) ≫ (overTensorIso S hS U M₂ N₂).hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right (F.map (f ⊗ g)) (overTensorIso S hS U M₂ N₂).hom

end Tensor

end KltDP.SheafOfModules
