import KltDP.Compatibility.SheafModuleMonoidal

/-!
# Naturality of the original sheafified tensor comparison

The existing sheafification counit and monoidal tensorator are natural
for actual morphisms. Their composition proves naturality of the
project's original `sheafTensorIsoSheafification`, in both directions.
No replacement tensor, chosen comparison, or naturality assumption is
introduced. The proof uses the pinned adjunction and monoidal-functor
laws and the accepted original comparison definition.
-/

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace KltDP.SheafTensorNaturality

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrp.{u}] [HasWeakSheafify J AddCommGrp.{u}]

section Counit

variable (R : Sheaf J RingCat.{u})
  {M N : _root_.SheafOfModules.{u} R}

/-- Naturality of the actual reflective sheafification counit. -/
theorem sheafificationForgetIso_hom_naturality (f : M ⟶ N) :
    (_root_.PresheafOfModules.sheafification (𝟙 R.val)).map f.val ≫
        (_root_.PresheafOfModules.sheafificationForgetIso R N).hom =
      (_root_.PresheafOfModules.sheafificationForgetIso R M).hom ≫ f :=
  (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.val)).counit.naturality f

/-- Naturality of the inverse of the same original counit. -/
theorem sheafificationForgetIso_inv_naturality (f : M ⟶ N) :
    (_root_.PresheafOfModules.sheafificationForgetIso R M).inv ≫
        (_root_.PresheafOfModules.sheafification (𝟙 R.val)).map f.val =
      f ≫ (_root_.PresheafOfModules.sheafificationForgetIso R N).inv := by
  apply (cancel_mono (_root_.PresheafOfModules.sheafificationForgetIso R N).hom).mp
  simp only [Category.assoc, sheafificationForgetIso_hom_naturality,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end Counit

section Tensor

variable (S : Cᵒᵖ ⥤ CommRingCat.{u})
  (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))
  {M₁ M₂ N₁ N₂ : _root_.SheafOfModules.{u}
    (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})}

set_option maxHeartbeats 800000 in
/-- The original sheaf-to-sheafified-tensor comparison commutes with
the original tensor product of two sheaf morphisms. -/
theorem sheafTensorIsoSheafification_hom_naturality
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    letI := _root_.PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    (f ⊗ g) ≫ (_root_.PresheafOfModules.sheafTensorIsoSheafification S hS M₂ N₂).hom =
      (_root_.PresheafOfModules.sheafTensorIsoSheafification S hS M₁ N₁).hom ≫
        (_root_.PresheafOfModules.sheafification
          (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).val)).map
          (f.val ⊗ g.val) := by
  letI := _root_.PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  letI := _root_.PresheafOfModules.sheafificationMonoidal S hS
  let R : Sheaf J RingCat.{u} := ⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩
  let L := _root_.PresheafOfModules.sheafification (𝟙 R.val)
  change (f ⊗ g) ≫
      (((_root_.PresheafOfModules.sheafificationForgetIso R M₂).inv ⊗
        (_root_.PresheafOfModules.sheafificationForgetIso R N₂).inv) ≫
          Functor.LaxMonoidal.μ L M₂.val N₂.val) =
    (((_root_.PresheafOfModules.sheafificationForgetIso R M₁).inv ⊗
      (_root_.PresheafOfModules.sheafificationForgetIso R N₁).inv) ≫
        Functor.LaxMonoidal.μ L M₁.val N₁.val) ≫ L.map (f.val ⊗ g.val)
  rw [← Category.assoc, ← tensor_comp,
    ← sheafificationForgetIso_inv_naturality R f,
    ← sheafificationForgetIso_inv_naturality R g,
    tensor_comp, Category.assoc, Functor.LaxMonoidal.μ_natural]
  simp only [Category.assoc, L]

set_option maxHeartbeats 800000 in
/-- The inverse tensor comparison has the corresponding original
morphism naturality square. -/
theorem sheafTensorIsoSheafification_inv_naturality
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    letI := _root_.PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    (_root_.PresheafOfModules.sheafification
        (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).val)).map
        (f.val ⊗ g.val) ≫
        (_root_.PresheafOfModules.sheafTensorIsoSheafification S hS M₂ N₂).inv =
      (_root_.PresheafOfModules.sheafTensorIsoSheafification S hS M₁ N₁).inv ≫
        (f ⊗ g) := by
  letI := _root_.PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  apply (cancel_epi
    (_root_.PresheafOfModules.sheafTensorIsoSheafification S hS M₁ N₁).hom).mp
  rw [← Category.assoc, ← sheafTensorIsoSheafification_hom_naturality S hS f g]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end Tensor

end KltDP.SheafTensorNaturality
