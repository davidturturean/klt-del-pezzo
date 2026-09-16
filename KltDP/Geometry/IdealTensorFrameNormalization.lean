import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# An actual line frame preserves the tensor of an ideal inclusion

Tensor the given frame with the original ideal object, then use the original
right unitor. Its inverse carries the tensor of the original inclusion to
that inclusion followed by the inverse frame. The proof uses only the pinned
whisker exchange and unitor naturality identities.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace KltDP.Geometry.IdealTensorFrameNormalization

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (I : C) {L : C} (e : L ≅ 𝟙_ C)

/-- Tensor the actual frame with the original ideal object. -/
def frameIso : I ⊗ L ≅ I :=
  (tensorLeft I).mapIso e ≪≫ ρ_ I

/-- The tensor inclusion retains the original inclusion and inverse frame. -/
theorem frameIso_inv_inclusion (i : I ⟶ 𝟙_ C) :
    (frameIso I e).inv ≫ (i ▷ L) ≫ (λ_ L).hom = i ≫ e.inv := by
  change ((ρ_ I).inv ≫ I ◁ e.inv) ≫ (i ▷ L) ≫ (λ_ L).hom = _
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality, unitors_equal,
    rightUnitor_naturality_assoc, Iso.inv_hom_id_assoc]

end KltDP.Geometry.IdealTensorFrameNormalization
