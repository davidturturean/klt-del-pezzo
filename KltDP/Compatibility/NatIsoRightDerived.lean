import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Natural isomorphisms of right-derived functors

Apply the pinned right-derived natural-transformation construction to the
two inverse maps. Its composition and identity laws supply the inverse laws.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.NatIso

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- The original two inverse natural transformations induce inverse derived maps. -/
def rightDerived (α : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived α.hom n
  inv := NatTrans.rightDerived α.inv n
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, α.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, α.inv_hom_id, NatTrans.rightDerived_id]

@[simp]
lemma rightDerived_hom (α : F ≅ G) (n : ℕ) :
    (rightDerived α n).hom = NatTrans.rightDerived α.hom n := rfl

@[simp]
lemma rightDerived_inv (α : F ≅ G) (n : ℕ) :
    (rightDerived α n).inv = NatTrans.rightDerived α.inv n := rfl

end CategoryTheory.NatIso
