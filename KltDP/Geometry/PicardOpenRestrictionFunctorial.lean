import KltDP.Geometry.CartierOpenRestrictionFunctorial
import KltDP.Geometry.CartierOpenRestrictionPicard
import KltDP.Geometry.CartierPicardComparison

/-!
# Identity and composition of actual Picard restriction

On an integral scheme every actual Picard class has a Cartier
representative, by the already constructed comparison. The proved O(D)
restriction theorem and the actual Cartier restriction laws therefore
give identity and composition for the existing Picard restriction homs.
The surjectivity used here is the proved theorem, not a supplied premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemeModuleRestriction

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

/-- Identity restriction on the existing actual Picard group of an
integral scheme. -/
theorem picardRestrictionHom_id :
    picardRestrictionHom (𝟙 X) = MonoidHom.id X.Pic := by
  apply MonoidHom.ext
  intro p
  obtain ⟨D, rfl⟩ := cartierPicardClass_surjective X p
  change picardRestrictionHom (𝟙 X) (cartierPicardClass X D) = cartierPicardClass X D
  rw [OpenImmersionRational.picardRestrictionHom_cartierPicardClass,
    OpenImmersionRational.cartierRestrictionHom_id]
  rfl

/-- Actual Picard restriction is contravariantly compatible with
composition of open immersions between integral schemes. -/
theorem picardRestrictionHom_comp (f : Y ⟶ X) (g : Z ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    picardRestrictionHom (g ≫ f) = (picardRestrictionHom g).comp (picardRestrictionHom f) := by
  apply MonoidHom.ext
  intro p
  obtain ⟨D, rfl⟩ := cartierPicardClass_surjective X p
  change picardRestrictionHom (g ≫ f) (cartierPicardClass X D) =
    picardRestrictionHom g (picardRestrictionHom f (cartierPicardClass X D))
  rw [OpenImmersionRational.picardRestrictionHom_cartierPicardClass,
    OpenImmersionRational.picardRestrictionHom_cartierPicardClass,
    OpenImmersionRational.picardRestrictionHom_cartierPicardClass,
    OpenImmersionRational.cartierRestrictionHom_comp]
  rfl

end KltDP.Geometry.SchemeModuleRestriction
