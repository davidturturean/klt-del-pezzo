import KltDP.Geometry.CartierOpenRestrictionFunctorial
import KltDP.Geometry.CartierSchemePullbackOpenImmersion
import KltDP.Geometry.CartierPicardComparison

/-!
# Restriction of actual Cartier classes

The existing Cartier restriction sends each actual principal divisor to
the principal divisor of the transported rational function. It therefore
descends to the original Cartier class quotient. Its values on original
divisors determine the map, including its identity and composition laws.

The original Cartier-class/Picard equivalence commutes with this quotient
map and the actual scheme Picard pullback. The inverse equivalence has the
same compatibility. No restriction map is defined by transporting Picard
classes, and no naturality or principal-subgroup premise is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.OpenImmersionRational

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
variable (f : Y ⟶ X) [IsOpenImmersion f]

/-- The actual Cartier restriction preserves the actual principal
subgroups, with the transported function supplied by the existing map. -/
theorem principalCartierDivisors_le_restriction_comap :
    principalCartierDivisors X ≤
      (principalCartierDivisors Y).comap (cartierRestrictionHom f) := by
  intro D hD
  obtain ⟨g, rfl⟩ := (mem_principalCartierDivisors_iff X D).mp hD
  change cartierRestrictionHom f
    (principalCartierDivisorHom X (Additive.ofMul g)) ∈ principalCartierDivisors Y
  rw [cartierRestrictionHom_principal]
  exact (mem_principalCartierDivisors_iff Y _).mpr
    ⟨Units.map (functionFieldIso f).hom.hom.toMonoidHom g, rfl⟩

/-- Restriction on the existing quotient of Cartier divisors by actual
principal divisors, induced by the original Cartier restriction. -/
def cartierClassRestrictionHom : CartierClassGroup X →+ CartierClassGroup Y :=
  QuotientAddGroup.map (principalCartierDivisors X) (principalCartierDivisors Y)
    (cartierRestrictionHom f) (principalCartierDivisors_le_restriction_comap f)

/-- The quotient restriction retains the original map on divisors. -/
@[simp]
theorem cartierClassRestrictionHom_class (D : CartierDivisor X) :
    cartierClassRestrictionHom f (cartierClassMap X D) =
      cartierClassMap Y (cartierRestrictionHom f D) := rfl

/-- The square of original Cartier and class maps commutes. -/
theorem cartierClassRestrictionHom_comp_classMap :
    (cartierClassRestrictionHom f).comp (cartierClassMap X) =
      (cartierClassMap Y).comp (cartierRestrictionHom f) := rfl

/-- An additive class map with the same values on actual divisors is
the constructed quotient restriction. -/
theorem cartierClassRestrictionHom_unique
    (φ : CartierClassGroup X →+ CartierClassGroup Y)
    (hφ : φ.comp (cartierClassMap X) =
      (cartierClassMap Y).comp (cartierRestrictionHom f)) :
    φ = cartierClassRestrictionHom f := by
  apply AddMonoidHom.ext
  intro c
  obtain ⟨D, rfl⟩ := cartierClassMap_surjective X c
  exact DFunLike.congr_fun hφ D

/-- Identity restriction acts identically on the actual Cartier quotient. -/
theorem cartierClassRestrictionHom_id :
    cartierClassRestrictionHom (𝟙 X) = AddMonoidHom.id (CartierClassGroup X) := by
  apply AddMonoidHom.ext
  intro c
  obtain ⟨D, rfl⟩ := cartierClassMap_surjective X c
  change cartierClassMap X (cartierRestrictionHom (𝟙 X) D) = cartierClassMap X D
  rw [cartierRestrictionHom_id]
  rfl

/-- Actual Cartier class restriction is contravariantly compatible with
composition of the original open immersions. -/
theorem cartierClassRestrictionHom_comp (g : Z ⟶ Y) [IsOpenImmersion g] :
    cartierClassRestrictionHom (g ≫ f) =
      (cartierClassRestrictionHom g).comp (cartierClassRestrictionHom f) := by
  apply AddMonoidHom.ext
  intro c
  obtain ⟨D, rfl⟩ := cartierClassMap_surjective X c
  change cartierClassMap Z (cartierRestrictionHom (g ≫ f) D) =
    cartierClassMap Z (cartierRestrictionHom g (cartierRestrictionHom f D))
  rw [cartierRestrictionHom_comp]
  rfl

/-- The original class/Picard equivalence carries quotient restriction
to the actual scheme Picard pullback. -/
theorem cartierClassPicardEquiv_restrict (c : CartierClassGroup X) :
    cartierClassPicardEquiv Y (cartierClassRestrictionHom f c) =
      (schemePicardPullbackHom f).toAdditive (cartierClassPicardEquiv X c) := by
  obtain ⟨D, rfl⟩ := cartierClassMap_surjective X c
  change Additive.ofMul (cartierPicardClass Y (cartierRestrictionHom f D)) =
    Additive.ofMul (schemePicardPullbackHom f (cartierPicardClass X D))
  exact congrArg Additive.ofMul (schemePicardPullbackHom_cartierPicardClass f D).symm

/-- Naturality as an equality of the original additive homomorphisms. -/
theorem cartierClassPicardEquiv_naturality :
    (cartierClassPicardEquiv Y).toAddMonoidHom.comp (cartierClassRestrictionHom f) =
      (schemePicardPullbackHom f).toAdditive.comp
        (cartierClassPicardEquiv X).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro c
  exact cartierClassPicardEquiv_restrict f c

/-- The inverse comparison restricts the actual Cartier class of every
original Picard class, without choosing a new divisor representative. -/
theorem cartierClassPicardEquiv_symm_restrict (p : Additive X.Pic) :
    cartierClassRestrictionHom f ((cartierClassPicardEquiv X).symm p) =
      (cartierClassPicardEquiv Y).symm ((schemePicardPullbackHom f).toAdditive p) := by
  apply (cartierClassPicardEquiv Y).injective
  rw [cartierClassPicardEquiv_restrict, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

end KltDP.Geometry.OpenImmersionRational
