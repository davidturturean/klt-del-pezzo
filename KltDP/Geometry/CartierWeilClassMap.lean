import KltDP.Geometry.CartierWeilMap
import KltDP.Geometry.CartierPicardHom
import KltDP.Geometry.WeilClassGroup

/-!
# The map from actual Cartier classes to actual Weil classes

The constructed Cartier-to-Weil homomorphism takes the actual principal
Cartier subgroup onto the actual principal Weil subgroup. Composing with
the existing Weil quotient map therefore kills principal Cartier divisors.
Mathlib's quotient universal property supplies the map on the existing
Cartier class group, retaining the original geometric map on representatives.

All divisor groups, principal subgroups, and quotient groups are the already
constructed actual objects. Neither injectivity nor surjectivity of the
induced map is assumed or concluded. In particular this construction does
not identify Cartier classes with Weil classes or with the scheme Picard
group; those require separate geometric arguments.
-/

noncomputable section

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

/-- The image of the actual principal Cartier subgroup is precisely the
actual principal Weil subgroup, by the already proved principal formula. -/
theorem cartierToWeilHom_map_principalCartierDivisors :
    (principalCartierDivisors S.toScheme).map S.cartierToWeilHom =
      S.principalDivisors := by
  change (principalCartierDivisorHom S.toScheme).range.map S.cartierToWeilHom =
    S.principalDivisorHom.range
  rw [AddMonoidHom.map_range, S.cartierToWeilHom_comp_principal]

/-- The actual composite with the Weil class map vanishes on every
principal Cartier divisor. -/
@[simp]
theorem weilClassMap_cartierToWeilHom_principal (f : S.toScheme.functionFieldˣ) :
    S.weilClassMap
        (S.cartierToWeilHom (principalCartierDivisorHom S.toScheme (Additive.ofMul f))) =
      0 := by
  rw [S.cartierToWeilHom_principal, S.weilClassMap_principalDivisor]

/-- The kernel inclusion required for quotient descent follows from the
actual principal compatibility, rather than being a premise of the map. -/
theorem principalCartierDivisors_le_weilClassMap_comp_cartierToWeilHom_ker :
    principalCartierDivisors S.toScheme ≤
      (S.weilClassMap.comp S.cartierToWeilHom).ker := by
  intro D hD
  obtain ⟨f, rfl⟩ := (mem_principalCartierDivisors_iff S.toScheme D).mp hD
  exact S.weilClassMap_cartierToWeilHom_principal f

/-- The homomorphism from the existing Cartier divisor class group to
the existing Weil divisor class group of the original surface. -/
def cartierClassToWeilClassHom : CartierClassGroup S.toScheme →+ S.WeilClassGroup :=
  QuotientAddGroup.lift (principalCartierDivisors S.toScheme)
    (S.weilClassMap.comp S.cartierToWeilHom)
    S.principalCartierDivisors_le_weilClassMap_comp_cartierToWeilHom_ker

/-- On a representative, the induced map is the class of the actual
Weil divisor constructed from local Cartier equation orders. -/
@[simp]
theorem cartierClassToWeilClassHom_class (D : CartierDivisor S.toScheme) :
    S.cartierClassToWeilClassHom (cartierClassMap S.toScheme D) =
      S.weilClassMap (S.cartierToWeilHom D) := rfl

/-- The actual quotient square commutes as an equality of homomorphisms. -/
theorem cartierClassToWeilClassHom_comp_classMap :
    S.cartierClassToWeilClassHom.comp (cartierClassMap S.toScheme) =
      S.weilClassMap.comp S.cartierToWeilHom := rfl

/-- Quotient descent is unique once its values on actual Cartier divisors
are fixed. This uses only the quotient map's proved surjectivity. -/
theorem cartierClassToWeilClassHom_unique
    (φ : CartierClassGroup S.toScheme →+ S.WeilClassGroup)
    (hφ : φ.comp (cartierClassMap S.toScheme) =
      S.weilClassMap.comp S.cartierToWeilHom) :
    φ = S.cartierClassToWeilClassHom := by
  apply AddMonoidHom.ext
  intro c
  obtain ⟨D, rfl⟩ := cartierClassMap_surjective S.toScheme c
  exact DFunLike.congr_fun hφ D

/-- Equal actual Cartier classes give equal actual Weil classes. This
asserts the forward implication only, without a hidden injectivity claim. -/
theorem weilClassMap_cartierToWeilHom_eq_of_cartierClassMap_eq
    {D E : CartierDivisor S.toScheme}
    (h : cartierClassMap S.toScheme D = cartierClassMap S.toScheme E) :
    S.weilClassMap (S.cartierToWeilHom D) =
      S.weilClassMap (S.cartierToWeilHom E) :=
  congrArg S.cartierClassToWeilClassHom h

/-- An actual principal Cartier difference gives an actual principal Weil
difference, witnessed by the same nonzero rational function. -/
theorem cartierToWeilHom_sub_of_principal
    (D E : CartierDivisor S.toScheme) (f : S.toScheme.functionFieldˣ)
    (h : D - E = principalCartierDivisorHom S.toScheme (Additive.ofMul f)) :
    S.cartierToWeilHom D - S.cartierToWeilHom E = S.principalDivisor f := by
  rw [← map_sub, h, S.cartierToWeilHom_principal]

/-- Cartier class equality preserves the already defined actual Weil
linear equivalence relation, with difference oriented as D minus E. -/
theorem cartierToWeilHom_linearlyEquivalent_of_cartierClassMap_eq
    {D E : CartierDivisor S.toScheme}
    (h : cartierClassMap S.toScheme D = cartierClassMap S.toScheme E) :
    S.LinearlyEquivalent (S.cartierToWeilHom D) (S.cartierToWeilHom E) := by
  obtain ⟨f, hf⟩ := (cartierClassMap_eq_iff S.toScheme D E).mp h
  exact ⟨f, S.cartierToWeilHom_sub_of_principal D E f hf⟩

/-- Vanishing of the image class means precisely that the associated
actual Weil divisor is principal. This does not infer that the original
Cartier divisor is principal. -/
theorem cartierClassToWeilClassHom_class_eq_zero_iff (D : CartierDivisor S.toScheme) :
    S.cartierClassToWeilClassHom (cartierClassMap S.toScheme D) = 0 ↔
      ∃ f : S.toScheme.functionFieldˣ, S.cartierToWeilHom D = S.principalDivisor f :=
  S.weilClassMap_eq_zero_iff (S.cartierToWeilHom D)

end KltDP.Geometry.NormalProjectiveSurface
