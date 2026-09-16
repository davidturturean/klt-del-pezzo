import KltDP.Geometry.CartierTensorProduct
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The actual Cartier-to-Picard group homomorphism

The tensor multiplication isomorphism and principal-divisor trivialization
already prove the group laws for the class of the constructed O(D). Here
they are packaged as an additive homomorphism into the additive type tag
of the existing scheme Picard group. Mathlib's type-tag equivalence also
gives the same homomorphism with multiplicative notation.

The actual principal Cartier divisors form the range of the existing map
from function-field units to global sections of the Cartier sheaf. Their
Picard classes vanish, so the existing quotient-group universal property
gives a homomorphism from Cartier divisors modulo principal divisors.
This quotient is taken on all Cartier divisors, not merely on global
rational equations. No injectivity, surjectivity, or comparison with Weil
divisor classes is asserted.

Reused pinned Mathlib sources (c44e0c8ee63ca166450922a373c7409c5d26b00b,
Apache-2.0): `Algebra/Group/TypeTags/Hom.lean` for the additive/multiplicative
notation equivalence and `GroupTheory/QuotientGroup/Defs.lean` for the
quotient, class map, and lift. The geometric group laws are the actual
tensor and principal-isomorphism theorems imported above.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual Cartier-to-Picard map, with the Picard group written additively. -/
def cartierPicardHom : CartierDivisor X →+ Additive X.Pic where
  toFun D := Additive.ofMul (cartierPicardClass X D)
  map_zero' := congrArg Additive.ofMul (cartierPicardClass_zero X)
  map_add' D E := congrArg Additive.ofMul (cartierPicardClass_add X D E)

/-- Forgetting the additive notation recovers the original O(D) Picard class. -/
@[simp]
theorem cartierPicardHom_apply (D : CartierDivisor X) :
    (cartierPicardHom X D).toMul = cartierPicardClass X D := rfl

/-- The same homomorphism with the existing multiplicative Picard notation. -/
def cartierPicardMulHom : Multiplicative (CartierDivisor X) →* X.Pic :=
  AddMonoidHom.toMultiplicative'' (cartierPicardHom X)

@[simp]
theorem cartierPicardMulHom_apply (D : CartierDivisor X) :
    cartierPicardMulHom X (Multiplicative.ofAdd D) = cartierPicardClass X D := rfl

/-- Negating a Cartier divisor gives the inverse actual Picard class. -/
theorem cartierPicardClass_neg (D : CartierDivisor X) :
    cartierPicardClass X (-D) = (cartierPicardClass X D)⁻¹ :=
  congrArg Additive.toMul ((cartierPicardHom X).map_neg D)

/-- Subtraction of Cartier divisors gives the quotient of actual Picard classes. -/
theorem cartierPicardClass_sub (D E : CartierDivisor X) :
    cartierPicardClass X (D - E) = cartierPicardClass X D / cartierPicardClass X E :=
  congrArg Additive.toMul ((cartierPicardHom X).map_sub D E)

/-- Every actual principal Cartier divisor lies in the kernel. -/
@[simp]
theorem cartierPicardHom_principal (f : Additive X.functionFieldˣ) :
    cartierPicardHom X (principalCartierDivisorHom X f) = 0 :=
  congrArg Additive.ofMul (cartierPicardClass_principal X f.toMul)

/-- The composition with the original principal-divisor map is the zero homomorphism. -/
theorem cartierPicardHom_comp_principal :
    (cartierPicardHom X).comp (principalCartierDivisorHom X) = 0 := by
  apply AddMonoidHom.ext
  intro f
  exact cartierPicardHom_principal X f

/-- The actual subgroup of principal Cartier divisors is the image of
the original map from nonzero rational functions to Cartier sections. -/
def principalCartierDivisors : AddSubgroup (CartierDivisor X) :=
  (principalCartierDivisorHom X).range

/-- Membership in this image supplies an actual nonzero rational equation. -/
theorem mem_principalCartierDivisors_iff (D : CartierDivisor X) :
    D ∈ principalCartierDivisors X ↔
      ∃ f : X.functionFieldˣ, D = principalCartierDivisorHom X (Additive.ofMul f) := by
  change D ∈ (principalCartierDivisorHom X).range ↔ _
  rw [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.toMul, hf.symm⟩
  · rintro ⟨f, hf⟩
    exact ⟨Additive.ofMul f, hf.symm⟩

/-- The kernel inclusion follows from the actual principal module trivialization. -/
theorem principalCartierDivisors_le_cartierPicardHom_ker :
    principalCartierDivisors X ≤ (cartierPicardHom X).ker := by
  intro D hD
  obtain ⟨f, rfl⟩ := (mem_principalCartierDivisors_iff X D).mp hD
  exact cartierPicardHom_principal X (Additive.ofMul f)

/-- Actual Cartier divisors modulo actual principal Cartier divisors,
using Mathlib's additive-group quotient. -/
abbrev CartierClassGroup := CartierDivisor X ⧸ principalCartierDivisors X

/-- The canonical homomorphism from Cartier divisors to their quotient classes. -/
def cartierClassMap : CartierDivisor X →+ CartierClassGroup X :=
  QuotientAddGroup.mk' (principalCartierDivisors X)

/-- Every quotient class has an actual Cartier divisor representative. -/
theorem cartierClassMap_surjective : Function.Surjective (cartierClassMap X) :=
  QuotientAddGroup.mk'_surjective (principalCartierDivisors X)

/-- Cartier class equality is the existence of an actual principal difference. -/
theorem cartierClassMap_eq_iff (D E : CartierDivisor X) :
    cartierClassMap X D = cartierClassMap X E ↔
      ∃ f : X.functionFieldˣ,
        D - E = principalCartierDivisorHom X (Additive.ofMul f) := by
  change (D : CartierClassGroup X) = E ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem, mem_principalCartierDivisors_iff]

/-- The actual O(D) Picard class descends to Cartier divisors modulo principals. -/
def cartierClassToPicard : CartierClassGroup X →+ Additive X.Pic :=
  QuotientAddGroup.lift (principalCartierDivisors X) (cartierPicardHom X)
    (principalCartierDivisors_le_cartierPicardHom_ker X)

/-- The descended map retains the original constructed O(D) class. -/
@[simp]
theorem cartierClassToPicard_class (D : CartierDivisor X) :
    (cartierClassToPicard X (cartierClassMap X D)).toMul = cartierPicardClass X D := rfl

/-- Its composition with the quotient map is the original geometric homomorphism. -/
theorem cartierClassToPicard_comp_classMap :
    (cartierClassToPicard X).comp (cartierClassMap X) = cartierPicardHom X := by
  apply AddMonoidHom.ext
  intro D
  rfl

end KltDP.Geometry
