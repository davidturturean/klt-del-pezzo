import KltDP.Geometry.WeilCartierEquiv
import KltDP.Geometry.CartierWeilClassMap
import KltDP.Geometry.CartierPicardComparison
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Actual Weil divisor classes and the sheaf Picard group

The existing Cartier-class-to-Weil-class homomorphism is bijective on a
locally factorial surface. Injectivity uses the same rational function
witnessing a principal Weil difference and the proved injectivity of the
actual Cartier-to-Weil map. Surjectivity uses the constructed Cartier
representative of every Weil divisor. The quotient maps and principal
subgroups are the existing ones from `CartierWeilClassMap`.

The inverse class equivalence composes with the proved Cartier-class-to-
Picard equivalence. Its target is the existing group of tensor-invertible
isomorphism classes of actual structure-sheaf modules. The representative
formula recovers the class of the actual module O(E), where E is the
Cartier divisor corresponding to the original Weil divisor.

The algebraically closed base and factoriality of each actual stalk remain
explicit. No Cartier–Weil or Picard comparison is added as an assumption.
The group packaging reuses pinned `AddEquiv.ofBijective`, `trans`, and
`toMultiplicative''`; the geometric maps and quotient relations are reused
without replacement.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
variable [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]

/-- The existing Cartier-class map is injective. A principal Weil
difference lifts to the principal Cartier difference of the same function. -/
theorem cartierClassToWeilClassHom_injective_of_stalks_ufd :
    Function.Injective X.cartierClassToWeilClassHom := by
  intro c d hcd
  obtain ⟨D, rfl⟩ := cartierClassMap_surjective X.toScheme c
  obtain ⟨E, rfl⟩ := cartierClassMap_surjective X.toScheme d
  change X.weilClassMap (X.cartierToWeilHom D) =
    X.weilClassMap (X.cartierToWeilHom E) at hcd
  obtain ⟨f, hf⟩ :=
    (X.weilClassMap_eq_iff (X.cartierToWeilHom D) (X.cartierToWeilHom E)).mp hcd
  apply (cartierClassMap_eq_iff X.toScheme D E).mpr
  refine ⟨f, ?_⟩
  apply X.cartierToWeilHom_injective_of_stalks_ufd
  rw [map_sub, X.cartierToWeilHom_principal]
  exact hf

/-- The existing class map is surjective, using the actual Cartier
representative constructed for an actual Weil representative. -/
theorem cartierClassToWeilClassHom_surjective_of_stalks_ufd :
    Function.Surjective X.cartierClassToWeilClassHom := by
  intro c
  obtain ⟨D, rfl⟩ := X.weilClassMap_surjective c
  obtain ⟨E, rfl⟩ := X.cartierToWeilHom_surjective_of_stalks_ufd D
  exact ⟨cartierClassMap X.toScheme E,
    X.cartierClassToWeilClassHom_class E⟩

/-- The actual Cartier and Weil class groups are equivalent through
the already constructed quotient homomorphism. -/
def cartierWeilClassEquiv : CartierClassGroup X.toScheme ≃+ X.WeilClassGroup :=
  AddEquiv.ofBijective X.cartierClassToWeilClassHom
    ⟨X.cartierClassToWeilClassHom_injective_of_stalks_ufd,
      X.cartierClassToWeilClassHom_surjective_of_stalks_ufd⟩

theorem cartierWeilClassEquiv_class (D : CartierDivisor X.toScheme) :
    X.cartierWeilClassEquiv (cartierClassMap X.toScheme D) =
      X.weilClassMap (X.cartierToWeilHom D) :=
  X.cartierClassToWeilClassHom_class D

/-- Actual Weil divisor classes are equivalent to the actual sheaf
Picard group, with the latter written additively. -/
def weilClassPicardEquiv : X.WeilClassGroup ≃+ Additive X.toScheme.Pic :=
  X.cartierWeilClassEquiv.symm.trans (cartierClassPicardEquiv X.toScheme)

/-- The same equivalence with the existing multiplicative notation
for tensor-invertible sheaf classes. -/
def weilClassPicardMulEquiv : Multiplicative X.WeilClassGroup ≃* X.toScheme.Pic :=
  AddEquiv.toMultiplicative'' X.weilClassPicardEquiv

/-- On the Weil image of an actual Cartier divisor, the equivalence
recovers the original class of its actual O(D) module sheaf. -/
theorem weilClassPicardEquiv_of_cartier (D : CartierDivisor X.toScheme) :
    (X.weilClassPicardEquiv (X.weilClassMap (X.cartierToWeilHom D))).toMul =
      cartierPicardClass X.toScheme D := by
  change ((cartierClassPicardEquiv X.toScheme)
    (X.cartierWeilClassEquiv.symm (X.weilClassMap (X.cartierToWeilHom D)))).toMul = _
  have hinverse : X.cartierWeilClassEquiv.symm
      (X.weilClassMap (X.cartierToWeilHom D)) = cartierClassMap X.toScheme D :=
    (congrArg X.cartierWeilClassEquiv.symm (X.cartierWeilClassEquiv_class D).symm).trans
      (X.cartierWeilClassEquiv.symm_apply_apply (cartierClassMap X.toScheme D))
  exact (congrArg (fun c => (cartierClassPicardEquiv X.toScheme c).toMul) hinverse).trans
    (cartierClassPicardEquiv_apply X.toScheme D)

/-- Every actual Weil divisor is sent to the class of the actual
O(E), where E is its constructed Cartier inverse image. -/
theorem weilClassPicardEquiv_representative (D : X.WeilDivisor) :
    (X.weilClassPicardEquiv (X.weilClassMap D)).toMul =
      cartierPicardClass X.toScheme (X.cartierWeilEquiv.symm D) := by
  have hD : X.cartierToWeilHom (X.cartierWeilEquiv.symm D) = D :=
    X.cartierWeilEquiv.apply_symm_apply D
  simpa only [hD] using
    X.weilClassPicardEquiv_of_cartier (X.cartierWeilEquiv.symm D)

/-- The actual Picard class associated to a Weil divisor. It factors
through the existing Weil quotient, so it is independent of representatives. -/
def weilPicardClass (D : X.WeilDivisor) : X.toScheme.Pic :=
  (X.weilClassPicardEquiv (X.weilClassMap D)).toMul

theorem weilPicardClass_of_cartier (D : CartierDivisor X.toScheme) :
    X.weilPicardClass (X.cartierToWeilHom D) = cartierPicardClass X.toScheme D :=
  X.weilClassPicardEquiv_of_cartier D

/-- Addition of actual Weil divisors gives multiplication in the
existing tensor Picard group. -/
theorem weilPicardClass_add (D E : X.WeilDivisor) :
    X.weilPicardClass (D + E) = X.weilPicardClass D * X.weilPicardClass E := by
  change (X.weilClassPicardEquiv (X.weilClassMap (D + E))).toMul = _
  exact (congrArg (fun c => (X.weilClassPicardEquiv c).toMul)
    (X.weilClassMap.map_add D E)).trans
      (congrArg Additive.toMul
        (X.weilClassPicardEquiv.map_add (X.weilClassMap D) (X.weilClassMap E)))

/-- The principal divisor of an actual rational function gives the
identity element of the existing Picard group. -/
theorem weilPicardClass_principal (f : X.toScheme.functionFieldˣ) :
    X.weilPicardClass (X.principalDivisor f) = 1 := by
  change (X.weilClassPicardEquiv (X.weilClassMap (X.principalDivisor f))).toMul = 1
  exact congrArg Additive.toMul
    ((congrArg X.weilClassPicardEquiv (X.weilClassMap_principalDivisor f)).trans
      X.weilClassPicardEquiv.map_zero)

/-- Equality of the actual Picard classes is exactly the existing
Weil linear equivalence, with the same principal-divisor relation. -/
theorem weilPicardClass_eq_iff (D E : X.WeilDivisor) :
    X.weilPicardClass D = X.weilPicardClass E ↔ X.LinearlyEquivalent D E := by
  rw [X.linearlyEquivalent_iff_weilClassMap_eq]
  constructor
  · intro h
    apply X.weilClassPicardEquiv.injective
    exact congrArg Additive.ofMul h
  · intro h
    exact congrArg (fun c => (X.weilClassPicardEquiv c).toMul) h

end KltDP.Geometry.NormalProjectiveSurface
