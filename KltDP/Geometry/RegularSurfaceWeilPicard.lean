import KltDP.Geometry.RegularStalkUFD
import KltDP.Geometry.WeilClassPicard

/-!
# Divisor and Picard comparisons on a regular projective surface

Regularity is asserted at every actual scheme point through the original
cotangent-space predicate. The canonical regular-local factoriality adapter
then supplies the factoriality of the original stalks. The existing geometric
Cartier construction, principal-divisor relations, and actual sheaf Picard
comparison give the equivalences below.

No factorial-stalk premise or Cartier representability is supplied to these
endpoints. The normal projective surface and algebraically closed base are
the existing hypotheses of the underlying divisor construction. Smoothness
is not identified with regularity by definition.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
variable (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Actual Cartier and Weil divisors agree on the regular surface. -/
def regularCartierWeilEquiv : CartierDivisor X.toScheme ≃+ X.WeilDivisor := by
  letI : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x) :=
    X.stalks_uniqueFactorizationMonoid_of_regular hregular
  exact X.cartierWeilEquiv

theorem regularCartierWeilEquiv_apply (D : CartierDivisor X.toScheme) :
    X.regularCartierWeilEquiv hregular D = X.cartierToWeilHom D := rfl

/-- The equivalence uses the same actual principal rational function. -/
theorem regularCartierWeilEquiv_principal (f : X.toScheme.functionFieldˣ) :
    X.regularCartierWeilEquiv hregular
        (principalCartierDivisorHom X.toScheme (Additive.ofMul f)) =
      X.principalDivisor f :=
  X.cartierToWeilHom_principal f

/-- The original Cartier and Weil class groups agree, with the original
principal-divisor subgroups. -/
def regularCartierWeilClassEquiv : CartierClassGroup X.toScheme ≃+ X.WeilClassGroup := by
  letI : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x) :=
    X.stalks_uniqueFactorizationMonoid_of_regular hregular
  exact X.cartierWeilClassEquiv

theorem regularCartierWeilClassEquiv_class (D : CartierDivisor X.toScheme) :
    X.regularCartierWeilClassEquiv hregular (cartierClassMap X.toScheme D) =
      X.weilClassMap (X.cartierToWeilHom D) := by
  letI : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x) :=
    X.stalks_uniqueFactorizationMonoid_of_regular hregular
  exact X.cartierWeilClassEquiv_class D

/-- Actual Weil divisor classes equal the original sheaf Picard group,
written additively, on the regular surface. -/
def regularWeilClassPicardEquiv : X.WeilClassGroup ≃+ Additive X.toScheme.Pic := by
  letI : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x) :=
    X.stalks_uniqueFactorizationMonoid_of_regular hregular
  exact X.weilClassPicardEquiv

/-- The same equivalence in the existing multiplicative Picard notation. -/
def regularWeilClassPicardMulEquiv : Multiplicative X.WeilClassGroup ≃* X.toScheme.Pic :=
  AddEquiv.toMultiplicative'' (X.regularWeilClassPicardEquiv hregular)

/-- The class formula recovers the original O(D), not a replacement sheaf. -/
theorem regularWeilClassPicardEquiv_of_cartier (D : CartierDivisor X.toScheme) :
    (X.regularWeilClassPicardEquiv hregular
      (X.weilClassMap (X.cartierToWeilHom D))).toMul =
        cartierPicardClass X.toScheme D := by
  letI : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x) :=
    X.stalks_uniqueFactorizationMonoid_of_regular hregular
  exact X.weilClassPicardEquiv_of_cartier D

/-- Every actual Weil class is represented by the constructed O(E),
where E is its actual Cartier inverse image. -/
theorem regularWeilClassPicardEquiv_representative (D : X.WeilDivisor) :
    (X.regularWeilClassPicardEquiv hregular (X.weilClassMap D)).toMul =
      cartierPicardClass X.toScheme ((X.regularCartierWeilEquiv hregular).symm D) := by
  letI : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x) :=
    X.stalks_uniqueFactorizationMonoid_of_regular hregular
  exact X.weilClassPicardEquiv_representative D

/-- The actual Picard class of an actual Weil divisor on the regular surface. -/
def regularWeilPicardClass (D : X.WeilDivisor) : X.toScheme.Pic :=
  (X.regularWeilClassPicardEquiv hregular (X.weilClassMap D)).toMul

/-- Addition of Weil divisors gives tensor multiplication of actual classes. -/
theorem regularWeilPicardClass_add (D E : X.WeilDivisor) :
    X.regularWeilPicardClass hregular (D + E) =
      X.regularWeilPicardClass hregular D * X.regularWeilPicardClass hregular E := by
  letI : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x) :=
    X.stalks_uniqueFactorizationMonoid_of_regular hregular
  exact X.weilPicardClass_add D E

/-- Actual principal divisors give the identity Picard class. -/
theorem regularWeilPicardClass_principal (f : X.toScheme.functionFieldˣ) :
    X.regularWeilPicardClass hregular (X.principalDivisor f) = 1 := by
  letI : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x) :=
    X.stalks_uniqueFactorizationMonoid_of_regular hregular
  exact X.weilPicardClass_principal f

/-- Equality of the actual Picard classes is exactly the existing Weil
linear equivalence, with its original principal-divisor relation. -/
theorem regularWeilPicardClass_eq_iff (D E : X.WeilDivisor) :
    X.regularWeilPicardClass hregular D = X.regularWeilPicardClass hregular E ↔
      X.LinearlyEquivalent D E := by
  letI : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x) :=
    X.stalks_uniqueFactorizationMonoid_of_regular hregular
  exact X.weilPicardClass_eq_iff D E

end KltDP.Geometry.NormalProjectiveSurface
