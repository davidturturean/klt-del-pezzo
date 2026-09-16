import KltDP.Geometry.CartierLocalClass
import KltDP.Geometry.PrincipalDivisorUnits
import KltDP.Geometry.WeilClassGroup

/-!
# Global principal equations modulo actual regular units

We quotient actual nonzero rational functions by the image of actual global
structure-sheaf units. The principal Weil divisor descends to this quotient
because global units have zero order along every prime curve, as proved in
`PrincipalDivisorUnits`. The image in the Weil class group is zero.

This constructs the group of global principal equations up to regular units.
It does not identify this quotient with a group of global sections of a
Cartier-divisor sheaf, and does not construct arbitrary Cartier divisors or
their line bundles. In particular the induced map to Weil divisors is not
declared injective here. The quotient, lift, and induction machinery is
reused directly from pinned Mathlib (Apache-2.0).
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Actual global principal equations modulo actual global regular units.
This is a quotient of the original scheme's rational-function units. -/
abbrev PrincipalCartierClass :=
  RingTheory.CartierLocalClass Γ(X.toScheme, ⊤) X.toScheme.functionField

/-- The quotient class of an actual global rational equation. -/
def principalCartierClassMap :
    Additive X.toScheme.functionFieldˣ →+ X.PrincipalCartierClass :=
  RingTheory.cartierLocalClassMap Γ(X.toScheme, ⊤) X.toScheme.functionField

/-- Every principal equation class has a rational-function representative. -/
theorem principalCartierClassMap_surjective :
    Function.Surjective X.principalCartierClassMap :=
  RingTheory.cartierLocalClassMap_surjective Γ(X.toScheme, ⊤) X.toScheme.functionField

/-- The kernel condition for descent is proved from actual section maps
and local unit orders, without assuming a Cartier-to-Weil comparison. -/
theorem globalRegularUnitImage_le_principalDivisorHom_ker :
    RingTheory.regularUnitImage Γ(X.toScheme, ⊤) X.toScheme.functionField ≤
      X.principalDivisorHom.ker := by
  intro f hf
  obtain ⟨a, ha⟩ := (RingTheory.mem_regularUnitImage_iff
    Γ(X.toScheme, ⊤) X.toScheme.functionField f.toMul).mp hf
  change X.principalDivisor f.toMul = 0
  rw [← ha]
  exact X.principalDivisor_map_global_unit a

/-- The actual principal Weil divisor is well-defined on global equations
modulo actual global units. -/
def principalCartierToWeil : X.PrincipalCartierClass →+ X.WeilDivisor :=
  QuotientAddGroup.lift
    (RingTheory.regularUnitImage Γ(X.toScheme, ⊤) X.toScheme.functionField)
    X.principalDivisorHom X.globalRegularUnitImage_le_principalDivisorHom_ker

@[simp]
theorem principalCartierToWeil_class (f : X.toScheme.functionFieldˣ) :
    X.principalCartierToWeil (X.principalCartierClassMap (Additive.ofMul f)) =
      X.principalDivisor f := rfl

/-- The resulting Weil divisor has trivial actual Weil class for every
principal equation class, as follows from its rational representative. -/
@[simp]
theorem weilClassMap_principalCartierToWeil (c : X.PrincipalCartierClass) :
    X.weilClassMap (X.principalCartierToWeil c) = 0 := by
  obtain ⟨f, rfl⟩ := X.principalCartierClassMap_surjective c
  exact X.weilClassMap_principalDivisor f.toMul

end KltDP.Geometry.NormalProjectiveSurface
