import KltDP.Geometry.OpenCartierIntrinsicOrder
import KltDP.Geometry.PrimeCurveExistence

/-!
# Exact Weil extension under restriction to a smaller open

The original extended coefficient is the intrinsic Cartier order on the open.
The existing order-restriction theorem compares these orders along the literal
`Scheme.homOfLE`. Coverage of every original prime generic point suffices for
equality of the actual finitely supported Weil divisors.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.OpenCartierWeil

open OpenImmersionRational
attribute [local instance] integralSchemeStalk_isDomain

/-- A large open of an actual surface is nonempty because the surface has
an original prime curve. -/
theorem nonempty_of_primeGenericPoint_mem
    {k : Type u} [Field k] {X : NormalProjectiveSurface k}
    (V : X.toScheme.Opens) (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V) :
    Nonempty V.toScheme := by
  obtain ⟨C⟩ := X.primeCurve_nonempty
  exact ⟨⟨C.genericPoint, hV C⟩⟩

/-- The actual large open inherits integrality from the original surface. -/
theorem isIntegral_of_primeGenericPoint_mem
    {k : Type u} [Field k] {X : NormalProjectiveSurface k}
    (V : X.toScheme.Opens) (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V) :
    IsIntegral V.toScheme := by
  letI : Nonempty V.toScheme := nonempty_of_primeGenericPoint_mem V hV
  letI : Nonempty V := ⟨Classical.choice inferInstance⟩
  exact isIntegral_of_isOpenImmersion V.ι

section Coefficients

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}
    (U V : X.toScheme.Opens) [Nonempty U.toScheme] [Nonempty V.toScheme]

local instance : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance : Nonempty V := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
local instance : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι

/-- Shrinking an actual open preserves its extended coefficient at every
original prime generic point retained in the smaller open. -/
theorem restrictedCoefficient_nestedRestriction
    (hVU : V ≤ U) (D : CartierDivisor U.toScheme)
    (C : X.PrimeCurve) (hCV : C.genericPoint ∈ V) :
    restrictedCoefficient V
        (cartierRestrictionHom (X.toScheme.homOfLE hVU) D) C =
      restrictedCoefficient U D C := by
  let xV : V.toScheme := ⟨C.genericPoint, hCV⟩
  let xU : U.toScheme := ⟨C.genericPoint, hVU hCV⟩
  letI : IsDiscreteValuationRing (X.toScheme.presheaf.stalk C.genericPoint) :=
    C.genericPoint_isDiscreteValuationRing
  letI : IsDiscreteValuationRing (V.toScheme.presheaf.stalk xV) :=
    stalk_isDiscreteValuationRing_of_isOpenImmersion V.ι xV C.genericPoint rfl
  letI : IsDiscreteValuationRing (U.toScheme.presheaf.stalk xU) :=
    stalk_isDiscreteValuationRing_of_isOpenImmersion U.ι xU C.genericPoint rfl
  have hpoint : (X.toScheme.homOfLE hVU).base xV = xU := by
    apply Subtype.ext
    exact Scheme.homOfLE_apply hVU xV
  calc
    _ = cartierOrderAt V.toScheme
        (cartierRestrictionHom (X.toScheme.homOfLE hVU) D) xV :=
      restrictedCoefficient_eq_cartierOrderAt V _ C hCV
    _ = cartierOrderAt U.toScheme D xU :=
      cartierOrderAt_cartierRestrictionHom
        (X.toScheme.homOfLE hVU) D xV xU hpoint
    _ = restrictedCoefficient U D C :=
      (restrictedCoefficient_eq_cartierOrderAt U D C (hVU hCV)).symm

end Coefficients

/-- Restriction to a smaller actual open containing every original prime
generic point leaves the exact Weil extension unchanged. All nonemptiness
and integrality instances are derived from this coverage and the surface. -/
theorem restrictedWeilHom_nestedRestriction
    {k : Type u} [Field k] {X : NormalProjectiveSurface k}
    (U V : X.toScheme.Opens) (hVU : V ≤ U)
    (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V) :
    letI : IsIntegral U.toScheme :=
      isIntegral_of_primeGenericPoint_mem U (fun C => hVU (hV C))
    letI : IsIntegral V.toScheme := isIntegral_of_primeGenericPoint_mem V hV
    ∀ D : CartierDivisor U.toScheme,
      restrictedWeilHom V (cartierRestrictionHom (X.toScheme.homOfLE hVU) D) =
        restrictedWeilHom U D := by
  letI : IsIntegral U.toScheme :=
    isIntegral_of_primeGenericPoint_mem U (fun C => hVU (hV C))
  letI : IsIntegral V.toScheme := isIntegral_of_primeGenericPoint_mem V hV
  intro D
  apply Finsupp.ext
  intro C
  exact restrictedCoefficient_nestedRestriction U V hVU D C (hV C)

end KltDP.Geometry.OpenCartierWeil

#check @KltDP.Geometry.OpenCartierWeil.restrictedWeilHom_nestedRestriction
#print axioms KltDP.Geometry.OpenCartierWeil.restrictedWeilHom_nestedRestriction
