import KltDP.Geometry.PrincipalDivisor
import KltDP.Geometry.UFDDivisorCoordinates

/-!
# Rational equations on an actual factorial affine open

Restrict the original finite Weil coefficients to curves meeting the open,
embed them into its actual height-one primes, and take the existing UFD
fraction product. The original affine/global order comparison recovers
every coefficient. No affine Picard triviality or principalization theorem
is assumed. This is the affine-open version of `WeilLocalEquation`'s
already compiled stalk-coordinate construction.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Finite original divisor coefficients on the actual affine prime carrier. -/
def affineDivisorCoordinates {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (D : X.WeilDivisor) : RingTheory.AffineHeightOnePrime Γ(X.toScheme, U) →₀ ℤ :=
  Finsupp.embDomain
    ⟨fun C : {C : X.PrimeCurve // C.genericPoint ∈ U} =>
        C.1.affineHeightOnePrime hU C.2,
      PrimeCurve.affineHeightOnePrime_injective hU⟩
    (D.subtypeDomain (fun C => C.genericPoint ∈ U))

theorem affineDivisorCoordinates_apply {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (D : X.WeilDivisor) (C : X.PrimeCurve) (hC : C.genericPoint ∈ U) :
    X.affineDivisorCoordinates hU D (C.affineHeightOnePrime hU hC) = D C :=
  Finsupp.embDomain_apply _ _ (⟨C, hC⟩ : {C : X.PrimeCurve // C.genericPoint ∈ U})

/-- An actual fraction on the original surface realizing the affine coefficients. -/
def affineRationalEquation {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    [Nonempty U] [UniqueFactorizationMonoid Γ(X.toScheme, U)]
    (D : X.WeilDivisor) : X.toScheme.functionFieldˣ :=
  letI : IsNoetherianRing Γ(X.toScheme, U) := X.affineSections_isNoetherianRing hU
  letI : IsFractionRing Γ(X.toScheme, U) X.toScheme.functionField :=
    functionField_isFractionRing_of_isAffineOpen X.toScheme U hU
  RingTheory.fractionOfDivisorCoordinates Γ(X.toScheme, U) X.toScheme.functionField
    (X.affineDivisorCoordinates hU D)

/-- The fraction has precisely the original order at every prime meeting the open. -/
theorem affineRationalEquation_order {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    [Nonempty U] [UniqueFactorizationMonoid Γ(X.toScheme, U)]
    (D : X.WeilDivisor) (C : X.PrimeCurve) (hC : C.genericPoint ∈ U) :
    C.order (X.affineRationalEquation hU D) = D C := by
  letI : IsNoetherianRing Γ(X.toScheme, U) := X.affineSections_isNoetherianRing hU
  letI : IsFractionRing Γ(X.toScheme, U) X.toScheme.functionField :=
    functionField_isFractionRing_of_isAffineOpen X.toScheme U hU
  rw [C.order_eq_affinePrincipalOrder hU hC]
  exact (RingTheory.affinePrincipalOrder_fractionOfDivisorCoordinates
    Γ(X.toScheme, U) X.toScheme.functionField (X.affineDivisorCoordinates hU D)
    (C.affineHeightOnePrime hU hC)).trans (X.affineDivisorCoordinates_apply hU D C hC)

/-- Subtracting this principal divisor leaves coefficients only outside the open. -/
theorem sub_principal_affineRationalEquation_apply {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) [Nonempty U] [UniqueFactorizationMonoid Γ(X.toScheme, U)]
    (D : X.WeilDivisor) (C : X.PrimeCurve) (hC : C.genericPoint ∈ U) :
    (D - X.principalDivisor (X.affineRationalEquation hU D)) C = 0 := by
  change D C - C.order (X.affineRationalEquation hU D) = 0
  rw [X.affineRationalEquation_order hU D C hC, sub_self]

end KltDP.Geometry.NormalProjectiveSurface
