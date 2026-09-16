import KltDP.Geometry.AffinePrincipalSupport
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.RingTheory.Localization.Basic

/-!
# Transport of the normalized DVR order

The integer order used here is the actual pinned adic valuation, with its
exponent negated so that a uniformizer has order `+1`. A ring equivalence
between DVRs preserves that exact normalization: every nonzero element is
a unit times a power of a uniformizer. Agreement on a DVR then determines
the valuation on its actual fraction field by localization uniqueness.

For two presentations of one localization, the compatibility of their
maps into a common fraction field is itself proved from the scalar towers
and uniqueness of localization algebra homomorphisms. The final wrapper
applies this to an actual affine open and its structure-sheaf stalk.

Reused pinned Mathlib declarations (commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, Apache-2.0):
* `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`;
* `HeightOneSpectrum.intValuation_singleton`;
* `Submonoid.LocalizationMap.epic_of_localizationMap`;
* `IsLocalization.algEquiv` and `IsLocalization.algHom_subsingleton`;
* `IsAffineOpen.isLocalization_stalk` and `functionField_isScalarTower`.

The newer external `Ring.ordFrac_ringEquiv` theorem was also reviewed in
the frozen Weil-divisor source. It concerns a different order definition
and is not used or assumed here. This module proves equality for the
existing `DivisorOrder` definition, without a comparison axiom.
-/

noncomputable section

open IsDedekindDomain
open scoped Multiplicative

universe u v w z

namespace KltDP.RingTheory

section DVR

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {S : Type v} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

/-- The actual normalized adic valuations on two isomorphic DVRs agree.
The normalization is proved using units and an irreducible uniformizer. -/
theorem dvrIntValuation_eq_of_ringEquiv (e : R ≃+* S) (r : R) :
    (dvrHeightOnePrime S).intValuation (e r) =
      (dvrHeightOnePrime R).intValuation r := by
  by_cases hr : r = 0
  · simp only [hr, map_zero]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have heϖ : Irreducible (e ϖ) := (MulEquiv.irreducible_iff e).mpr hϖ
  have hϖR : (dvrHeightOnePrime R).intValuation ϖ =
      ((Multiplicative.ofAdd (-1) : Multiplicative ℤ) : ℤₘ₀) :=
    (dvrHeightOnePrime R).intValuation_singleton hϖ.ne_zero hϖ.maximalIdeal_eq
  have hϖS : (dvrHeightOnePrime S).intValuation (e ϖ) =
      ((Multiplicative.ofAdd (-1) : Multiplicative ℤ) : ℤₘ₀) :=
    (dvrHeightOnePrime S).intValuation_singleton heϖ.ne_zero heϖ.maximalIdeal_eq
  obtain ⟨n, a, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  have haR : (dvrHeightOnePrime R).intValuation (a : R) = 1 :=
    Valuation.Integers.one_of_isUnit' a.isUnit
      (fun x => (dvrHeightOnePrime R).intValuation_le_one x)
  have haS : (dvrHeightOnePrime S).intValuation (e (a : R)) = 1 :=
    Valuation.Integers.one_of_isUnit' (a.isUnit.map e)
      (fun x => (dvrHeightOnePrime S).intValuation_le_one x)
  simp only [map_mul, map_pow, haR, haS, hϖR, hϖS, one_mul]

variable (K : Type w) [Field K]
variable [Algebra R K] [IsFractionRing R K] [Algebra S K] [IsFractionRing S K]

/-- Compatible presentations of two isomorphic DVRs inside a common
actual fraction field give the same fraction-field valuation. -/
theorem fractionFieldValuation_eq_of_ringEquiv (e : R ≃+* S)
    (hcompat : ∀ r : R, algebraMap S K (e r) = algebraMap R K r) :
    fractionFieldValuation R K = fractionFieldValuation S K := by
  have hbase (r : R) :
      fractionFieldValuation R K (algebraMap R K r) =
        fractionFieldValuation S K (algebraMap R K r) := by
    calc
      fractionFieldValuation R K (algebraMap R K r) =
          (dvrHeightOnePrime R).intValuation r :=
        (dvrHeightOnePrime R).valuation_of_algebraMap r
      _ = (dvrHeightOnePrime S).intValuation (e r) :=
        (dvrIntValuation_eq_of_ringEquiv e r).symm
      _ = fractionFieldValuation S K (algebraMap S K (e r)) :=
        ((dvrHeightOnePrime S).valuation_of_algebraMap (e r)).symm
      _ = fractionFieldValuation S K (algebraMap R K r) :=
        congrArg (fractionFieldValuation S K) (hcompat r)
  have hhom :
      (fractionFieldValuation R K).toMonoidWithZeroHom.toMonoidHom =
        (fractionFieldValuation S K).toMonoidWithZeroHom.toMonoidHom :=
    (IsLocalization.toLocalizationMap (nonZeroDivisors R) K).epic_of_localizationMap
      hbase
  exact Valuation.ext (fun x => DFunLike.congr_fun hhom x)

/-- Exact agreement of the integer orders, including their sign, for
compatible isomorphic DVRs in a common actual fraction field. -/
theorem divisorOrder_eq_of_ringEquiv (e : R ≃+* S)
    (hcompat : ∀ r : R, algebraMap S K (e r) = algebraMap R K r) (f : Kˣ) :
    divisorOrder R K f = divisorOrder S K f := by
  apply (divisorOrder_eq_iff R K f (divisorOrder S K f)).mpr
  rw [fractionFieldValuation_eq_of_ringEquiv K e hcompat]
  exact (coe_neg_divisorOrder S K f).symm

end DVR

section Localization

variable (A : Type u) [CommRing A] (M : Submonoid A)
variable (R : Type v) [CommRing R] [Algebra A R] [IsLocalization M R]
variable (S : Type w) [CommRing S] [Algebra A S]
variable (K : Type z) [CommRing K] [Algebra A K] [Algebra R K] [Algebra S K]
variable [IsScalarTower A R K] [IsScalarTower A S K]

include M

/-- The maps from an actual localization into a common algebra agree
after any equivalence over the base ring. Compatibility follows from
localization uniqueness, and is not an additional equality hypothesis. -/
theorem localizationAlgEquiv_algebraMap (e : R ≃ₐ[A] S) (r : R) :
    algebraMap S K (e r) = algebraMap R K r := by
  letI : Subsingleton (R →ₐ[A] K) := IsLocalization.algHom_subsingleton M
  have h : (IsScalarTower.toAlgHom A S K).comp e.toAlgHom =
      IsScalarTower.toAlgHom A R K := Subsingleton.elim _ _
  exact DFunLike.congr_fun h r

end Localization

section DVRLocalization

variable (A : Type u) [CommRing A] (M : Submonoid A)
variable (R : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Algebra A R] [IsLocalization M R]
variable (S : Type w) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
variable [Algebra A S] [IsLocalization M S]
variable (K : Type z) [Field K] [Algebra A K]
variable [Algebra R K] [IsFractionRing R K] [Algebra S K] [IsFractionRing S K]
variable [IsScalarTower A R K] [IsScalarTower A S K]

include A M

/-- Any two actual DVR presentations of the same localization give
identical orders in their common actual fraction field. -/
theorem divisorOrder_eq_of_isLocalization (f : Kˣ) :
    divisorOrder R K f = divisorOrder S K f :=
  divisorOrder_eq_of_ringEquiv K (IsLocalization.algEquiv M R S).toRingEquiv
    (localizationAlgEquiv_algebraMap A M R S K (IsLocalization.algEquiv M R S)) f

end DVRLocalization

end KltDP.RingTheory

namespace KltDP.Geometry

open AlgebraicGeometry

local instance (X : Scheme.{u}) [IsIntegral X] (x : X) :
    IsDomain (X.presheaf.stalk x) := integralSchemeStalk_isDomain X x

variable (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
variable [IsNoetherianRing Γ(X, U)] [IsIntegrallyClosed Γ(X, U)]

/-- A height-one point of an actual normal Noetherian affine chart has
a DVR stalk, by the canonical equivalence with its prime localization. -/
theorem affineStalk_isDiscreteValuationRing (hU : IsAffineOpen U) (x : U)
    (hp : (hU.primeIdealOf x).asIdeal.height = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  letI : IsDiscreteValuationRing (Localization.AtPrime (hU.primeIdealOf x).asIdeal) :=
    RingTheory.heightOneLocalization_isDiscreteValuationRing Γ(X, U)
      ⟨hU.primeIdealOf x, hp⟩
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf x).asIdeal) (X.presheaf.stalk x))

/-- The actual affine prime-localization order equals the order in the
original structure-sheaf stalk and original scheme function field.
The stalk DVR property and both maps into that field are derived. -/
theorem affinePrincipalOrder_eq_stalkDivisorOrder (hU : IsAffineOpen U) (x : U)
    (hp : (hU.primeIdealOf x).asIdeal.height = 1) (f : X.functionFieldˣ) :
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      affineStalk_isDiscreteValuationRing X U hU x hp
    RingTheory.affinePrincipalOrder Γ(X, U) X.functionField ⟨hU.primeIdealOf x, hp⟩ f =
      stalkDivisorOrder X x f := by
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    affineStalk_isDiscreteValuationRing X U hU x hp
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  letI : IsDiscreteValuationRing (Localization.AtPrime (hU.primeIdealOf x).asIdeal) :=
    RingTheory.heightOneLocalization_isDiscreteValuationRing Γ(X, U)
      ⟨hU.primeIdealOf x, hp⟩
  letI : Algebra (Localization.AtPrime (hU.primeIdealOf x).asIdeal) X.functionField :=
    RingTheory.heightOneFractionFieldAlgebra Γ(X, U) X.functionField
      ⟨hU.primeIdealOf x, hp⟩
  letI : IsScalarTower Γ(X, U)
      (Localization.AtPrime (hU.primeIdealOf x).asIdeal) X.functionField :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.AtPrime (hU.primeIdealOf x).asIdeal) X.functionField
      (hU.primeIdealOf x).asIdeal.primeCompl (nonZeroDivisors Γ(X, U))
      (hU.primeIdealOf x).asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
      X.functionField :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (hU.primeIdealOf x).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf x).asIdeal) X.functionField
  exact RingTheory.divisorOrder_eq_of_isLocalization Γ(X, U)
    (hU.primeIdealOf x).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf x).asIdeal) (X.presheaf.stalk x)
    X.functionField f

end KltDP.Geometry
