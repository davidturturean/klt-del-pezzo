import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integers

/-!
# Integer orders from actual DVR stalks

The pinned Mathlib already extends a Dedekind-domain prime valuation to its
fraction field. For a DVR, the prime is its actual maximal ideal. This
valuation sends a uniformizer to the multiplicative integer exponent `-1`.
We negate that exponent, obtaining an integer order that sends a uniformizer
to `+1` and every local unit to zero.

Orders reuse Mathlib's existing `HeightOneSpectrum.valuationOfNeZero` on
nonzero rational functions, represented by units of the actual fraction
field. Their additive homomorphism structure proves the
product and inverse formulas without choosing numerators or uniformizers.
The algebra-map comparison is with the pinned valuation itself; no equality
with an external order-of-vanishing definition is assumed.

The scheme adapter uses the actual structure-sheaf stalk and function field.
Its explicit DVR hypothesis is not asserted for all scheme points here.
Deriving it at prime-curve generic points and proving finite principal support
remain separate adapters. See `docs/WEIL_DIVISOR_BACKPORT_ASSESSMENT.md` for
the source review and the distinction from the later `Ring.ordFrac` API.
-/

noncomputable section

open IsDedekindDomain
open scoped Multiplicative

universe u v

namespace KltDP.RingTheory

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual maximal ideal of a DVR, as a nonzero prime of its Dedekind
domain. Its nonzeroness is part of the definition of a DVR. -/
def dvrHeightOnePrime : HeightOneSpectrum R where
  asIdeal := IsLocalRing.maximalIdeal R
  isPrime := inferInstance
  ne_bot := IsDiscreteValuationRing.not_a_field R

@[simp]
theorem dvrHeightOnePrime_asIdeal :
    (dvrHeightOnePrime R).asIdeal = IsLocalRing.maximalIdeal R := rfl

/-- The existing adic valuation, extended to the actual fraction field. -/
def fractionFieldValuation : Valuation K ℤₘ₀ :=
  (dvrHeightOnePrime R).valuation K

/-- Extract the integer exponent of the nonzero valuation of a field unit.
This is still the valuation convention, with exponent `-1` on a uniformizer. -/
def valuationExponentHom : Kˣ →* Multiplicative ℤ :=
  (dvrHeightOnePrime R).valuationOfNeZero

/-- The reused nonzero valuation is exactly exponent extraction from
the value of the original valuation on units. -/
theorem valuationExponentHom_eq_unitsWithZeroEquiv (f : Kˣ) :
    valuationExponentHom R K f =
      WithZero.unitsWithZeroEquiv
        (Units.map (fractionFieldValuation R K).toMonoidWithZeroHom.toMonoidHom f) := by
  apply WithZero.coe_inj.mp
  exact ((dvrHeightOnePrime R).valuationOfNeZero_eq f).trans
    (WithZero.coe_unitsWithZeroEquiv_eq_units_val
      (Units.map (fractionFieldValuation R K).toMonoidWithZeroHom.toMonoidHom f)).symm

/-- The additive integer order on nonzero elements of the actual fraction
field. The minus sign changes the adic exponent into divisor order. -/
def divisorOrderHom : Additive Kˣ →+ ℤ :=
  -(valuationExponentHom R K).toAdditive'

/-- Integer order, with a multiplicative unit argument. -/
def divisorOrder (f : Kˣ) : ℤ :=
  divisorOrderHom R K (Additive.ofMul f)

theorem divisorOrder_def (f : Kˣ) :
    divisorOrder R K f =
      -Multiplicative.toAdd (valuationExponentHom R K f) := rfl

/-- The exact normalization relation with the original fraction-field
valuation. In particular, no order convention is hidden in the wrappers. -/
theorem coe_neg_divisorOrder (f : Kˣ) :
    ((Multiplicative.ofAdd (-divisorOrder R K f) : Multiplicative ℤ) : ℤₘ₀) =
      fractionFieldValuation R K (f : K) := by
  rw [divisorOrder_def, neg_neg]
  exact (dvrHeightOnePrime R).valuationOfNeZero_eq f

/-- Characterization of an integer order by the value of the actual
fraction-field valuation. -/
theorem divisorOrder_eq_iff (f : Kˣ) (n : ℤ) :
    divisorOrder R K f = n ↔
      fractionFieldValuation R K (f : K) =
        ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : ℤₘ₀) := by
  constructor
  · intro h
    rw [← coe_neg_divisorOrder R K f, h]
  · intro h
    have h' := (coe_neg_divisorOrder R K f).trans h
    have h'' := congrArg Multiplicative.toAdd (WithZero.coe_inj.mp h')
    exact neg_injective h''

@[simp]
theorem divisorOrder_one : divisorOrder R K 1 = 0 :=
  (divisorOrderHom R K).map_zero

theorem divisorOrder_mul (f g : Kˣ) :
    divisorOrder R K (f * g) = divisorOrder R K f + divisorOrder R K g :=
  (divisorOrderHom R K).map_add (Additive.ofMul f) (Additive.ofMul g)

@[simp]
theorem divisorOrder_inv (f : Kˣ) :
    divisorOrder R K f⁻¹ = -divisorOrder R K f :=
  map_neg (divisorOrderHom R K) (Additive.ofMul f)

/-- A nonzero local element, regarded as a unit in its actual fraction
field. The nonzeroness proof uses the fraction-field embedding. -/
def fractionFieldUnit (r : R) (hr : r ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap R K r) (fun h =>
    hr ((IsFractionRing.injective R K) (by simpa only [map_zero] using h)))

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[simp]
theorem fractionFieldUnit_val (r : R) (hr : r ≠ 0) :
    (fractionFieldUnit R K r hr : K) = algebraMap R K r := rfl

/-- Comparison for a nonzero local element with the pinned valuation on
the local ring, before extension to its fraction field. -/
theorem divisorOrder_algebraMap_eq_iff (r : R) (hr : r ≠ 0) (n : ℤ) :
    divisorOrder R K (fractionFieldUnit R K r hr) = n ↔
      (dvrHeightOnePrime R).intValuation r =
        ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : ℤₘ₀) := by
  rw [divisorOrder_eq_iff]
  change (dvrHeightOnePrime R).valuation K (algebraMap R K r) = _ ↔ _
  rw [HeightOneSpectrum.valuation_of_algebraMap]

/-- Every actual local unit has valuation one in the fraction field. -/
theorem fractionFieldValuation_algebraMap_of_isUnit {r : R} (hr : IsUnit r) :
    fractionFieldValuation R K (algebraMap R K r) = 1 :=
  Valuation.Integers.one_of_isUnit' hr
    (fun a => (dvrHeightOnePrime R).valuation_le_one (K := K) a)

/-- The integer order of an actual local unit is zero. -/
@[simp]
theorem divisorOrder_map_unit (r : Rˣ) :
    divisorOrder R K (Units.map (algebraMap R K) r) = 0 := by
  apply (divisorOrder_eq_iff R K _ 0).mpr
  change fractionFieldValuation R K (algebraMap R K (r : R)) = _
  rw [fractionFieldValuation_algebraMap_of_isUnit R K r.isUnit]
  simp

/-- The same unit-vanishing statement for a local element supplied with
an `IsUnit` proof, using its nonzero fraction-field image. -/
theorem divisorOrder_algebraMap_of_isUnit {r : R} (hr : IsUnit r) :
    divisorOrder R K (fractionFieldUnit R K r hr.ne_zero) = 0 := by
  apply (divisorOrder_eq_iff R K _ 0).mpr
  change fractionFieldValuation R K (algebraMap R K r) = _
  rw [fractionFieldValuation_algebraMap_of_isUnit R K hr]
  simp

/-- A uniformizer has integer order `+1`, with the sign obtained from the
pinned valuation's explicit singleton-ideal calculation. -/
theorem divisorOrder_uniformizer (ϖ : R) (hϖ : Irreducible ϖ) :
    divisorOrder R K (fractionFieldUnit R K ϖ hϖ.ne_zero) = 1 := by
  apply (divisorOrder_algebraMap_eq_iff R K ϖ hϖ.ne_zero 1).mpr
  exact (dvrHeightOnePrime R).intValuation_singleton hϖ.ne_zero hϖ.maximalIdeal_eq

/-- The order homomorphism takes the value one on an actual local
uniformizer; in particular its normalization is nontrivial. -/
theorem exists_uniformizer_divisorOrder_one :
    ∃ (ϖ : R) (hϖ : Irreducible ϖ),
      divisorOrder R K (fractionFieldUnit R K ϖ hϖ.ne_zero) = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact ⟨ϖ, hϖ, divisorOrder_uniformizer R K ϖ hϖ⟩

end KltDP.RingTheory

namespace KltDP.Geometry

open AlgebraicGeometry

/-- An integral scheme's actual stalk embeds in its actual function
field, so it is a domain. This supplies the domain input of the DVR class. -/
theorem integralSchemeStalk_isDomain (X : Scheme.{u}) [IsIntegral X] (x : X) :
    IsDomain (X.presheaf.stalk x) :=
  Function.Injective.isDomain (algebraMap (X.presheaf.stalk x) X.functionField)
    (IsFractionRing.injective _ _)

local instance (X : Scheme.{u}) [IsIntegral X] (x : X) :
    IsDomain (X.presheaf.stalk x) := integralSchemeStalk_isDomain X x

variable (X : Scheme.{u}) [IsIntegral X] (x : X)
variable [IsDiscreteValuationRing (X.presheaf.stalk x)]

/-- Integer order on actual nonzero rational functions at an actual DVR
stalk. No geometric identification of the point is assumed. -/
def stalkDivisorOrderHom : Additive X.functionFieldˣ →+ ℤ :=
  RingTheory.divisorOrderHom (X.presheaf.stalk x) X.functionField

/-- The same actual stalk order with a multiplicative unit argument. -/
def stalkDivisorOrder (f : X.functionFieldˣ) : ℤ :=
  stalkDivisorOrderHom X x (Additive.ofMul f)

@[simp]
theorem stalkDivisorOrder_one : stalkDivisorOrder X x 1 = 0 :=
  RingTheory.divisorOrder_one (X.presheaf.stalk x) X.functionField

theorem stalkDivisorOrder_mul (f g : X.functionFieldˣ) :
    stalkDivisorOrder X x (f * g) = stalkDivisorOrder X x f + stalkDivisorOrder X x g :=
  RingTheory.divisorOrder_mul (X.presheaf.stalk x) X.functionField f g

@[simp]
theorem stalkDivisorOrder_inv (f : X.functionFieldˣ) :
    stalkDivisorOrder X x f⁻¹ = -stalkDivisorOrder X x f :=
  RingTheory.divisorOrder_inv (X.presheaf.stalk x) X.functionField f

/-- Actual stalk units have order zero as rational functions. -/
@[simp]
theorem stalkDivisorOrder_map_unit (r : (X.presheaf.stalk x)ˣ) :
    stalkDivisorOrder X x
      (Units.map (algebraMap (X.presheaf.stalk x) X.functionField) r) = 0 :=
  RingTheory.divisorOrder_map_unit (X.presheaf.stalk x) X.functionField r

/-- Exact comparison with the valuation on the actual stalk's maximal
ideal, for a nonzero stalk element mapped to the function field. -/
theorem stalkDivisorOrder_algebraMap_eq_iff (r : X.presheaf.stalk x)
    (hr : r ≠ 0) (n : ℤ) :
    stalkDivisorOrder X x
        (RingTheory.fractionFieldUnit (X.presheaf.stalk x) X.functionField r hr) = n ↔
      (RingTheory.dvrHeightOnePrime (X.presheaf.stalk x)).intValuation r =
        ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : ℤₘ₀) :=
  RingTheory.divisorOrder_algebraMap_eq_iff (X.presheaf.stalk x) X.functionField r hr n

/-- A uniformizer in the actual scheme stalk has order `+1` in the
actual function field. -/
theorem stalkDivisorOrder_uniformizer (ϖ : X.presheaf.stalk x) (hϖ : Irreducible ϖ) :
    stalkDivisorOrder X x
      (RingTheory.fractionFieldUnit (X.presheaf.stalk x) X.functionField ϖ hϖ.ne_zero) = 1 :=
  RingTheory.divisorOrder_uniformizer (X.presheaf.stalk x) X.functionField ϖ hϖ

end KltDP.Geometry
