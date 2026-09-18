import KltDP.Geometry.AffineBlowupRegularPairExceptionalDVR
import KltDP.Geometry.DivisorOrder
import Mathlib.Algebra.Group.Irreducible.Lemmas

/-!
# Original branch equations have exceptional order one

The original first parameter is the proved uniformizer. The original
second parameter is its product with the actual chart fraction, which
is a unit at the exceptional generic prime because its exceptional
coordinate is the nonzero polynomial variable. Both branch orders are
therefore one. An original base unit has exceptional order zero.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup

universe u v

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)
variable (ha : (a : R) ∈ nonZeroDivisors R)
variable (hb : Ideal.Quotient.mk (Ideal.span {(a : R)}) (b : R) ∈
  nonZeroDivisors (R ⧸ Ideal.span {(a : R)}))
variable (hI : I = Ideal.span {(a : R), (b : R)}) [I.IsPrime]

/-- The actual base-to-chart map followed by the actual exceptional
generic localization map. -/
def exceptionalGenericBaseMap : R →+* exceptionalGenericLocalRing I a b ha hb hI :=
  (algebraMap (chartRing I a) (exceptionalGenericLocalRing I a b ha hb hI)).comp
    (chartBaseMap I a)

/-- The original chart fraction is a unit at the actual exceptional
generic point; its original exceptional coordinate is the nonzero `X`. -/
theorem exceptionalGenericFraction_isUnit :
    IsUnit (algebraMap (chartRing I a) (exceptionalGenericLocalRing I a b ha hb hI)
      (chartFraction I a b)) := by
  have hnot : chartFraction I a b ∉ (exceptionalGenericPrime I a b ha hb hI).asIdeal := by
    change chartFraction I a b ∉ chartCenterIdeal I a
    rw [← exceptionalCoordinateMap_ker I a b ha hb hI]
    change exceptionalCoordinateMap I a b ha hb hI (chartFraction I a b) ≠ 0
    rw [exceptionalCoordinateMap_fraction]
    exact Polynomial.X_ne_zero
  exact IsLocalization.map_units (exceptionalGenericLocalRing I a b ha hb hI)
    (⟨chartFraction I a b, hnot⟩ :
      (exceptionalGenericPrime I a b ha hb hI).asIdeal.primeCompl)

/-- The original second branch equation also becomes a uniformizer,
using the actual Rees fraction relation. -/
theorem exceptionalGeneric_second_irreducible [IsDomain R] :
    Irreducible (exceptionalGenericBaseMap I a b ha hb hI (b : R)) := by
  have hmul : exceptionalGenericBaseMap I a b ha hb hI (b : R) =
      exceptionalGenericParameter I a b ha hb hI *
        algebraMap (chartRing I a) (exceptionalGenericLocalRing I a b ha hb hI)
          (chartFraction I a b) := by
    change algebraMap (chartRing I a) (exceptionalGenericLocalRing I a b ha hb hI)
      (chartBaseMap I a (b : R)) =
      algebraMap (chartRing I a) (exceptionalGenericLocalRing I a b ha hb hI)
        (chartBaseMap I a (a : R)) *
      algebraMap (chartRing I a) (exceptionalGenericLocalRing I a b ha hb hI)
        (chartFraction I a b)
    rw [← map_mul, chartBaseMap_mul_chartFraction]
  rw [hmul]
  exact (irreducible_mul_isUnit (exceptionalGenericFraction_isUnit I a b ha hb hI)).mpr
    (exceptionalGenericParameter_irreducible I a b ha hb hI)

variable [IsDomain R] [IsNoetherianRing R]
variable (K : Type v) [Field K]
variable [Algebra (exceptionalGenericLocalRing I a b ha hb hI) K]
variable [IsFractionRing (exceptionalGenericLocalRing I a b ha hb hI) K]

/-- The original first branch equation has normalized exceptional
order `+1` in any actual fraction field of the exceptional stalk. -/
theorem exceptionalGeneric_first_order :
    letI : IsDomain (exceptionalGenericLocalRing I a b ha hb hI) :=
      exceptionalGenericLocalRing_isDomain I a b ha hb hI
    letI : IsDiscreteValuationRing (exceptionalGenericLocalRing I a b ha hb hI) :=
      exceptionalGenericLocalRing_isDiscreteValuationRing I a b ha hb hI
    KltDP.RingTheory.divisorOrder (exceptionalGenericLocalRing I a b ha hb hI) K
      (KltDP.RingTheory.fractionFieldUnit (exceptionalGenericLocalRing I a b ha hb hI) K
        (exceptionalGenericParameter I a b ha hb hI)
        (exceptionalGenericParameter_ne_zero I a b ha hb hI)) = 1 := by
  letI := exceptionalGenericLocalRing_isDomain I a b ha hb hI
  letI := exceptionalGenericLocalRing_isDiscreteValuationRing I a b ha hb hI
  exact KltDP.RingTheory.divisorOrder_uniformizer
    (exceptionalGenericLocalRing I a b ha hb hI) K
    (exceptionalGenericParameter I a b ha hb hI)
    (exceptionalGenericParameter_irreducible I a b ha hb hI)

/-- The original second branch equation has the same normalized
exceptional order `+1`. -/
theorem exceptionalGeneric_second_order :
    letI : IsDomain (exceptionalGenericLocalRing I a b ha hb hI) :=
      exceptionalGenericLocalRing_isDomain I a b ha hb hI
    letI : IsDiscreteValuationRing (exceptionalGenericLocalRing I a b ha hb hI) :=
      exceptionalGenericLocalRing_isDiscreteValuationRing I a b ha hb hI
    KltDP.RingTheory.divisorOrder (exceptionalGenericLocalRing I a b ha hb hI) K
      (KltDP.RingTheory.fractionFieldUnit (exceptionalGenericLocalRing I a b ha hb hI) K
        (exceptionalGenericBaseMap I a b ha hb hI (b : R))
        (exceptionalGeneric_second_irreducible I a b ha hb hI).ne_zero) = 1 := by
  letI := exceptionalGenericLocalRing_isDomain I a b ha hb hI
  letI := exceptionalGenericLocalRing_isDiscreteValuationRing I a b ha hb hI
  exact KltDP.RingTheory.divisorOrder_uniformizer
    (exceptionalGenericLocalRing I a b ha hb hI) K
    (exceptionalGenericBaseMap I a b ha hb hI (b : R))
    (exceptionalGeneric_second_irreducible I a b ha hb hI)

/-- An original local unit has order zero under the same original
base-to-chart-to-exceptional-stalk map. -/
theorem exceptionalGeneric_unit_order (r : R) (hr : IsUnit r) :
    letI : IsDomain (exceptionalGenericLocalRing I a b ha hb hI) :=
      exceptionalGenericLocalRing_isDomain I a b ha hb hI
    letI : IsDiscreteValuationRing (exceptionalGenericLocalRing I a b ha hb hI) :=
      exceptionalGenericLocalRing_isDiscreteValuationRing I a b ha hb hI
    KltDP.RingTheory.divisorOrder (exceptionalGenericLocalRing I a b ha hb hI) K
      (KltDP.RingTheory.fractionFieldUnit (exceptionalGenericLocalRing I a b ha hb hI) K
        (exceptionalGenericBaseMap I a b ha hb hI r)
        (hr.map (exceptionalGenericBaseMap I a b ha hb hI)).ne_zero) = 0 := by
  letI := exceptionalGenericLocalRing_isDomain I a b ha hb hI
  letI := exceptionalGenericLocalRing_isDiscreteValuationRing I a b ha hb hI
  exact KltDP.RingTheory.divisorOrder_algebraMap_of_isUnit
    (exceptionalGenericLocalRing I a b ha hb hI) K
    (hr.map (exceptionalGenericBaseMap I a b ha hb hI))

end KltDP.Geometry.AffineBlowupRegularPairChart
