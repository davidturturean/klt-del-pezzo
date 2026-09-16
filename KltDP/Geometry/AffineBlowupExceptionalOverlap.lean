import KltDP.Geometry.AffineBlowupConormalOverlap
import Mathlib.RingTheory.Localization.Ideal

/-!
# Actual exceptional quotient restrictions on the Rees chart intersection

The overlap and its ideal are the existing actual homogeneous product
localization and the actual extended center. The pinned localization
surjection theorem descends the two chart localizations to their quotient
rings. The reciprocal-coordinate identity is derived before quotienting,
by cancellation of the proved regular center equation.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

/-- The actual center quotient on the ambient chart intersection. -/
abbrev exceptionalOverlapRing := conormalOverlapRing I a b ⧸ conormalOverlapIdeal I a b

/-- Restriction from the first actual exceptional chart quotient. -/
def exceptionalOverlapLeft : exceptionalChartRing I a →+* exceptionalOverlapRing I a b :=
  Ideal.quotientMap (conormalOverlapIdeal I a b) (conormalOverlapLeft I a b)
    (conormalOverlapLeft_ideal_le I a b)

/-- Restriction from the second actual exceptional chart quotient. -/
def exceptionalOverlapRight : exceptionalChartRing I b →+* exceptionalOverlapRing I a b :=
  Ideal.quotientMap (conormalOverlapIdeal I a b) (conormalOverlapRight I a b)
    (conormalOverlapRight_ideal_le I a b)

@[simp] theorem exceptionalOverlapLeft_mk (x : chartRing I a) :
    exceptionalOverlapLeft I a b (Ideal.Quotient.mk (chartCenterIdeal I a) x) =
      Ideal.Quotient.mk (conormalOverlapIdeal I a b) (conormalOverlapLeft I a b x) := rfl

@[simp] theorem exceptionalOverlapRight_mk (x : chartRing I b) :
    exceptionalOverlapRight I a b (Ideal.Quotient.mk (chartCenterIdeal I b) x) =
      Ideal.Quotient.mk (conormalOverlapIdeal I a b) (conormalOverlapRight I a b x) := rfl

/-- The actual quotient restriction inverts the first chart ratio. -/
theorem exceptionalOverlapLeft_isLocalization :
    letI := (exceptionalOverlapLeft I a b).toAlgebra
    IsLocalization.Away
      (Ideal.Quotient.mk (chartCenterIdeal I a) (chartFraction I a b))
      (exceptionalOverlapRing I a b) := by
  letI := (conormalOverlapLeft I a b).toAlgebra
  letI := (exceptionalOverlapLeft I a b).toAlgebra
  letI := conormalOverlapLeft_isLocalization I a b
  have h := IsLocalization.of_surjective (M := Submonoid.powers (chartFraction I a b))
    (S := conormalOverlapRing I a b)
    (Ideal.Quotient.mk (chartCenterIdeal I a)) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (conormalOverlapIdeal I a b)) Ideal.Quotient.mk_surjective
    (show (Ideal.Quotient.mk (conormalOverlapIdeal I a b)).comp
        (conormalOverlapLeft I a b) =
      (exceptionalOverlapLeft I a b).comp (Ideal.Quotient.mk (chartCenterIdeal I a)) from
        (Ideal.quotientMap_comp_mk (conormalOverlapLeft_ideal_le I a b)).symm)
    (by
      rw [Ideal.mk_ker, Ideal.mk_ker]
      exact (conormalOverlapLeft_map_ideal I a b).ge)
  rw [Submonoid.map_powers] at h
  exact h

/-- The actual quotient restriction inverts the second chart ratio. -/
theorem exceptionalOverlapRight_isLocalization :
    letI := (exceptionalOverlapRight I a b).toAlgebra
    IsLocalization.Away
      (Ideal.Quotient.mk (chartCenterIdeal I b) (chartFraction I b a))
      (exceptionalOverlapRing I a b) := by
  letI := (conormalOverlapRight I a b).toAlgebra
  letI := (exceptionalOverlapRight I a b).toAlgebra
  letI := conormalOverlapRight_isLocalization I a b
  have h := IsLocalization.of_surjective (M := Submonoid.powers (chartFraction I b a))
    (S := conormalOverlapRing I a b)
    (Ideal.Quotient.mk (chartCenterIdeal I b)) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (conormalOverlapIdeal I a b)) Ideal.Quotient.mk_surjective
    (show (Ideal.Quotient.mk (conormalOverlapIdeal I a b)).comp
        (conormalOverlapRight I a b) =
      (exceptionalOverlapRight I a b).comp (Ideal.Quotient.mk (chartCenterIdeal I b)) from
        (Ideal.quotientMap_comp_mk (conormalOverlapRight_ideal_le I a b)).symm)
    (by
      rw [Ideal.mk_ker, Ideal.mk_ker]
      exact (conormalOverlapRight_map_ideal I a b).ge)
  rw [Submonoid.map_powers] at h
  exact h

/-- On the actual ambient overlap, the two actual chart fractions multiply to one. -/
theorem conormalOverlap_chartFractions_mul :
    conormalOverlapLeft I a b (chartFraction I a b) *
      conormalOverlapRight I a b (chartFraction I b a) = 1 := by
  have ha : conormalOverlapBaseMap I a b (a : R) ∈
      nonZeroDivisors (conormalOverlapRing I a b) :=
    conormalOverlapEquationLeft_regular I a b
  have hab := congrArg (conormalOverlapLeft I a b) (chartBaseMap_mul_chartFraction I a b)
  have hba := congrArg (conormalOverlapRight I a b) (chartBaseMap_mul_chartFraction I b a)
  simp only [map_mul, conormalOverlapLeft_baseMap] at hab
  simp only [map_mul, conormalOverlapRight_baseMap] at hba
  apply (mul_cancel_left_mem_nonZeroDivisors ha).mp
  rw [← mul_assoc, hab, hba, mul_one]

/-- The reciprocal-coordinate identity survives in the actual exceptional overlap quotient. -/
theorem exceptionalOverlap_chartFractions_mul :
    exceptionalOverlapLeft I a b
        (Ideal.Quotient.mk (chartCenterIdeal I a) (chartFraction I a b)) *
      exceptionalOverlapRight I a b
        (Ideal.Quotient.mk (chartCenterIdeal I b) (chartFraction I b a)) = 1 := by
  rw [exceptionalOverlapLeft_mk, exceptionalOverlapRight_mk, ← map_mul,
    conormalOverlap_chartFractions_mul, map_one]

end KltDP.Geometry.AffineBlowup
