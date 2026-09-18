import KltDP.Geometry.QuadraticFractionCommonDenominator
import KltDP.Geometry.OriginalQuadraticSurjective

/-!
# The actual quadratic fraction algebra under the original coefficient map

The original base-change coefficient homomorphism supplies the algebra
structure. Its proved injectivity and the original common denominator
give the pinned fraction-field criterion when the actual quadratic
polynomial over the base fraction field is irreducible. The scalar tower
is proved from that same original homomorphism's scalar compatibility.
No replacement fraction map or fraction-field comparison is assumed.
-/

noncomputable section
universe u v

namespace KltDP.Geometry.QuadraticCover

variable {R : Type u} [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The algebra structure furnished by the original quadratic coefficient map. -/
def coefficientAlgebra (s : R) :
    Algebra (CoverAlgebra s) (CoverAlgebra (algebraMap R K s)) :=
  (baseChangeCoeffHom (S := K) s).toRingHom.toAlgebra

/-- The original scalar map is retained after introducing the coefficient algebra. -/
theorem coefficientAlgebra_isScalarTower (s : R) :
    letI := coefficientAlgebra K s
    IsScalarTower R (CoverAlgebra s) (CoverAlgebra (algebraMap R K s)) := by
  letI := coefficientAlgebra K s
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact ((baseChangeCoeffHom (S := K) s).commutes r).symm

/-- The actual field quadratic algebra is the fraction field of the original quotient. -/
theorem coefficientAlgebra_isFractionRing (s : R)
    [Fact (Irreducible (polynomial (algebraMap R K s)))] :
    letI := coefficientAlgebra K s
    IsFractionRing (CoverAlgebra s) (CoverAlgebra (algebraMap R K s)) := by
  letI := coefficientAlgebra K s
  letI : FaithfulSMul (CoverAlgebra s) (CoverAlgebra (algebraMap R K s)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (baseChangeCoeffHom_injective s (IsFractionRing.injective R K))
  apply IsFractionRing.of_field
  intro z
  obtain ⟨d, y, hy⟩ := exists_common_base_denominator K s z
  refine ⟨y, algebraMap R (CoverAlgebra s) d, ?_⟩
  have hden : algebraMap (CoverAlgebra s) (CoverAlgebra (algebraMap R K s))
      (algebraMap R (CoverAlgebra s) d) =
      algebraMap K (CoverAlgebra (algebraMap R K s)) (algebraMap R K d) :=
    baseChangeCoeffHom_algebraMap s d
  have hdK : algebraMap R K d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
  have hdQ : algebraMap (CoverAlgebra s) (CoverAlgebra (algebraMap R K s))
      (algebraMap R (CoverAlgebra s) d) ≠ 0 := by
    rw [hden]
    exact (map_ne_zero_iff _ (algebraMap_injective (algebraMap R K s))).mpr hdK
  apply (eq_div_iff hdQ).mpr
  rw [hden, mul_comm]
  exact hy.symm

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.coefficientAlgebra_isFractionRing
