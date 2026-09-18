import KltDP.Geometry.QuadraticCoverIntegral

/-!
# One original denominator for both quadratic fraction coefficients

The two existing coordinates of the original quadratic algebra over the
base fraction field each admit a base denominator. Their product clears
both coordinates at once. The numerator belongs to the original
quadratic algebra and is mapped by the original coefficient homomorphism.
No fraction-field comparison for the quadratic algebra is assumed.
-/

noncomputable section
universe u v

namespace KltDP.Geometry.QuadraticCover

variable {R : Type u} [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- A single nonzero original base denominator clears the actual quadratic element. -/
theorem exists_common_base_denominator (s : R)
    (z : CoverAlgebra (algebraMap R K s)) :
    ∃ (d : nonZeroDivisors R) (y : CoverAlgebra s),
      baseChangeCoeffHom (S := K) s y =
        algebraMap K (CoverAlgebra (algebraMap R K s)) (algebraMap R K d) * z := by
  let t := algebraMap R K s
  obtain ⟨⟨a, d⟩, ha⟩ := IsLocalization.surj (nonZeroDivisors R) (constantCoeff t z)
  obtain ⟨⟨b, e⟩, hb⟩ := IsLocalization.surj (nonZeroDivisors R) (rootCoeff t z)
  have hca : algebraMap R K (a * e) =
      (algebraMap R K d * algebraMap R K e) * constantCoeff t z := by
    rw [map_mul, ← ha]
    ring
  have hcb : algebraMap R K (b * d) =
      (algebraMap R K d * algebraMap R K e) * rootCoeff t z := by
    rw [map_mul, ← hb]
    ring
  refine ⟨d * e, ofCoeffs s (a * e) (b * d), ?_⟩
  rw [baseChangeCoeffHom_ofCoeffs, ← Algebra.smul_def]
  apply (coordinatesEquiv t).injective
  apply Prod.ext
  · change constantCoeff t (ofCoeffs t (algebraMap R K (a * e))
        (algebraMap R K (b * d))) =
      constantCoeff t ((algebraMap R K (↑(d * e) : R)) • z)
    rw [constantCoeff_ofCoeffs, map_smul]
    simpa only [Submonoid.coe_mul, map_mul, smul_eq_mul] using hca
  · change rootCoeff t (ofCoeffs t (algebraMap R K (a * e))
        (algebraMap R K (b * d))) =
      rootCoeff t ((algebraMap R K (↑(d * e) : R)) • z)
    rw [rootCoeff_ofCoeffs, map_smul]
    simpa only [Submonoid.coe_mul, map_mul, smul_eq_mul] using hcb

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.exists_common_base_denominator
