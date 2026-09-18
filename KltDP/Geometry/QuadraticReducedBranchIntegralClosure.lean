import KltDP.Geometry.QuadraticReducedBranchDenominators
import KltDP.Geometry.QuadraticConjugationScalars
import KltDP.Geometry.OriginalQuadraticSurjective

/-!
# Original quadratic coefficients contain all integral elements after base fractions

In the actual quadratic algebra over the original fraction field, an
element integral over the original normal base has integral conjugate.
Their sum and product are the actual trace and norm scalars. Inverting
two in the original base puts the constant coordinate in that base.
The norm then puts s times the square of the root coordinate in the base.
The proved reduced-branch denominator descent puts the root coordinate
there as well. The original coefficient map supplies the resulting
preimage in the original quadratic algebra.

This is the actual integral-closure containment. It does not assume a
quadratic fraction-field comparison, a normal cover, or any valuation.
-/

noncomputable section
universe u v

namespace KltDP.Geometry.QuadraticCover

variable {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every element integral over the original base has an original quadratic-algebra preimage. -/
theorem exists_preimage_of_integral_reduced_branch
    (s : R) (hs : s ≠ 0) (h2 : IsUnit (2 : R))
    (hred : IsReduced (R ⧸ Ideal.span ({s} : Set R)))
    (z : CoverAlgebra (algebraMap R K s)) (hz : IsIntegral R z) :
    ∃ y : CoverAlgebra s, baseChangeCoeffHom (S := K) s y = z := by
  let t := algebraMap R K s
  let aK := constantCoeff t z
  let bK := rootCoeff t z
  have hj : IsIntegral R (conjugation t z) :=
    hz.map ((conjugation t).toAlgHom.restrictScalars R)
  have hsum : IsIntegral R (2 * aK) := by
    apply (isIntegral_algebraMap_iff (algebraMap_injective t)).mp
    rw [← add_conjugation_eq_scalar]
    exact hz.add hj
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hsum
  obtain ⟨u, hu⟩ := h2
  let a₀ : R := (↑u⁻¹ : R) * a
  have huK : algebraMap R K (u : R) = 2 := by rw [hu, map_ofNat]
  have ha₀ : algebraMap R K a₀ = aK := by
    calc
      algebraMap R K a₀ = algebraMap R K (↑u⁻¹ : R) * (2 * aK) := by
        rw [map_mul, ha]
      _ = algebraMap R K (↑u⁻¹ : R) * (algebraMap R K (u : R) * aK) := by rw [huK]
      _ = aK := by
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  have hnorm : IsIntegral R (aK ^ 2 - t * bK ^ 2) := by
    apply (isIntegral_algebraMap_iff (algebraMap_injective t)).mp
    rw [← mul_conjugation_eq_scalar]
    exact hz.mul hj
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hnorm
  have hcoeff : algebraMap R K (a₀ ^ 2 - c) = algebraMap R K s * bK ^ 2 := by
    rw [map_sub, map_pow, ha₀, hc]
    change aK ^ 2 - (aK ^ 2 - t * bK ^ 2) = t * bK ^ 2
    ring
  obtain ⟨b₀, hb₀⟩ := coefficient_mem_base_of_branch_mul_sq K s hs hred bK
    (a₀ ^ 2 - c) hcoeff
  refine ⟨ofCoeffs s a₀ b₀, ?_⟩
  rw [baseChangeCoeffHom_ofCoeffs, ha₀, hb₀]
  exact ofCoeffs_coefficients t z

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.exists_preimage_of_integral_reduced_branch
