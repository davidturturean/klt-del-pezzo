import KltDP.Geometry.QuadraticCoverReducedBranch

/-!
# Reduced branch equations clear quadratic coefficient denominators

For a normal domain and a nonzero reduced branch equation s, a fraction b
with s*b^2 in the original ring already belongs to that ring. The square
of s*b belongs to the ring, so normality puts s*b in the ring. Its class
modulo s is nilpotent and hence zero by reducedness; cancellation clears
the original denominator. This is the coefficient descent needed in an
integral-closure proof for the original quadratic algebra, with no
valuation or discrete-valuation-ring premise.
-/

noncomputable section
universe u v

namespace KltDP.Geometry.QuadraticCover

/-- A reduced original branch equation admits no extra fractional root coefficients. -/
theorem coefficient_mem_base_of_branch_mul_sq
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (s : R) (hs : s ≠ 0)
    (hred : IsReduced (R ⧸ Ideal.span ({s} : Set R)))
    (b : K) (a : R) (ha : algebraMap R K a = algebraMap R K s * b ^ 2) :
    ∃ d : R, algebraMap R K d = b := by
  letI := hred
  have hsq : (algebraMap R K s * b) ^ 2 = algebraMap R K (s * a) := by
    calc
      (algebraMap R K s * b) ^ 2 =
          algebraMap R K s * (algebraMap R K s * b ^ 2) := by ring
      _ = algebraMap R K s * algebraMap R K a := by rw [ha]
      _ = algebraMap R K (s * a) := (map_mul _ _ _).symm
  have hint : IsIntegral R ((algebraMap R K s * b) ^ 2) := by
    rw [hsq]
    exact isIntegral_algebraMap
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := R) (K := K) (x := algebraMap R K s * b) (n := 2) (by decide) hint
  have hc2 : c ^ 2 = s * a := by
    apply IsFractionRing.injective R K
    rw [map_pow, hc, hsq]
  have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span ({s} : Set R)) c) := by
    refine ⟨2, ?_⟩
    rw [← map_pow, hc2, map_mul, Ideal.Quotient.mk_singleton_self, zero_mul]
  obtain ⟨d, hd⟩ := (Ideal.Quotient.eq_zero_iff_dvd s c).mp hnil.eq_zero
  have hsK : algebraMap R K s ≠ 0 := by
    intro hzero
    exact hs ((IsFractionRing.injective R K) (by simpa only [map_zero] using hzero))
  refine ⟨d, mul_left_cancel₀ hsK ?_⟩
  rw [← map_mul, ← hd, hc]

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.coefficient_mem_base_of_branch_mul_sq
