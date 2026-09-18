import KltDP.Geometry.QuadraticDomainNonsquare
import KltDP.Geometry.QuadraticFractionField
import KltDP.Geometry.QuadraticReducedBranchIntegralClosure

/-!
# Integral closedness of the original integral quadratic chart

The actual domain quotient supplies nonsquareness over the original
fraction field. The original coefficient map then makes the actual field
quadratic algebra its fraction field. An element integral over the
original quotient is integral over the original base because that
quotient is finite. The proved original integral-closure containment
returns its preimage in the original quotient, proving integral closedness.

Geometric consumers derive domain, nonzero coefficient, and reduced
quotient from the same original Cartier branch and integral cover.
-/

noncomputable section
universe u v

namespace KltDP.Geometry.QuadraticCover

/-- The original domain quadratic chart with reduced branch is integrally closed. -/
theorem coverAlgebra_isIntegrallyClosed_of_reduced_branch
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (s : R) [IsDomain (CoverAlgebra s)] (hs : s ≠ 0) (h2 : IsUnit (2 : R))
    (hred : IsReduced (R ⧸ Ideal.span ({s} : Set R))) :
    IsIntegrallyClosed (CoverAlgebra s) := by
  letI : Fact (Irreducible (polynomial (algebraMap R K s))) :=
    ⟨polynomial_irreducible_of_nonsquare _ (nonsquare_of_coverAlgebra_isDomain K s)⟩
  letI := coefficientAlgebra K s
  letI := coefficientAlgebra_isScalarTower K s
  letI := coefficientAlgebra_isFractionRing K s
  letI : Module.Finite R (CoverAlgebra s) := finite s
  apply (isIntegrallyClosed_iff (CoverAlgebra (algebraMap R K s))).mpr
  intro z hz
  have hzR : IsIntegral R z := isIntegral_trans z hz
  obtain ⟨y, hy⟩ := exists_preimage_of_integral_reduced_branch K s hs h2 hred z hzR
  exact ⟨y, hy⟩

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.coverAlgebra_isIntegrallyClosed_of_reduced_branch
