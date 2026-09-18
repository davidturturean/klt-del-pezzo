import KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf
import KltDP.Geometry.ProjectiveLineDegreeOneSections
import KltDP.Geometry.ProjectiveLineDegreeExponent

/-! The original homogeneous-coordinate O(1) has transition exponent one.
The comparison uses the actual coordinate fraction on the original left
chart. The proved Picard classification therefore compares every actual
degree-one line directly with the O(1) used by our projective-space maps. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProjectiveLineActualDegreeOne

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveSpaceDegreeOneSheaf ProjectiveLineComparison ProjectiveLineSections
open ProjectiveLineCanonicalFrame ProjectiveLineTransitionExtension
open ProjectiveLineSheafExponent RationalTreePicard ProjectiveLineTransitionExponent

variable (k : Type u) [Field k]

private theorem leftCoordinate_eq_original :
    leftCoordinate k = ProjectiveCoordinateSectionBasicOpen.coordinateSection k 1 0 1 := by
  have h : (firstChartPolynomialEquiv k).symm Polynomial.X =
      ProjectiveChart.chartFraction k 1 0 1 := by
    apply (firstChartPolynomialEquiv k).injective
    rw [RingEquiv.apply_symm_apply, ProjectiveChart.chartFraction_eq]
    exact (firstChartPolynomialEquiv_coordinate k).symm
  exact congrArg ((Proj.awayToSection (grading k) (MvPolynomial.X 0)).hom) h

/-- The exact O(1) used by the projective-space map has the original exponent one. -/
theorem exponent_degreeOne : exponent k (degreeOne k 1) = 1 := by
  have h01 : overlapUnit k 1 ⟨0⟩ ⟨1⟩ = monomialIntersectionUnit k 1 := by
    apply Units.ext
    rw [ProjectiveSpaceDegreeOneSheaf.overlapUnit_val,
      ProjectiveLineDegreeOneSections.monomialIntersectionUnit_one_val,
      leftCoordinate_eq_original]
    rfl
  calc
    exponent k (degreeOne k 1) = cocycleExponent k (overlapUnit k 1) :=
      exponent_eq_of_iso_to_glued k (degreeOne k 1) (overlapUnit k 1)
        (overlapUnit_isCocycle k 1) (Iso.refl _)
    _ = 1 := by
      change overlapExponent k (overlapRestriction k (overlapUnit k 1 ⟨0⟩ ⟨1⟩)) = 1
      rw [h01, overlapRestriction_monomialIntersectionUnit,
        overlapExponent_monomialOverlapUnit]

/-- An actual degree-one line is the actual homogeneous O(1), as a sheaf. -/
theorem exists_iso_of_degree_one (L : InvertibleSheaf (projectiveSpace k 1))
    (hdegree : ProjectiveLineDegree.degree k L = 1) :
    Nonempty (L.obj ≅ (degreeOne k 1).obj) := by
  have hexp : exponent k L = exponent k (degreeOne k 1) :=
    (ProjectiveLineDegree.degree_eq_exponent k L).symm.trans
      (hdegree.trans (exponent_degreeOne k).symm)
  have hpic := ProjectiveLineDegree.toPic_eq_of_exponent_eq k hexp
  have hsk : toSkeleton L.obj = toSkeleton (degreeOne k 1).obj := by
    simpa only [InvertibleSheaf.toPic_val] using
      congrArg (fun p : (projectiveSpace k 1).Pic =>
        (p : Skeleton (projectiveSpace k 1).Modules)) hpic
  exact Quotient.exact hsk

#print axioms exponent_degreeOne
#print axioms exists_iso_of_degree_one

end KltDP.Geometry.ProjectiveLineActualDegreeOne
