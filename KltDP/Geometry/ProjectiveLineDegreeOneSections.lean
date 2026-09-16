import KltDP.Geometry.RationalTreePicardProjectiveLine
import KltDP.Geometry.ProjectiveCoordinateSectionBasicOpen
import KltDP.Geometry.TwoOpenUnitGlobalSectionNonvanishing

/-!
# The two original coordinate sections of the degree-one projective line bundle

The accepted Laurent transition T glues (1, T⁻¹) and (T, 1) into actual
global sections of the existing monomial line bundle. Their intrinsic
nonvanishing opens are exactly the two original standard affine charts.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveLineDegreeOneSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveLineComparison ProjectiveLineSections ProjectiveLineCanonicalFrame
open ProjectiveLineTransitionExtension TransitionUnitGluing RationalTreePicard
open InvertibleSectionNonvanishingOpen

variable (k : Type u) [Field k]

private theorem eq_of_overlap_res
    {a b : Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1)}
    (h : res (projectiveSpace k 1) (overlapOpen_eq_inf k).le a =
      res (projectiveSpace k 1) (overlapOpen_eq_inf k).le b) : a = b := by
  have he := congrArg (res (projectiveSpace k 1) (overlapOpen_eq_inf k).ge) h
  simpa only [res_res, res_self] using he

/-- The degree-one transition is the original coordinate T on the overlap. -/
theorem monomialOverlapUnit_one_val :
    (monomialOverlapUnit k 1 : Γ(projectiveSpace k 1, overlapOpen k)) = leftFrame k := by
  apply (overlapSectionsEquiv k).injective
  rw [overlapSectionsEquiv_leftFrame]
  change overlapSectionsEquiv k ((overlapSectionsEquiv k).symm
      ((LaurentPolynomial.isUnit_T (R := k) (1 : ℤ)).unit : LaurentPolynomial k)) =
    LaurentPolynomial.T 1
  rw [RingEquiv.apply_symm_apply, IsUnit.unit_spec]

/-- On the actual chart intersection the transition is the restricted left coordinate. -/
theorem monomialIntersectionUnit_one_val :
    (monomialIntersectionUnit k 1 :
        Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1)) =
      res (projectiveSpace k 1) inf_le_left (leftCoordinate k) := by
  apply eq_of_overlap_res k
  rw [res_res]
  have h := congrArg
    (fun z : Γ(projectiveSpace k 1, overlapOpen k)ˣ =>
      (z : Γ(projectiveSpace k 1, overlapOpen k)))
    (overlapRestriction_monomialIntersectionUnit k 1)
  exact h.trans (monomialOverlapUnit_one_val k)

private theorem first_compatible :
    res (projectiveSpace k 1)
        (inf_le_left : chartOpen k 0 ⊓ chartOpen k 1 ≤ chartOpen k 0)
        (1 : Γ(projectiveSpace k 1, chartOpen k 0)) =
      (monomialIntersectionUnit k 1 :
          Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1)) *
        res (projectiveSpace k 1) inf_le_right (rightCoordinate k) := by
  rw [map_one, monomialIntersectionUnit_one_val]
  apply eq_of_overlap_res k
  simp only [map_one, map_mul, res_res]
  exact (leftFrame_mul_rightFrame k).symm

private theorem second_compatible :
    res (projectiveSpace k 1)
        (inf_le_left : chartOpen k 0 ⊓ chartOpen k 1 ≤ chartOpen k 0)
        (leftCoordinate k) =
      (monomialIntersectionUnit k 1 :
          Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1)) *
        res (projectiveSpace k 1) inf_le_right
          (1 : Γ(projectiveSpace k 1, chartOpen k 1)) := by
  rw [map_one, mul_one]
  exact (monomialIntersectionUnit_one_val k).symm

/-- The original coordinate section with chart functions (1, X₀/X₁). -/
def firstSection : (monomialLineBundle k 1).obj.sections :=
  TwoOpenUnitGlobalSections.globalSection (projectiveSpace k 1) (standardOpens k)
    (monomialIntersectionUnit k 1) 1 (rightCoordinate k) (first_compatible k)

/-- The original coordinate section with chart functions (X₁/X₀, 1). -/
def secondSection : (monomialLineBundle k 1).obj.sections :=
  TwoOpenUnitGlobalSections.globalSection (projectiveSpace k 1) (standardOpens k)
    (monomialIntersectionUnit k 1) (leftCoordinate k) 1 (second_compatible k)

private theorem leftCoordinate_eq_coordinateSection :
    leftCoordinate k = ProjectiveCoordinateSectionBasicOpen.coordinateSection k 1 0 1 := by
  have h : (firstChartPolynomialEquiv k).symm Polynomial.X =
      ProjectiveChart.chartFraction k 1 0 1 := by
    apply (firstChartPolynomialEquiv k).injective
    rw [RingEquiv.apply_symm_apply, ProjectiveChart.chartFraction_eq]
    exact (firstChartPolynomialEquiv_coordinate k).symm
  exact congrArg ((Proj.awayToSection (grading k) (MvPolynomial.X 0)).hom) h

private theorem rightCoordinate_eq_coordinateSection :
    rightCoordinate k = ProjectiveCoordinateSectionBasicOpen.coordinateSection k 1 1 0 := by
  have h : (secondChartPolynomialEquiv k).symm Polynomial.X =
      ProjectiveChart.chartFraction k 1 1 0 := by
    apply (secondChartPolynomialEquiv k).injective
    rw [RingEquiv.apply_symm_apply, ProjectiveChart.chartFraction_eq]
    exact (secondChartPolynomialEquiv_coordinate k).symm
  exact congrArg ((Proj.awayToSection (grading k) (MvPolynomial.X 1)).hom) h

/-- The original left affine coordinate is nonzero exactly on the original overlap. -/
theorem basicOpen_leftCoordinate :
    (projectiveSpace k 1).basicOpen (leftCoordinate k) = chartOpen k 0 ⊓ chartOpen k 1 := by
  rw [leftCoordinate_eq_coordinateSection]
  exact ProjectiveCoordinateSectionBasicOpen.basicOpen_coordinateSection k 1 0 1

/-- The original right affine coordinate is nonzero exactly on the original overlap. -/
theorem basicOpen_rightCoordinate :
    (projectiveSpace k 1).basicOpen (rightCoordinate k) = chartOpen k 1 ⊓ chartOpen k 0 := by
  rw [rightCoordinate_eq_coordinateSection]
  exact ProjectiveCoordinateSectionBasicOpen.basicOpen_coordinateSection k 1 1 0

/-- The first coordinate section's intrinsic nonvanishing open is chart zero. -/
theorem nonvanishingOpen_firstSection :
    nonvanishingOpen (projectiveSpace k 1) (monomialLineBundle k 1) (firstSection k) =
      chartOpen k 0 := by
  have h := TwoOpenUnitGlobalSections.nonvanishingOpen_globalSection
    (projectiveSpace k 1) (standardOpens k) (monomialIntersectionUnit k 1)
    (ProjectiveLineSheafExponent.standardCover k
      (InvertibleSheaf.trivial (projectiveSpace k 1)))
    1 (rightCoordinate k) (first_compatible k)
  exact h.trans (by
    rw [Scheme.basicOpen_one, basicOpen_rightCoordinate]
    exact sup_eq_left.mpr inf_le_right)

/-- The second coordinate section's intrinsic nonvanishing open is chart one. -/
theorem nonvanishingOpen_secondSection :
    nonvanishingOpen (projectiveSpace k 1) (monomialLineBundle k 1) (secondSection k) =
      chartOpen k 1 := by
  have h := TwoOpenUnitGlobalSections.nonvanishingOpen_globalSection
    (projectiveSpace k 1) (standardOpens k) (monomialIntersectionUnit k 1)
    (ProjectiveLineSheafExponent.standardCover k
      (InvertibleSheaf.trivial (projectiveSpace k 1)))
    (leftCoordinate k) 1 (second_compatible k)
  exact h.trans (by
    rw [Scheme.basicOpen_one, basicOpen_leftCoordinate]
    exact sup_eq_right.mpr inf_le_right)

/-- The two actual homogeneous-coordinate global sections, indexed by the original cover. -/
def standardSection (i : ULift.{u} (Fin 2)) : (monomialLineBundle k 1).obj.sections :=
  Fin.cases (firstSection k) (fun _ => secondSection k) i.down

/-- Each original coordinate section cuts out exactly its original affine chart. -/
theorem nonvanishingOpen_standardSection (i : ULift.{u} (Fin 2)) :
    nonvanishingOpen (projectiveSpace k 1) (monomialLineBundle k 1) (standardSection k i) =
      chartOpen k i.down := by
  rcases i with ⟨i⟩
  fin_cases i
  · exact nonvanishingOpen_firstSection k
  · exact nonvanishingOpen_secondSection k

end KltDP.Geometry.ProjectiveLineDegreeOneSections
