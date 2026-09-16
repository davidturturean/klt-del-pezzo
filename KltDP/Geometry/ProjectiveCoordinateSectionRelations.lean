import KltDP.Geometry.ProjectiveCoordinateSectionBasicOpen
import KltDP.Geometry.ProjectiveSpaceChartFunctionsGeneral
import KltDP.Geometry.ProjectiveSegreGeneralCharts
import KltDP.Geometry.TransitionUnitSections

/-!
# Original section identities for projective homogeneous coordinates

The accepted identities in the original homogeneous overlap rings transport
through the pinned awayToSection restriction equation. They give the actual
section transition and inverse identities on the original chart intersections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveCoordinateSectionRelations

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveChart ProjectiveCoordinateSectionBasicOpen TransitionUnitGluing

variable (k : Type u) [Field k] (n : ℕ)

abbrev overlapOpen (i j : Fin (n + 1)) : (projectiveSpace k n).Opens :=
  Proj.basicOpen (grading k n)
    ((MvPolynomial.X i : homogeneousRing k n) * MvPolynomial.X j)

theorem overlapOpen_eq_inf (i j : Fin (n + 1)) :
    overlapOpen k n i j = standardOpen k n i ⊓ standardOpen k n j :=
  Proj.basicOpen_mul (grading k n) (MvPolynomial.X i) (MvPolynomial.X j)

private theorem overlapOpen_le_left (i j : Fin (n + 1)) :
    overlapOpen k n i j ≤ standardOpen k n i :=
  (overlapOpen_eq_inf k n i j).le.trans inf_le_left

private theorem overlapOpen_le_right (i j : Fin (n + 1)) :
    overlapOpen k n i j ≤ standardOpen k n j :=
  (overlapOpen_eq_inf k n i j).le.trans inf_le_right

private theorem eq_of_overlap_res (i j : Fin (n + 1))
    {a b : Γ(projectiveSpace k n, standardOpen k n i ⊓ standardOpen k n j)}
    (h : res (projectiveSpace k n) (overlapOpen_eq_inf k n i j).le a =
      res (projectiveSpace k n) (overlapOpen_eq_inf k n i j).le b) : a = b := by
  have he := congrArg (res (projectiveSpace k n) (overlapOpen_eq_inf k n i j).ge) h
  simpa only [res_res, res_self] using he

/-- Restriction of the original left coordinate section is the accepted
left map of the original homogeneous overlap ring. -/
theorem restrictLeft_coordinateSection (i j a : Fin (n + 1)) :
    res (projectiveSpace k n) (overlapOpen_le_left k n i j) (coordinateSection k n i a) =
      (Proj.awayToSection (grading k n)
        ((MvPolynomial.X i : homogeneousRing k n) * MvPolynomial.X j)).hom
          (toOverlapLeft k n i j (chartFraction k n i a)) := by
  have h := Proj.awayMap_awayToSection (grading k n) (coordinate_mem k n j)
    (f := (MvPolynomial.X i : homogeneousRing k n)) rfl
  have hp := congrArg (fun f : coordinateChartRing k n i →+*
    Γ(projectiveSpace k n, overlapOpen k n i j) => f (chartFraction k n i a))
    (congrArg CommRingCat.Hom.hom h)
  exact hp.symm

/-- The corresponding original right-coordinate restriction. -/
theorem restrictRight_coordinateSection (i j a : Fin (n + 1)) :
    res (projectiveSpace k n) (overlapOpen_le_right k n i j) (coordinateSection k n j a) =
      (Proj.awayToSection (grading k n)
        ((MvPolynomial.X i : homogeneousRing k n) * MvPolynomial.X j)).hom
          (toOverlapRight k n i j (chartFraction k n j a)) := by
  have h := Proj.awayMap_awayToSection (grading k n) (coordinate_mem k n i)
    (f := (MvPolynomial.X j : homogeneousRing k n))
    (mul_comm (MvPolynomial.X i : homogeneousRing k n) (MvPolynomial.X j))
  have hp := congrArg (fun f : coordinateChartRing k n j →+*
    Γ(projectiveSpace k n, overlapOpen k n i j) => f (chartFraction k n j a))
    (congrArg CommRingCat.Hom.hom h)
  exact hp.symm

/-- The original section z_i/z_i is one on its original coordinate chart. -/
theorem coordinateSection_self (i : Fin (n + 1)) :
    coordinateSection k n i i = 1 := by
  change (Proj.awayToSection (grading k n) (MvPolynomial.X i)).hom
    (chartFraction k n i i) = 1
  rw [ProjectiveSegreGeneral.chartFraction_self, map_one]

/-- The original coordinate sections satisfy z_a/z_i = (z_j/z_i)(z_a/z_j)
on the actual intersection of the original i and j charts. -/
theorem coordinateSection_relation_mul (i j a : Fin (n + 1)) :
    res (projectiveSpace k n)
        (inf_le_left : standardOpen k n i ⊓ standardOpen k n j ≤ standardOpen k n i)
        (coordinateSection k n i a) =
      res (projectiveSpace k n) inf_le_left (coordinateSection k n i j) *
        res (projectiveSpace k n) inf_le_right (coordinateSection k n j a) := by
  apply eq_of_overlap_res k n i j
  simp only [map_mul, res_res]
  rw [restrictLeft_coordinateSection, restrictLeft_coordinateSection,
    restrictRight_coordinateSection]
  let φ : coordinateOverlapRing k n i j →+* Γ(projectiveSpace k n, overlapOpen k n i j) :=
    (Proj.awayToSection (grading k n)
      ((MvPolynomial.X i : homogeneousRing k n) * MvPolynomial.X j)).hom
  change φ (toOverlapLeft k n i j (chartFraction k n i a)) =
    φ (toOverlapLeft k n i j (chartFraction k n i j)) *
      φ (toOverlapRight k n i j (chartFraction k n j a))
  exact (congrArg φ (toOverlapLeft_chartFraction_eq k n i j a)).trans
    (map_mul φ _ _)

/-- The original transition coordinate and the original reciprocal coordinate
multiply to one on the actual chart intersection. -/
theorem coordinateSection_relation_inv (i j : Fin (n + 1)) :
    res (projectiveSpace k n)
        (inf_le_left : standardOpen k n i ⊓ standardOpen k n j ≤ standardOpen k n i)
        (coordinateSection k n i j) *
      res (projectiveSpace k n) inf_le_right (coordinateSection k n j i) = 1 := by
  apply eq_of_overlap_res k n i j
  simp only [map_one, map_mul, res_res]
  rw [restrictLeft_coordinateSection, restrictRight_coordinateSection]
  let φ : coordinateOverlapRing k n i j →+* Γ(projectiveSpace k n, overlapOpen k n i j) :=
    (Proj.awayToSection (grading k n)
      ((MvPolynomial.X i : homogeneousRing k n) * MvPolynomial.X j)).hom
  change φ (toOverlapLeft k n i j (chartFraction k n i j)) *
    φ (toOverlapRight k n i j (chartFraction k n j i)) = 1
  exact (map_mul φ _ _).symm.trans
    ((congrArg φ (toOverlapLeft_mul_toOverlapRight k n i j)).trans (map_one φ))

end KltDP.Geometry.ProjectiveCoordinateSectionRelations
