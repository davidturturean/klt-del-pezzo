import KltDP.Geometry.LinearSystemNormalizedCoordinates
import KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf

/-!
# Original homogeneous sections in the chosen linear-system atlas

The constructed standard gluing frame and the original chosen invertible
atlas are linear identifications of the same section module. Their actual
transition unit multiplies every homogeneous coordinate by the same unit.
Dividing by the selected coordinate therefore recovers the original
projective coordinate section, without a compatibility premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveCoordinateLinearSystem

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing TransitionUnitExtraction LinearSystemMorphism
  InvertibleSectionNonvanishingOpen ProjectiveSpaceDegreeOneSheaf
  ProjectiveCoordinateSectionBasicOpen ProjectiveCoordinateSectionRelations

variable (k : Type u) [Field k] (n : ℕ)

local instance sectionModule (A : (projectiveSpace k n).Modules)
    (W : (projectiveSpace k n).Opens) :
    Module Γ(projectiveSpace k n, W) (A.val.obj (op W)) :=
  (A.val.obj (op W)).isModule

/-- The original homogeneous-coordinate nonvanishing opens cover projective space. -/
theorem homogeneousSection_cover :
    (⨆ j, nonvanishingOpen (projectiveSpace k n) (degreeOne k n)
      (homogeneousSection k n j)) = ⊤ := by
  simp only [nonvanishingOpen_homogeneousSection]
  exact ProjectiveChart.iSup_coordinateStandardOpen k n

/-- The selected intrinsic nonvanishing open is the original standard chart. -/
theorem le_standardOpen_of_homogeneousSection {W : (projectiveSpace k n).Opens}
    (m : Fin (n + 1))
    (hWm : W ≤ nonvanishingOpen (projectiveSpace k n) (degreeOne k n)
      (homogeneousSection k n m)) : W ≤ standardOpen k n m := by
  rwa [nonvanishingOpen_homogeneousSection] at hWm

/-- The actual standard gluing frame, evaluated on the original section module. -/
def standardFrame (m : Fin (n + 1)) {W : (projectiveSpace k n).Opens}
    (hWm : W ≤ standardOpen k n m) :
    (degreeOne k n).obj.val.obj (op W) ≃ₗ[Γ(projectiveSpace k n, W)]
      Γ(projectiveSpace k n, W) :=
  trivialization (projectiveSpace k n) (chart k n) (overlapUnit k n)
    (overlapUnit_isCocycle k n) (ULift.up m) hWm

/-- This frame reads the original homogeneous fraction on every actual subopen. -/
theorem standardFrame_homogeneousSection (m : Fin (n + 1))
    {W : (projectiveSpace k n).Opens} (hWm : W ≤ standardOpen k n m)
    (j : Fin (n + 1)) :
    standardFrame k n m hWm ((homogeneousSection k n j).val (op W)) =
      res (projectiveSpace k n) hWm (coordinateSection k n m j) :=
  trivialization_globalSectionOfCoordinates (projectiveSpace k n) (chart k n)
    (overlapUnit k n) (fun i => coordinateSection k n i.down j)
    (fun i l => coordinateSection_relation_mul k n i.down l.down j)
    (overlapUnit_isCocycle k n) (ULift.up m) hWm

/-- Normalization in the original chosen atlas recovers the original coordinate section. -/
theorem coordinates_homogeneousSection
    (i : (degreeOne k n).localTrivializations.I) {W : (projectiveSpace k n).Opens}
    (hWi : W ≤ (degreeOne k n).localTrivializations.X i) (m : Fin (n + 1))
    (hWm : W ≤ nonvanishingOpen (projectiveSpace k n) (degreeOne k n)
      (homogeneousSection k n m)) (j : Fin (n + 1)) :
    coordinates (degreeOne k n) (homogeneousSection k n) i hWi m hWm j =
      res (projectiveSpace k n) (le_standardOpen_of_homogeneousSection k n m hWm)
        (coordinateSection k n m j) := by
  let hstd := le_standardOpen_of_homogeneousSection k n m hWm
  let e := standardFrame k n m hstd
  let e' := chartEquiv (projectiveSpace k n) (degreeOne k n).obj
    (degreeOne k n).localTrivializations i hWi
  let t := KltDP.Module.transitionUnit e e'
  have hc (a : Fin (n + 1)) :
      coefficient (degreeOne k n) (homogeneousSection k n a) i hWi =
        (t : Γ(projectiveSpace k n, W)) *
          res (projectiveSpace k n) hstd (coordinateSection k n m a) := by
    exact (KltDP.Module.transitionUnit_mul_apply e e'
      ((homogeneousSection k n a).val (op W))).symm.trans
        (congrArg (fun b : Γ(projectiveSpace k n, W) => (t : Γ(projectiveSpace k n, W)) * b)
          (standardFrame_homogeneousSection k n m hstd a))
  have hm : coefficient (degreeOne k n) (homogeneousSection k n m) i hWi =
      (t : Γ(projectiveSpace k n, W)) := by
    rw [hc m, coordinateSection_self, map_one, mul_one]
  apply (coefficient_isUnit (degreeOne k n) (homogeneousSection k n m) i hWi hWm).mul_left_cancel
  rw [denominator_mul_coordinates, hc j, hm]

end KltDP.Geometry.ProjectiveCoordinateLinearSystem
