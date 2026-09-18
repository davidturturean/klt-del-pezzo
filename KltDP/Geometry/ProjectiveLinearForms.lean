import KltDP.Geometry.SectionLinearCombinations
import KltDP.Geometry.LinearSystemRationalMap
import KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf

/-!
# Original projective linear forms and their map on the original domain

A matrix over the original field forms actual homogeneous degree-one
sections. Their original standard-frame coefficients are the indicated
linear forms. The existing linear-system construction gives their actual
projective morphism precisely where they do not all vanish.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.ProjectiveLinearForms

attribute [local instance] Types.instFunLike Types.instConcreteCategory
open ProjectiveSpaceDegreeOneSheaf ProjectiveCoordinateSectionBasicOpen
  TransitionUnitGluing SectionLinearCombinations

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual homogeneous linear form with its original field coefficients. -/
def formSection (a : Fin (n + 1) → k) : (degreeOne k n).obj.sections :=
  combination (projectiveSpaceToSpec k n) (degreeOne k n).obj
    (homogeneousSection k n) a

/-- In every original standard frame, this section is the corresponding
linear form in the original coordinate fractions. -/
theorem formSection_trivialization (a : Fin (n + 1) → k)
    (i : ULift.{u} (Fin (n + 1))) {W : (projectiveSpace k n).Opens}
    (hW : W ≤ chart k n i) :
    trivialization (projectiveSpace k n) (chart k n) (overlapUnit k n)
      (overlapUnit_isCocycle k n) i hW ((formSection k n a).val (op W)) =
      ∑ j, scalarOnOpen (projectiveSpaceToSpec k n) W (a j) *
        res (projectiveSpace k n) hW (coordinateSection k n i.down j) := by
  classical
  rw [formSection, combination_val]
  let E := trivialization (projectiveSpace k n) (chart k n) (overlapUnit k n)
    (overlapUnit_isCocycle k n) i hW
  change E.toLinearMap.toAddMonoidHom _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (E.map_smul (scalarOnOpen (projectiveSpaceToSpec k n) W (a j))
    ((homogeneousSection k n j).val (op W))).trans
    (congrArg (fun b => scalarOnOpen (projectiveSpaceToSpec k n) W (a j) * b)
    (trivialization_globalSectionOfCoordinates (projectiveSpace k n)
      (chart k n) (overlapUnit k n)
      (fun l => coordinateSection k n l.down j)
      (fun l m => ProjectiveCoordinateSectionRelations.coordinateSection_relation_mul
        k n l.down m.down j) (overlapUnit_isCocycle k n) i hW))

variable {m : ℕ} (a : Fin (m + 1) → Fin (n + 1) → k)

/-- The actual original open on which the indicated matrix defines a projective map. -/
def domain : (projectiveSpace k n).Opens :=
  LinearSystemRationalMap.nonBaseOpen (degreeOne k n) (fun i => formSection k n (a i))

/-- The actual projective linear map on that original open. -/
def morphism : (domain k n a).toScheme ⟶ projectiveSpace k m :=
  LinearSystemRationalMap.morphism (degreeOne k n) (fun i => formSection k n (a i))
    (projectiveSpaceToSpec k n)

/-- The matrix construction preserves the original base field. -/
theorem morphism_structure :
    morphism k n a ≫ projectiveSpaceToSpec k m =
      (domain k n a).ι ≫ projectiveSpaceToSpec k n :=
  LinearSystemRationalMap.morphism_structure (degreeOne k n)
    (fun i => formSection k n (a i)) (projectiveSpaceToSpec k n)

/-- The original target degree-one sheaf pulls back to the original source
degree-one sheaf restricted to the matrix domain. -/
def pullbackDegreeOneIso :
    (pullbackInvertibleSheaf (morphism k n a) (degreeOne k m)).obj ≅
      (pullbackInvertibleSheaf (domain k n a).ι (degreeOne k n)).obj :=
  LinearSystemRationalMap.pullbackDegreeOneIso (degreeOne k n)
    (fun i => formSection k n (a i)) (projectiveSpaceToSpec k n)

end KltDP.Geometry.ProjectiveLinearForms
