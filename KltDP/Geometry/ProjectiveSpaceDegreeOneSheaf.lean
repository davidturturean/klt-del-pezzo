import KltDP.Geometry.ProjectiveCoordinateSectionRelations
import KltDP.Geometry.TransitionUnitGlobalSectionNonvanishing
import KltDP.Geometry.ProjectiveSpaceNormal

/-!
# The actual homogeneous degree-one sheaf on original projective space

The original units z_j/z_i on standard chart intersections form the
rank-one gluing cocycle. Its original homogeneous-coordinate sections
have precisely the original standard charts as their nonvanishing opens.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveCoordinateSectionBasicOpen ProjectiveCoordinateSectionRelations
open TransitionUnitGluing InvertibleSectionNonvanishingOpen

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual standard chart, with only the finite index universe lifted. -/
abbrev chart (i : ULift.{u} (Fin (n + 1))) : (projectiveSpace k n).Opens :=
  standardOpen k n i.down

/-- The original transition unit z_j/z_i, with the original reciprocal as inverse. -/
def overlapUnit (i j : ULift.{u} (Fin (n + 1))) :
    Γ(projectiveSpace k n, chart k n i ⊓ chart k n j)ˣ where
  val := res (projectiveSpace k n) inf_le_left (coordinateSection k n i.down j.down)
  inv := res (projectiveSpace k n) inf_le_right (coordinateSection k n j.down i.down)
  val_inv := coordinateSection_relation_inv k n i.down j.down
  inv_val := (mul_comm _ _).trans (coordinateSection_relation_inv k n i.down j.down)

@[simp] theorem overlapUnit_val (i j : ULift.{u} (Fin (n + 1))) :
    (overlapUnit k n i j : Γ(projectiveSpace k n, chart k n i ⊓ chart k n j)) =
      res (projectiveSpace k n) inf_le_left (coordinateSection k n i.down j.down) := rfl

/-- The original coordinate transition units satisfy the original cocycle equations. -/
theorem overlapUnit_isCocycle :
    IsCocycle (projectiveSpace k n) (chart k n) (overlapUnit k n) where
  unit_self i := by
    rw [overlapUnit_val, coordinateSection_self, map_one]
  mul_res i j l := by
    have h := congrArg
      (res (projectiveSpace k n)
        (inf_le_left : chart k n i ⊓ chart k n j ⊓ chart k n l ≤ chart k n i ⊓ chart k n j))
      (coordinateSection_relation_mul k n i.down j.down l.down)
    simp only [map_mul, res_res] at h
    simp only [overlapUnit_val, res_res]
    exact h.symm

/-- The original finite coordinate charts cover the original projective space. -/
theorem chart_cover : (⨆ i, chart k n i) = ⊤ := by
  rw [iSup_ulift]
  exact ProjectiveChart.iSup_coordinateStandardOpen k n

/-- The actual line sheaf obtained from the original degree-one coordinate cocycle. -/
def degreeOne : InvertibleSheaf (projectiveSpace k n) :=
  invertibleSheaf (projectiveSpace k n) (chart k n) (overlapUnit k n)
    (overlapUnit_isCocycle k n) (chart_cover k n)

/-- The original homogeneous coordinate z_a as an actual global section. -/
def homogeneousSection (a : Fin (n + 1)) : (degreeOne k n).obj.sections :=
  globalSectionOfCoordinates (projectiveSpace k n) (chart k n) (overlapUnit k n)
    (fun i => coordinateSection k n i.down a)
    (fun i j => coordinateSection_relation_mul k n i.down j.down a)

/-- The original homogeneous coordinate vanishes nowhere precisely on
its original standard affine chart. -/
theorem nonvanishingOpen_homogeneousSection (a : Fin (n + 1)) :
    nonvanishingOpen (projectiveSpace k n) (degreeOne k n) (homogeneousSection k n a) =
      standardOpen k n a := by
  calc
    _ = ⨆ i : ULift.{u} (Fin (n + 1)),
        (projectiveSpace k n).basicOpen (coordinateSection k n i.down a) :=
      nonvanishingOpen_globalSectionOfCoordinates (projectiveSpace k n) (chart k n)
        (overlapUnit k n) (overlapUnit_isCocycle k n) (chart_cover k n)
        (fun i => coordinateSection k n i.down a)
        (fun i j => coordinateSection_relation_mul k n i.down j.down a)
    _ = standardOpen k n a := by
      apply le_antisymm
      · apply iSup_le
        intro i
        rw [basicOpen_coordinateSection]
        exact inf_le_right
      · apply le_iSup_of_le (ULift.up a)
        rw [basicOpen_coordinateSection]
        exact le_inf le_rfl le_rfl

end KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf
