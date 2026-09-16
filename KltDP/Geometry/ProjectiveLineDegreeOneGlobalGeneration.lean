import KltDP.Geometry.ProjectiveLineDegreeOneSections
import KltDP.Geometry.FramedGlobalGeneration

/-!
# The original two coordinate sections generate the original degree-one sheaf

In each original chart, its matching coordinate section has coefficient one.
The accepted local-generator gluing theorem gives the actual epimorphism
from the free sheaf on these two sections, retaining this exact finite family.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveLineDegreeOneGlobalGeneration

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open RationalTreePicard ProjectiveLineDegreeOneSections
open ProjectiveLineComparison ProjectiveLineTransitionExtension TransitionUnitGluing

variable (k : Type u) [Field k]

/-- The original gluing frame of the existing degree-one line bundle. -/
def coordinateFrame (i : ULift.{u} (Fin 2)) :
    (monomialLineBundle k 1).obj.over (standardOpens k i) ≅
      _root_.SheafOfModules.unit ((projectiveSpace k 1).ringCatSheaf.over (standardOpens k i)) :=
  chartIsoOn (projectiveSpace k 1) (standardOpens k) (monomialCocycle k 1)
    (monomialCocycle_isCocycle k 1) i le_rfl

private theorem firstCoefficient :
    (coordinateFrame k ⟨0⟩).hom.val.app (op (Over.mk (𝟙 (standardOpens k ⟨0⟩))))
      ((firstSection k).val (op (standardOpens k ⟨0⟩))) =
        (1 : Γ(projectiveSpace k 1, standardOpens k ⟨0⟩)) := by
  have hc : res (projectiveSpace k 1)
      (inf_le_left : chartOpen k 0 ⊓ chartOpen k 1 ≤ chartOpen k 0)
      (1 : Γ(projectiveSpace k 1, chartOpen k 0)) =
    (monomialIntersectionUnit k 1 : Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1)) *
      res (projectiveSpace k 1) inf_le_right (ProjectiveLineCanonicalFrame.rightCoordinate k) := by
    rw [map_one, monomialIntersectionUnit_one_val]
    let φ := res (projectiveSpace k 1) (ProjectiveLineSections.overlapOpen_eq_inf k).ge
    have he := (map_one φ).symm.trans
      ((congrArg φ (ProjectiveLineCanonicalFrame.leftFrame_mul_rightFrame k).symm).trans
        (map_mul φ _ _))
    change (1 : Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1)) =
      res (projectiveSpace k 1) (ProjectiveLineSections.overlapOpen_eq_inf k).ge
        (res (projectiveSpace k 1) (ProjectiveLineSections.overlapOpen_le_left k)
          (ProjectiveLineCanonicalFrame.leftCoordinate k)) *
      res (projectiveSpace k 1) (ProjectiveLineSections.overlapOpen_eq_inf k).ge
        (res (projectiveSpace k 1) (ProjectiveLineSections.overlapOpen_le_right k)
          (ProjectiveLineCanonicalFrame.rightCoordinate k)) at he
    simpa only [res_res] using he
  have h := chartIsoOn_hom_app_apply (projectiveSpace k 1) (standardOpens k)
    (monomialCocycle k 1) (monomialCocycle_isCocycle k 1) ⟨0⟩
    (le_refl (standardOpens k ⟨0⟩)) (op (Over.mk (𝟙 (standardOpens k ⟨0⟩))))
    ((firstSection k).val (op (standardOpens k ⟨0⟩)))
  have ht := trivialization_globalSectionOfCoordinates (projectiveSpace k 1) (standardOpens k)
    (monomialCocycle k 1)
    (TwoOpenUnitGlobalSections.coordinates (projectiveSpace k 1) (standardOpens k)
      1 (ProjectiveLineCanonicalFrame.rightCoordinate k))
    (TwoOpenUnitGlobalSections.coordinates_compatible (projectiveSpace k 1) (standardOpens k)
      (monomialIntersectionUnit k 1) 1 (ProjectiveLineCanonicalFrame.rightCoordinate k) hc)
    (monomialCocycle_isCocycle k 1) ⟨0⟩ (le_refl (standardOpens k ⟨0⟩))
  exact h.trans (ht.trans (map_one (res (projectiveSpace k 1) (le_refl (standardOpens k ⟨0⟩)))))

private theorem secondCoefficient :
    (coordinateFrame k ⟨1⟩).hom.val.app (op (Over.mk (𝟙 (standardOpens k ⟨1⟩))))
      ((secondSection k).val (op (standardOpens k ⟨1⟩))) =
        (1 : Γ(projectiveSpace k 1, standardOpens k ⟨1⟩)) := by
  have hc : res (projectiveSpace k 1)
      (inf_le_left : chartOpen k 0 ⊓ chartOpen k 1 ≤ chartOpen k 0)
      (ProjectiveLineCanonicalFrame.leftCoordinate k) =
    (monomialIntersectionUnit k 1 : Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1)) *
      res (projectiveSpace k 1) inf_le_right (1 : Γ(projectiveSpace k 1, chartOpen k 1)) := by
    rw [map_one, mul_one]
    exact (monomialIntersectionUnit_one_val k).symm
  have h := chartIsoOn_hom_app_apply (projectiveSpace k 1) (standardOpens k)
    (monomialCocycle k 1) (monomialCocycle_isCocycle k 1) ⟨1⟩
    (le_refl (standardOpens k ⟨1⟩)) (op (Over.mk (𝟙 (standardOpens k ⟨1⟩))))
    ((secondSection k).val (op (standardOpens k ⟨1⟩)))
  have ht := trivialization_globalSectionOfCoordinates (projectiveSpace k 1) (standardOpens k)
    (monomialCocycle k 1)
    (TwoOpenUnitGlobalSections.coordinates (projectiveSpace k 1) (standardOpens k)
      (ProjectiveLineCanonicalFrame.leftCoordinate k) 1)
    (TwoOpenUnitGlobalSections.coordinates_compatible (projectiveSpace k 1) (standardOpens k)
      (monomialIntersectionUnit k 1) (ProjectiveLineCanonicalFrame.leftCoordinate k) 1 hc)
    (monomialCocycle_isCocycle k 1) ⟨1⟩ (le_refl (standardOpens k ⟨1⟩))
  exact h.trans (ht.trans (map_one (res (projectiveSpace k 1) (le_refl (standardOpens k ⟨1⟩)))))

/-- On every original chart the matching coordinate section has coefficient one. -/
theorem standardSection_coefficient (i : ULift.{u} (Fin 2)) :
    (coordinateFrame k i).hom.val.app (op (Over.mk (𝟙 (standardOpens k i))))
      ((standardSection k i).val (op (standardOpens k i))) =
        (1 : Γ(projectiveSpace k 1, standardOpens k i)) := by
  rcases i with ⟨i⟩
  fin_cases i
  · exact firstCoefficient k
  · exact secondCoefficient k

/-- The actual epimorphism determined by the two original coordinate sections. -/
theorem standardSections_epi :
    Epi ((monomialLineBundle k 1).obj.freeHomEquiv.symm (standardSection k)) := by
  apply FramedGlobalGeneration.epi_of_unit_coefficients (monomialLineBundle k 1).obj
    (standardOpens k)
    (ProjectiveLineSheafExponent.standardCover k
      (InvertibleSheaf.trivial (projectiveSpace k 1))).ge
    (coordinateFrame k) (standardSection k)
  intro i
  exact ⟨i, standardSection_coefficient k i⟩

/-- The literal two-section generating family of the original degree-one sheaf. -/
def standardGenerators : (monomialLineBundle k 1).obj.GeneratingSections where
  I := ULift.{u} (Fin 2)
  s := standardSection k
  epi := standardSections_epi k

theorem standardGenerators_finite : Finite (standardGenerators k).I :=
  inferInstanceAs (Finite (ULift.{u} (Fin 2)))

/-- The original degree-one sheaf is globally generated by its two
constructed coordinate sections. -/
theorem degreeOne_isGloballyGenerated :
    Positivity.IsGloballyGenerated (monomialLineBundle k 1).obj :=
  ⟨ULift.{u} (Fin 2), (monomialLineBundle k 1).obj.freeHomEquiv.symm (standardSection k),
    standardSections_epi k⟩

end KltDP.Geometry.ProjectiveLineDegreeOneGlobalGeneration
