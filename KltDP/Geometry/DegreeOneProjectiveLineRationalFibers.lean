import KltDP.Geometry.DegreeOneProjectiveLineFibers
import KltDP.Geometry.RationalPoints

/-! The original degree-one morphism has point fibers over every actual
base-field-valued section, using the proved uniqueness of that section. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.DegreeOneProjectiveLineFibers

variable {k : Type u} [Field k] [IsAlgClosed k]
local instance sectionFiber_projectiveLineIntegral : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1

theorem isIso_section_fiber
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (π : X ⟶ projectiveSpace k 1) [GenericPointPreserving π] [IsFinite π]
    (hπ : π ≫ projectiveSpaceToSpec k 1 = f)
    (hdim : topologicalKrullDim X ≤ 1)
    (hdegree : eulerCharacteristic f (pullbackInvertibleSheaf π
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 1)
    (i : Spec (CommRingCat.of k) ⟶ projectiveSpace k 1)
    (hi : i ≫ projectiveSpaceToSpec k 1 = 𝟙 _) :
    IsIso (pullback.snd π i) := by
  have hx := isClosed_point_of_section (projectiveSpaceToSpec k 1) i hi
  have he := section_eq_closedPointSection (projectiveSpaceToSpec k 1) i hi
    (fieldMorphismPoint i) hx rfl
  rw [he]
  exact isIso_closedPoint_fiber f π hπ hdim hdegree (fieldMorphismPoint i) hx

#check KltDP.Geometry.DegreeOneProjectiveLineFibers.isIso_section_fiber
#print axioms KltDP.Geometry.DegreeOneProjectiveLineFibers.isIso_section_fiber

end KltDP.Geometry.DegreeOneProjectiveLineFibers
