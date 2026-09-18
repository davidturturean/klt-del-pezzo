import KltDP.Geometry.FinitePointFibersClosedImmersion
import KltDP.Geometry.DegreeOneProjectiveLineRationalFibers
import KltDP.Geometry.ProperGenericPointSurjective

/-! The original finite degree-one curve map is itself an isomorphism.
Its fibers, local scalar surjections, and closed immersion are derived;
no fiber identification or isomorphism is supplied. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.DegreeOneProjectiveLineIsomorphism

variable {k : Type u} [Field k] [IsAlgClosed k]
local instance degreeOneIso_projectiveLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- The same actual degree-one morphism is an isomorphism over the field. -/
theorem isIso_of_degree_one
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (π : X ⟶ projectiveSpace k 1) [GenericPointPreserving π] [IsFinite π]
    (hπ : π ≫ projectiveSpaceToSpec k 1 = f)
    (hdim : topologicalKrullDim X ≤ 1)
    (hdegree : eulerCharacteristic f (pullbackInvertibleSheaf π
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 1) :
    IsIso π := by
  letI : IsClosedImmersion π :=
    FinitePointFibersClosedImmersion.isClosedImmersion (projectiveSpaceToSpec k 1) π
      (fun i hi => DegreeOneProjectiveLineFibers.isIso_section_fiber
        f π hπ hdim hdegree i hi)
  letI : Surjective π := surjective_of_proper_genericPointPreserving π
  exact isIso_of_isClosedImmersion_of_surjective π

#check KltDP.Geometry.DegreeOneProjectiveLineIsomorphism.isIso_of_degree_one
#print axioms KltDP.Geometry.DegreeOneProjectiveLineIsomorphism.isIso_of_degree_one

end KltDP.Geometry.DegreeOneProjectiveLineIsomorphism
