import KltDP.Geometry.DegreeOneCartierFiber
import KltDP.Geometry.AffineHZeroOneIso
import KltDP.Geometry.ProjectiveLineClosedPointCartier
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
Every original closed-point fiber of a finite degree-one map to P1 is
isomorphic to the original base field. The point's Cartier divisor and
its equality with the actual O(1) line are constructed internally.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.DegreeOneProjectiveLineFibers

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance closedPointFiber_projectiveLineIntegral : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1

/-- The actual scheme-theoretic fiber over each original closed point is
the original Spec k, through its original second projection. -/
theorem isIso_closedPoint_fiber
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (π : X ⟶ projectiveSpace k 1) [GenericPointPreserving π] [IsFinite π]
    (hπ : π ≫ projectiveSpaceToSpec k 1 = f)
    (hdim : topologicalKrullDim X ≤ 1)
    (hdegree : eulerCharacteristic f (pullbackInvertibleSheaf π
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 1)
    (x : projectiveSpace k 1) (hclosed : IsClosed ({x} : Set (projectiveSpace k 1))) :
    IsIso (pullback.snd π (closedPointSection (projectiveSpaceToSpec k 1) x hclosed)) := by
  obtain ⟨D, hD, hci, hi, hI, ⟨eD⟩⟩ :=
    ProjectiveLineClosedPointCartier.exists_cartierDivisor k x hclosed
  let i := closedPointSection (projectiveSpaceToSpec k 1) x hclosed
  letI : IsClosedImmersion i := hci
  letI : IsFinite (pullback.snd π i) := MorphismProperty.pullback_snd _ _ inferInstance
  letI : IsAffine (pullback π i) := isAffine_of_isAffineHom (pullback.snd π i)
  apply AffineHZeroOneIso.isIso_of_cohomologyDimension_eq_one (pullback.snd π i)
  exact DegreeOneCartierFiber.cohomologyDimension_eq_one f (projectiveSpaceToSpec k 1)
    π hπ hdim (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1) D hD eD i hi hI.symm hdegree

#check KltDP.Geometry.DegreeOneProjectiveLineFibers.isIso_closedPoint_fiber
#print axioms KltDP.Geometry.DegreeOneProjectiveLineFibers.isIso_closedPoint_fiber

end KltDP.Geometry.DegreeOneProjectiveLineFibers
