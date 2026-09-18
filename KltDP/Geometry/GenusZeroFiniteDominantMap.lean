import KltDP.Geometry.GenusZeroCurveProjectiveLineMap
import KltDP.Geometry.ProperNonconstantCurveFieldFinite
import KltDP.Geometry.NonconstantCurveGenericPoint
import KltDP.Geometry.ProjectiveSpaceDimension
import KltDP.Geometry.ProjectiveSpaceIntegral

/-!
# An actual finite dominant map from an original genus-zero curve

The map, its finiteness, its action on the original generic point, and its
degree are all produced from properness, integrality, dimension one and
arithmetic genus zero. The generic-point condition permits the already
proved signed Cartier pullback and original point-fiber comparisons.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.GenusZeroCurveProjectiveLineMap

open ModuleCohomology

local instance genusZeroFiniteDominant_projectiveIntegral
    (k : Type u) [Field k] : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- The actual curve has a finite generic-point-preserving map of original
O(1) Euler degree one. No point or morphism is a supplied choice. -/
theorem exists_finite_dominant_morphism_with_degree_one
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X = 1) (hgenus : CurveCanonical.genus f = 0) :
    ∃ g : X ⟶ projectiveSpace k 1,
      g ≫ projectiveSpaceToSpec k 1 = f ∧ IsFinite g ∧
      GenericPointPreserving g ∧
      eulerCharacteristic f (pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj -
        eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 1 := by
  obtain ⟨g, hg, hproper, hdegree, hnonconstant⟩ :=
    exists_proper_morphism_with_degree_one f hdim hgenus
  letI : IsProper g := hproper
  have hfinite : IsFinite g :=
    ProperNonconstantCurve.isFinite_of_not_factors_through_structure f
      (projectiveSpaceToSpec k 1) g hg hdim.le hnonconstant
  letI : NoetherianSpace (projectiveSpace k 1) :=
    noetherianSpace_of_locallyOfFiniteType_quasiCompact_spec (projectiveSpaceToSpec k 1)
  have hgeneric : GenericPointPreserving g :=
    ProperNonconstantCurve.genericPointPreserving_of_not_factors_through_structure f
      (projectiveSpaceToSpec k 1) g hg
      (projectiveSpace_topologicalKrullDim k 1).le hnonconstant
  exact ⟨g, hg, hfinite, hgeneric, hdegree⟩

end KltDP.Geometry.GenusZeroCurveProjectiveLineMap

#check @KltDP.Geometry.GenusZeroCurveProjectiveLineMap.exists_finite_dominant_morphism_with_degree_one
#print axioms KltDP.Geometry.GenusZeroCurveProjectiveLineMap.exists_finite_dominant_morphism_with_degree_one
