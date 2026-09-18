import KltDP.Geometry.DegreeOneProjectiveLineIsomorphism
import KltDP.Geometry.GenusZeroFiniteDominantMap

/-! A proper integral curve of arithmetic genus zero is the actual
projective line over the original algebraically closed base field.
The Cartier point, degree-one map, finiteness and isomorphism are proved
from the original curve; no normality or smoothness premise is added. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.GenusZeroCurveProjectiveLineIso

local instance genusZeroIso_projectiveLineIntegral (k : Type u) [Field k] [IsAlgClosed k] :
    IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1

/-- Arithmetic genus zero produces an actual projective-line isomorphism
commuting with the original structure morphism. -/
theorem exists_iso
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X = 1) (hgenus : CurveCanonical.genus f = 0) :
    ∃ e : X ≅ projectiveSpace k 1, e.hom ≫ projectiveSpaceToSpec k 1 = f := by
  obtain ⟨g, hg, hfinite, hgeneric, hdegree⟩ :=
    GenusZeroCurveProjectiveLineMap.exists_finite_dominant_morphism_with_degree_one
      f hdim hgenus
  letI : IsFinite g := hfinite
  letI : GenericPointPreserving g := hgeneric
  letI : IsIso g := DegreeOneProjectiveLineIsomorphism.isIso_of_degree_one
    f g hg hdim.le hdegree
  exact ⟨asIso g, hg⟩

#check KltDP.Geometry.GenusZeroCurveProjectiveLineIso.exists_iso
#print axioms KltDP.Geometry.GenusZeroCurveProjectiveLineIso.exists_iso

end KltDP.Geometry.GenusZeroCurveProjectiveLineIso
