import KltDP.Examples.FrobeniusGlobalBlowupSmooth

/-!
# Smoothness of an original curve isomorphic to the projective line

The existing two polynomial charts prove smooth relative dimension one for
the original projective line. Its composition with an actual scheme
isomorphism gives the same property for the original curve over the field.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- An actual projective-line isomorphism over k supplies smooth relative dimension one. -/
theorem smoothOne_of_projectiveLineIso (f : C ⟶ Spec (CommRingCat.of k))
    (e : C ≅ projectiveSpace k 1) (he : e.hom ≫ projectiveSpaceToSpec k 1 = f) :
    IsSmoothOfRelativeDimension 1 f := by
  rw [← he]
  exact isSmoothOfRelativeDimension_comp (n := 0) (m := 1)
    (f := e.hom) (g := projectiveSpaceToSpec k 1)

end KltDP.Geometry
