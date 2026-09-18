import KltDP.Geometry.RationalPrimeCurveAdjunction
import KltDP.Geometry.SmoothCanonicalCartierExterior

/-!
# Exact rational adjunction for the original compatible canonical divisor

The original exterior-square module isomorphism transports canonical degree
to the chosen representative. The proved rational-curve adjunction formula
then gives the exact original canonical matrix row value.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.CompatibleRationalAdjunctionDegree

/-- An actual canonical exterior-square identification and actual rational
curve isomorphism determine the exact original canonical intersection degree. -/
theorem canonical_intersection_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (C : S.PrimeCurve) (e : C.toScheme ≅ projectiveSpace k 1)
    (he : e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    C.intersectionNumber KS = -C.selfIntersectionNumber hregular - 2 := by
  have heq : C.intersectionNumber KS = C.intersectionNumber
      (SmoothCanonicalCartierRepresentative.cartierRepresentative S.structureMorphism) :=
    C.restrictionDegree_eq_of_iso
      (eKS ≪≫ (SmoothCanonicalCartierExterior.representativeIsoExterior S.structureMorphism).symm)
  have hadj := RationalPrimeCurveAdjunction.antiCanonical_degree S C e he
  rw [C.intersectionNumber_neg] at hadj
  rw [heq]
  omega

end KltDP.Geometry.CompatibleRationalAdjunctionDegree

#print axioms KltDP.Geometry.CompatibleRationalAdjunctionDegree.canonical_intersection_eq
