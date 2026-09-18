import KltDP.Geometry.MinimalExceptionalCanonicalDegree
import KltDP.Geometry.SmoothCanonicalCartierExterior

/-! Actual exterior-square identifications preserve the canonical degree on
an original rational exceptional prime of the original minimal resolution. -/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- The minimal-resolution canonical degree bound holds for any actual
compatible exterior-square Cartier representative, not just the chosen one. -/
theorem IsMinimalResolution.canonical_degree_nonneg_of_rational_exceptional
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {π : S.toScheme ⟶ X.toScheme}
    (hmin : IsMinimalResolution S X π)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (C : S.PrimeCurve) (hC : IsExceptionalCurve π C)
    (e : C.toScheme ≅ projectiveSpace k 1)
    (he : e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    0 ≤ C.intersectionNumber KS := by
  have hdegree := hmin.rational_exceptional_canonical_degree_nonneg C hC e he
  have heq : C.intersectionNumber KS = C.intersectionNumber
      (SmoothCanonicalCartierRepresentative.cartierRepresentative S.structureMorphism) :=
    C.restrictionDegree_eq_of_iso
      (eKS ≪≫ (SmoothCanonicalCartierExterior.representativeIsoExterior S.structureMorphism).symm)
  rw [heq]
  exact hdegree

end KltDP.Geometry

#check @KltDP.Geometry.IsMinimalResolution.canonical_degree_nonneg_of_rational_exceptional
#print axioms KltDP.Geometry.IsMinimalResolution.canonical_degree_nonneg_of_rational_exceptional
