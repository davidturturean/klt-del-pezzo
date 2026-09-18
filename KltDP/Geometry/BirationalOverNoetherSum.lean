import KltDP.Geometry.RegularResolutionNoetherSum
import KltDP.Geometry.CommonResolutionFromBirationalOver

/-!
# The original Noether sum under an actual birational correspondence

The dense-open isomorphism constructs a common smooth resolution. Applying
the original regular-target resolution invariant to its two actual maps
compares arbitrary original canonical Cartier representatives.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open SmoothCanonicalExteriorComparison SmoothCanonicalCartierRepresentative
  SmoothCanonicalCartierExterior

/-- The canonical-square plus numerical-rank sum is preserved by the given
actual birational correspondence over the original field. -/
theorem canonical_square_add_picardRank_eq_of_birationalOver
    {k : Type u} [Field k] [IsAlgClosed k]
    (S T : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
    (h : Scheme.BirationalOver S.structureMorphism T.structureMorphism)
    (KS : CartierDivisor S.toScheme) (KT : CartierDivisor T.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (eKT : cartierDivisorModule T.toScheme KT ≅
      relativeDifferentialExterior T.structureMorphism 2) :
    S.intersectionPairing hS KS KS + (S.picardRank : ℤ) =
      T.intersectionPairing hT KT KT + (T.picardRank : ℤ) := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hS
  letI : IsSmooth S.structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism
  obtain ⟨Z, b, q, hb, hq, _, _⟩ := exists_common_resolution_of_birationalOver S T h
  letI : IsSmoothOfRelativeDimension 2 Z.structureMorphism :=
    Z.isSmoothOfRelativeDimension_two_of_regularPoints hb.regular
  let KZ := cartierRepresentative Z.structureMorphism
  let eKZ : cartierDivisorModule Z.toScheme KZ ≅
      relativeDifferentialExterior Z.structureMorphism 2 :=
    representativeIsoExterior Z.structureMorphism
  exact (hb.canonical_square_add_picardRank_eq hS KZ KS eKZ eKS).symm.trans
    (hq.canonical_square_add_picardRank_eq hT KZ KT eKZ eKT)

end KltDP.Geometry

#check @KltDP.Geometry.canonical_square_add_picardRank_eq_of_birationalOver
#print axioms KltDP.Geometry.canonical_square_add_picardRank_eq_of_birationalOver
