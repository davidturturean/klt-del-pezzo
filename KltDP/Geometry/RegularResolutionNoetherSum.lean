import KltDP.Geometry.ContractionNoetherSum
import KltDP.Geometry.IsomorphismCanonicalNumericalInvariants
import KltDP.Geometry.ResolutionContractionInduction
import KltDP.Geometry.SmoothCanonicalCartierExterior

/-!
# The original Noether sum along an actual regular-target resolution

The original minimalization induction retains each actual minus-one curve.
The base case is an actual isomorphism. Each step uses the proved canonical
square decrement and numerical rank increment for that same contraction.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open SmoothCanonicalExteriorComparison SmoothCanonicalCartierRepresentative
  SmoothCanonicalCartierExterior

/-- An actual resolution of an original regular surface preserves the
canonical-square plus numerical-Picard-rank sum. -/
theorem IsResolution.canonical_square_add_picardRank_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hres : IsResolution S X π)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    (KS : CartierDivisor S.toScheme) (KX : CartierDivisor X.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (eKX : cartierDivisorModule X.toScheme KX ≅
      relativeDifferentialExterior X.structureMorphism 2) :
    S.intersectionPairing hres.regular KS KS + (S.picardRank : ℤ) =
      X.intersectionPairing hX KX KX + (X.picardRank : ℤ) := by
  let P : NormalProjectiveSurface k → Prop := fun T =>
    ∀ (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
      (K : CartierDivisor T.toScheme),
      (cartierDivisorModule T.toScheme K ≅
          relativeDifferentialExterior T.structureMorphism 2) →
      T.intersectionPairing hT K K + (T.picardRank : ℤ) =
        X.intersectionPairing hX KX KX + (X.picardRank : ℤ)
  have h : P S := by
    apply hres.regular_target_induction hX P
    · intro T g hg hgk hT K eK
      letI : IsIso g := hg
      rw [IsomorphismSurfaceInvariants.canonical_square_eq g hgk hT hX K KX eK eKX,
        IsomorphismSurfaceInvariants.picardRank_eq g hgk hT hX]
    · intro T T' hT E b hminus hb ih hT0 K eK
      letI : IsSmoothOfRelativeDimension 2 T'.structureMorphism :=
        T'.isSmoothOfRelativeDimension_two_of_regularPoints hb.regular
      let K' := cartierRepresentative T'.structureMorphism
      let eK' : cartierDivisorModule T'.toScheme K' ≅
          relativeDifferentialExterior T'.structureMorphism 2 :=
        representativeIsoExterior T'.structureMorphism
      exact (hb.canonical_square_add_picardRank_eq hT hminus K K' eK eK').trans
        (ih hb.regular K' eK')
  exact h hres.regular KS eKS

end KltDP.Geometry

#check @KltDP.Geometry.IsResolution.canonical_square_add_picardRank_eq
#print axioms KltDP.Geometry.IsResolution.canonical_square_add_picardRank_eq
