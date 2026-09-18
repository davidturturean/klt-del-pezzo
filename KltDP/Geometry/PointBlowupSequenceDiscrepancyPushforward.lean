import KltDP.Geometry.PointBlowupAtDiscrepancyPushforward
import KltDP.Geometry.IsomorphismCanonicalDiscrepancyPushforward
import KltDP.Geometry.BirationalWeilPushforwardComp

/-!
# Finite discrepancy propagation with the original canonical choice fixed

The constructed source canonical Cartier divisor pushes forward to the
specified original target Cartier divisor. Every step also constructs a
reduced SNC containing boundary and preserves the strict coefficient bound.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance (Y : NormalProjectiveSurface k) : IsLocallyNoetherian Y.toScheme :=
  Y.isLocallyNoetherian

theorem IsPointBlowupSequence.exists_canonical_discrepancy_boundary_with_pushforward
    {S T X : NormalProjectiveSurface k} [hT : IsSmooth T.structureMorphism]
    {f : S.toScheme ⟶ T.toScheme} (h : IsPointBlowupSequence S T f)
    (g : T.toScheme ⟶ X.toScheme) [GenericPointPreserving g]
    (K : CartierDivisor T.toScheme)
    (eK : cartierDivisorModule T.toScheme K ≅
      relativeDifferentialExterior T.structureMorphism 2)
    (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (A : CartierDivisor T.toScheme)
    (hA : IsStrictNormalCrossingsCartier T.toScheme A)
    (hcoeff : ∀ C : T.PrimeCurve,
      T.cartierToWeilHom A C = 0 ∨ T.cartierToWeilHom A C = 1)
    (hsupport : (T.rationalCartierToWeilHom K - QCartierPullback.pullback g B hB).support ⊆
      (T.cartierToWeilHom A).support)
    (hbound : ∀ C : T.PrimeCurve,
      (-1 : ℚ) < (T.rationalCartierToWeilHom K - QCartierPullback.pullback g B hB) C) :
    letI : GenericPointPreserving f := h.genericPointPreserving
    letI : IsProper f := h.isProper
    ∃ (K' A' : CartierDivisor S.toScheme),
      Nonempty (cartierDivisorModule S.toScheme K' ≅
        relativeDifferentialExterior S.structureMorphism 2) ∧
      BirationalWeilPushforward.pushforward f h.isBirationalScheme
        (S.cartierToWeilHom K') = T.cartierToWeilHom K ∧
      IsStrictNormalCrossingsCartier S.toScheme A' ∧
      (∀ C : S.PrimeCurve,
        S.cartierToWeilHom A' C = 0 ∨ S.cartierToWeilHom A' C = 1) ∧
      (S.rationalCartierToWeilHom K' - QCartierPullback.pullback (f ≫ g) B hB).support ⊆
        (S.cartierToWeilHom A').support ∧
      ∀ C : S.PrimeCurve,
        (-1 : ℚ) < (S.rationalCartierToWeilHom K' -
          QCartierPullback.pullback (f ≫ g) B hB) C := by
  revert g K eK A hA hcoeff hsupport hbound
  revert hT
  induction h with
  | of_isIso f hf hover =>
      intro hT g hg K eK A hA hcoeff hsupport hbound
      letI := hT
      letI := hg
      letI := hf
      letI : GenericPointPreserving f := ⟨genericPoint_eq_of_isOpenImmersion f⟩
      refine ⟨DominantCartierPullback.pullbackHom f K,
        DominantCartierPullback.pullbackHom f A, ?_⟩
      exact IsomorphismDiscrepancy.pullback_canonical_boundary_with_pushforward
        (asIso f) hover g K eK B hB A hA hcoeff hsupport hbound
  | @step S S' T b p x hb hp ih =>
      intro hT g hg K eK A hA hcoeff hsupport hbound
      letI := hT
      letI := hg
      letI : GenericPointPreserving b := hb.genericPointPreserving
      letI : GenericPointPreserving p := hp.genericPointPreserving
      letI : IsProper b := hb.isProper
      letI : IsProper p := hp.isProper
      letI : IsSmooth S'.structureMorphism := hp.source_isSmooth
      obtain ⟨K', A', ⟨eK'⟩, hpush', hA', hcoeff', hsupport', hbound'⟩ :=
        @ih hT g hg K eK A hA hcoeff hsupport hbound
      obtain ⟨K'', A'', eK'', hpush'', hA'', hcoeff'', hsupport'', hbound''⟩ :=
        hb.exists_canonical_discrepancy_boundary_with_pushforward
          (p ≫ g) K' eK' B hB A' hA' hcoeff' hsupport' hbound'
      refine ⟨K'', A'', eK'', ?_, hA'', hcoeff'', ?_, ?_⟩
      · rw [BirationalWeilPushforward.pushforward_comp
          b hb.isBirationalScheme p hp.isBirationalScheme, hpush'', hpush']
      · simpa only [Category.assoc] using hsupport''
      · simpa only [Category.assoc] using hbound''

end KltDP.Geometry

#check @KltDP.Geometry.IsPointBlowupSequence.exists_canonical_discrepancy_boundary_with_pushforward
#print axioms KltDP.Geometry.IsPointBlowupSequence.exists_canonical_discrepancy_boundary_with_pushforward
