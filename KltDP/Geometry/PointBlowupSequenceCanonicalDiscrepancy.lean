import KltDP.Geometry.PointBlowupSequenceDiscrepancyPushforward
import KltDP.Geometry.BirationalCanonicalRepresentativeUnique

/-!
# Bounds for every normalized canonical representative on the original sequence

The constructed representative fixes the actual composite Weil pushforward.
Uniqueness identifies every other canonical Cartier representative with that
same pushforward, so the bound applies to every such original choice.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T X : NormalProjectiveSurface k}
  (g : T.toScheme ⟶ X.toScheme) [IsProper g] (hg : IsBirationalScheme g)

local instance : IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

theorem IsPointBlowupSequence.normalized_canonical_discrepancy_gt_neg_one
    [IsSmooth T.structureMorphism]
    {f : S.toScheme ⟶ T.toScheme} (h : IsPointBlowupSequence S T f)
    (K : CartierDivisor T.toScheme)
    (eK : cartierDivisorModule T.toScheme K ≅
      relativeDifferentialExterior T.structureMorphism 2)
    (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (A : CartierDivisor T.toScheme)
    (hA : IsStrictNormalCrossingsCartier T.toScheme A)
    (hcoeff : ∀ C : T.PrimeCurve,
      T.cartierToWeilHom A C = 0 ∨ T.cartierToWeilHom A C = 1) :
    letI : GenericPointPreserving g := ⟨hg.map_genericPoint⟩
    (T.rationalCartierToWeilHom K - QCartierPullback.pullback g B hB).support ⊆
      (T.cartierToWeilHom A).support →
    (∀ C : T.PrimeCurve,
      (-1 : ℚ) < (T.rationalCartierToWeilHom K - QCartierPullback.pullback g B hB) C) →
    letI : GenericPointPreserving f := h.genericPointPreserving
    letI : IsProper f := h.isProper
    ∀ (D : CartierDivisor S.toScheme)
      (eD : cartierDivisorModule S.toScheme D ≅
        relativeDifferentialExterior S.structureMorphism 2),
      BirationalWeilPushforward.pushforward (f ≫ g)
          (BirationalWeilPushforward.comp_isBirational f h.isBirationalScheme g hg)
          (S.cartierToWeilHom D) =
        BirationalWeilPushforward.pushforward g hg (T.cartierToWeilHom K) →
      ∀ C : S.PrimeCurve,
        (-1 : ℚ) < (S.rationalCartierToWeilHom D -
          QCartierPullback.pullback (f ≫ g) B hB) C := by
  letI : GenericPointPreserving g := ⟨hg.map_genericPoint⟩
  intro hsupport hbound
  letI : GenericPointPreserving f := h.genericPointPreserving
  letI : IsProper f := h.isProper
  intro D eD hD
  obtain ⟨K', A', ⟨eK'⟩, hpush', _, _, _, hbound'⟩ :=
    h.exists_canonical_discrepancy_boundary_with_pushforward
      g K eK B hB A hA hcoeff hsupport hbound
  have hpush : BirationalWeilPushforward.pushforward (f ≫ g)
      (BirationalWeilPushforward.comp_isBirational f h.isBirationalScheme g hg)
      (S.cartierToWeilHom K') =
      BirationalWeilPushforward.pushforward g hg (T.cartierToWeilHom K) := by
    rw [BirationalWeilPushforward.pushforward_comp, hpush']
  have heq : D = K' :=
    BirationalCanonicalRepresentative.eq_of_exterior_iso_of_pushforward_eq
      (f ≫ g) (BirationalWeilPushforward.comp_isBirational f h.isBirationalScheme g hg)
      D K' eD eK' (hD.trans hpush.symm)
  simpa only [heq] using hbound'

end KltDP.Geometry

#check @KltDP.Geometry.IsPointBlowupSequence.normalized_canonical_discrepancy_gt_neg_one
#print axioms KltDP.Geometry.IsPointBlowupSequence.normalized_canonical_discrepancy_gt_neg_one
