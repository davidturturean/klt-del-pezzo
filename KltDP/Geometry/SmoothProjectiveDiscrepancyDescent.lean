import KltDP.Geometry.PointBlowupSequenceDiscrepancyPushforward
import KltDP.Geometry.CanonicalWeilBirationalRepresentative
import KltDP.Geometry.CanonicalWeilOfCartier
import KltDP.Geometry.BirationalCanonicalRepresentativeUnique
import KltDP.Geometry.BirationalPullbackDifference
import KltDP.Geometry.CommonSmoothProperModel
import KltDP.Geometry.SmoothSurfaceRelativeDimension

/-!
# Discrepancy bounds on every smooth projective birational model

An actual common smooth model is constructed by point blowups of the
given SNC model. Canonical representatives on it are identified using
their original differential sheaves and exact pushforward to the original
target. The existing coefficient descent then applies to the independently
chosen canonical divisor on the other original smooth model.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

open BirationalWeilPushforward
open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)

local instance {k : Type u} [Field k] (Y : NormalProjectiveSurface k) :
    IsLocallyNoetherian Y.toScheme := Y.isLocallyNoetherian

/-- Bounds from an actual reduced SNC containing boundary hold on every
other original smooth projective birational model, for every canonical
Cartier divisor with the same exact target Weil pushforward. -/
theorem canonical_discrepancy_gt_neg_one_on_smooth_projective_model
    {k : Type u} [Field k] [IsAlgClosed k]
    (T X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 T.structureMorphism]
    (g : T.toScheme ⟶ X.toScheme) [IsProper g]
    (hg : IsBirationalScheme g)
    (hgk : g ≫ X.structureMorphism = T.structureMorphism)
    (KT : CartierDivisor T.toScheme)
    (eKT : cartierDivisorModule T.toScheme KT ≅
      relativeDifferentialExterior T.structureMorphism 2)
    (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (A : CartierDivisor T.toScheme)
    (hA : IsStrictNormalCrossingsCartier T.toScheme A)
    (hcoeff : ∀ C : T.PrimeCurve,
      T.cartierToWeilHom A C = 0 ∨ T.cartierToWeilHom A C = 1) :
    letI : GenericPointPreserving g := ⟨hg.map_genericPoint⟩
    (T.rationalCartierToWeilHom KT - QCartierPullback.pullback g B hB).support ⊆
      (T.cartierToWeilHom A).support →
    (∀ C : T.PrimeCurve, (-1 : ℚ) <
      (T.rationalCartierToWeilHom KT - QCartierPullback.pullback g B hB) C) →
    ∀ (V : NormalProjectiveSurface k)
      (_ : IsSmoothOfRelativeDimension 2 V.structureMorphism)
      (v : V.toScheme ⟶ X.toScheme) [hvproper : IsProper v]
      (hv : IsBirationalScheme v)
      (_ : v ≫ X.structureMorphism = V.structureMorphism)
      (KV : CartierDivisor V.toScheme),
      (cartierDivisorModule V.toScheme KV ≅
        relativeDifferentialExterior V.structureMorphism 2) →
      pushforward v hv (V.cartierToWeilHom KV) = pushforward g hg (T.cartierToWeilHom KT) →
      letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
      ∀ C : V.PrimeCurve, (-1 : ℚ) <
        (V.rationalCartierToWeilHom KV - QCartierPullback.pullback v B hB) C := by
  letI : GenericPointPreserving g := ⟨hg.map_genericPoint⟩
  intro hsupport hbound V hV v hvproper hv hvk KV eKV hcompatible
  letI : IsSmooth T.structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 T.structureMorphism
  letI : IsSmoothOfRelativeDimension 2 V.structureMorphism := hV
  letI : IsSmooth V.structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 V.structureMorphism
  letI : IsProper v := hvproper
  letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
  obtain ⟨S, b, q, hbR, hS, hseq, hq, hqproper, hqk, _, _, hfac, _⟩ :=
    exists_common_smooth_projective_domination T X g v hg hv hgk
  letI : IsSmooth S.structureMorphism := hS
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two
  letI : IsProper b := hseq.isProper
  letI : GenericPointPreserving b := hseq.genericPointPreserving
  letI : IsProper q := hqproper
  letI : GenericPointPreserving q := ⟨hq.map_genericPoint⟩
  obtain ⟨KS, AS, ⟨eKS⟩, hKS, _, _, _, hboundS⟩ :=
    hseq.exists_canonical_discrepancy_boundary_with_pushforward
      g KT eKT B hB A hA hcoeff hsupport hbound
  have hqV : q ≫ V.structureMorphism = S.structureMorphism := by
    rw [← hvk]
    exact hqk
  obtain ⟨L, ⟨eL⟩, hL⟩ :=
    IsCanonicalWeilDivisor.exists_compatible_canonical_cartier S V q hqV hq
      (V.cartierToWeilHom KV) (IsCanonicalWeilDivisor.of_cartier V KV eKV)
  have hqv := comp_isBirational q hq v hv
  have hLpush : pushforward (q ≫ v) hqv (S.cartierToWeilHom L) =
      pushforward g hg (T.cartierToWeilHom KT) := by
    rw [pushforward_comp q hq v hv, hL, hcompatible]
  have hKSpush : pushforward (q ≫ v) hqv (S.cartierToWeilHom KS) =
      pushforward g hg (T.cartierToWeilHom KT) := by
    have hbpush : pushforward (b ≫ g) (comp_isBirational b hseq.isBirationalScheme g hg)
        (S.cartierToWeilHom KS) = pushforward g hg (T.cartierToWeilHom KT) := by
      rw [pushforward_comp b hseq.isBirationalScheme g hg, hKS]
    simpa only [hfac] using hbpush
  have hLK : L = KS :=
    BirationalCanonicalRepresentative.eq_of_exterior_iso_of_pushforward_eq
      (q ≫ v) hqv L KS eL eKS (hLpush.trans hKSpush.symm)
  have hKSq : pushforward q hq (S.cartierToWeilHom KS) = V.cartierToWeilHom KV := by
    rw [← hLK]
    exact hL
  have hKSqRat : rationalPushforward q hq (S.rationalCartierToWeilHom KS) =
      V.rationalCartierToWeilHom KV :=
    (rationalPushforward_rationalize q hq (S.cartierToWeilHom KS)).trans
      (congrArg (NormalProjectiveSurface.rationalizeWeilDivisor V) hKSq)
  have hboundS' : ∀ C : S.PrimeCurve, (-1 : ℚ) <
      (S.rationalCartierToWeilHom KS - QCartierPullback.pullback (q ≫ v) B hB) C := by
    simpa only [hfac] using hboundS
  have hdesc := coefficient_gt_neg_one_difference_of_composite
    q v hq (S.rationalCartierToWeilHom KS) B hB hboundS'
  rw [hKSqRat] at hdesc
  exact hdesc

end KltDP.Geometry

#check @KltDP.Geometry.canonical_discrepancy_gt_neg_one_on_smooth_projective_model
#print axioms KltDP.Geometry.canonical_discrepancy_gt_neg_one_on_smooth_projective_model
