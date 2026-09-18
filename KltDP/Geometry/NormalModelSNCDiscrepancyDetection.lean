import KltDP.Geometry.NormalModelCommonOpenDetection
import KltDP.Geometry.PointBlowupSequenceDiscrepancyPushforward

/-!
# SNC discrepancy data at every original normal-model divisor

The actual valuation-detection construction supplies a finite point-blowup
sequence of the given smooth surface. The proved sequence induction then
supplies its canonical divisor, exact original target pushforward and strict
discrepancy bound. The original model and point remain on an actual common
open; no properness assumption on that model is introduced.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)
open BirationalWeilPushforward

theorem exists_snc_canonical_common_open_at_normal_model_divisor
    {k : Type u} [Field k] [IsAlgClosed k]
    (T X : NormalProjectiveSurface k) [IsSmooth T.structureMorphism]
    (g : T.toScheme ⟶ X.toScheme) [IsProper g] (hg : IsBirationalScheme g)
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
    ∀ (V : Scheme.{u}) [IsIntegral V] (hnormal : IsNormalScheme V)
      (v : V ⟶ X.toScheme) [LocallyOfFiniteType (v ≫ X.structureMorphism)]
      (hv : IsBirationalScheme v) (x : CodimensionOnePoint V),
      ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme)
        (hR : IsResolution S X π),
        IsSmoothOfRelativeDimension 2 S.structureMorphism ∧
        letI : IsProper π := hR.isProper
        let hbir : IsBirationalScheme π :=
          ⟨hR.birational.map_genericPoint, hR.birational.isIso_stalkMap_genericPoint⟩
        letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
        ∃ KS : CartierDivisor S.toScheme,
          Nonempty (cartierDivisorModule S.toScheme KS ≅
            relativeDifferentialExterior S.structureMorphism 2) ∧
          pushforward π hbir (S.cartierToWeilHom KS) =
            pushforward g hg (T.cartierToWeilHom KT) ∧
          (∀ C : S.PrimeCurve, (-1 : ℚ) <
            (S.rationalCartierToWeilHom KS - QCartierPullback.pullback π B hB) C) ∧
          ∃ (D : S.PrimeCurve) (W : Scheme.{u}) (iS : W ⟶ S.toScheme)
            (iV : W ⟶ V) (w : W),
            IsOpenImmersion iS ∧ IsOpenImmersion iV ∧
            iS.base w = D.genericPoint ∧ iV.base w = x.val ∧ iS ≫ π = iV ≫ v := by
  letI : GenericPointPreserving g := ⟨hg.map_genericPoint⟩
  intro hsupport hbound V hV hnormal v hvft hv x
  letI : IsIntegral V := hV
  letI : LocallyOfFiniteType (v ≫ X.structureMorphism) := hvft
  obtain ⟨S, π, hR, hS, ⟨b, hbR, hseq, hπ⟩, D, W, iS, iV, w,
      hiS, hiV, hwS, hwV, hcomm⟩ :=
    exists_smooth_resolution_common_open_at_normal_model_divisor
      T X hnormal g v hg hv hgk x
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism := hS
  letI : IsProper b := hseq.isProper
  letI : GenericPointPreserving b := hseq.genericPointPreserving
  letI : IsProper π := hR.isProper
  let hbir : IsBirationalScheme π :=
    ⟨hR.birational.map_genericPoint, hR.birational.isIso_stalkMap_genericPoint⟩
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  obtain ⟨KS, AS, heKS, hpush, _, _, _, hboundS⟩ :=
    hseq.exists_canonical_discrepancy_boundary_with_pushforward
      g KT eKT B hB A hA hcoeff hsupport hbound
  refine ⟨S, π, hR, hS, KS, heKS, ?_, ?_,
    D, W, iS, iV, w, hiS, hiV, hwS, hwV, hcomm⟩
  · have hbgpush : pushforward (b ≫ g) (comp_isBirational b hseq.isBirationalScheme g hg)
        (S.cartierToWeilHom KS) = pushforward g hg (T.cartierToWeilHom KT) := by
      rw [pushforward_comp b hseq.isBirationalScheme g hg, hpush]
    simpa only [hπ] using hbgpush
  · simpa only [hπ] using hboundS

end KltDP.Geometry

#check @KltDP.Geometry.exists_snc_canonical_common_open_at_normal_model_divisor
#print axioms KltDP.Geometry.exists_snc_canonical_common_open_at_normal_model_divisor
