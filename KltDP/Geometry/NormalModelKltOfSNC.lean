import KltDP.Geometry.NormalModelSNCDiscrepancyDetection
import KltDP.Geometry.NormalModelFrameNormalization
import KltDP.Geometry.NormalModelCanonicalFrameComparison
import KltDP.Geometry.CommonOpenLocalFrameDiscrepancy
import KltDP.Geometry.NormalModelKltPair

/-!
# The all-normal-model KLT criterion from an actual SNC discrepancy calculation

Every original normal-model divisor is detected on a finite point-blowup
sequence. The sequence supplies a canonical representative with the exact
target pushforward. Its normalized local frame exists at the original
valuation point, and every other normalized frame has the same order.
Every positive Cartier numerator then computes the proved discrepancy.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

open NormalProjectiveSurface NormalModelCanonical
open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)
attribute [local instance] integralSchemeStalk_isDomain

theorem isKltPairWithCanonicalDivisor_of_snc_discrepancy
    {k : Type u} [Field k] [IsAlgClosed k]
    (T X : NormalProjectiveSurface k) [IsSmooth T.structureMorphism]
    (g : T.toScheme ⟶ X.toScheme) [IsProper g] (hg : IsBirationalScheme g)
    (hgk : g ≫ X.structureMorphism = T.structureMorphism)
    (KT : CartierDivisor T.toScheme)
    (eKT : cartierDivisorModule T.toScheme KT ≅
      relativeDifferentialExterior T.structureMorphism 2)
    (KX : X.WeilDivisor) (hKX : IsCanonicalWeilDivisor X KX)
    (boundary : X.RationalWeilDivisor) (heffective : ∀ C : X.PrimeCurve, 0 ≤ boundary C)
    (hK : X.QCartier ((rationalizeWeilDivisor X KX + boundary)))
    (hpush : BirationalWeilPushforward.pushforward g hg (T.cartierToWeilHom KT) = KX)
    (A : CartierDivisor T.toScheme)
    (hA : IsStrictNormalCrossingsCartier T.toScheme A)
    (hcoeff : ∀ C : T.PrimeCurve,
      T.cartierToWeilHom A C = 0 ∨ T.cartierToWeilHom A C = 1) :
    letI : GenericPointPreserving g := ⟨hg.map_genericPoint⟩
    (T.rationalCartierToWeilHom KT -
      QCartierPullback.pullback g ((rationalizeWeilDivisor X KX + boundary)) hK).support ⊆
      (T.cartierToWeilHom A).support →
    (∀ C : T.PrimeCurve, (-1 : ℚ) <
      (T.rationalCartierToWeilHom KT -
        QCartierPullback.pullback g ((rationalizeWeilDivisor X KX + boundary)) hK) C) →
    IsKltPairWithCanonicalDivisor X KX boundary := by
  letI : GenericPointPreserving g := ⟨hg.map_genericPoint⟩
  intro hsupport hbound
  refine ⟨heffective, hKX, hK, ?_⟩
  intro U hne
  letI : Nonempty U.toScheme := hne
  letI : Nonempty U := ⟨Classical.choice hne⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  intro hUsmooth hU KU eKU hKU V hV hnormal v hvft hv x
  letI : IsIntegral V := hV
  letI : LocallyOfFiniteType (v ≫ X.structureMorphism) := hvft
  letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
  letI : IsDiscreteValuationRing (V.presheaf.stalk x.val) :=
    normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
  obtain ⟨S, π, hR, hS, KS, ⟨eKS⟩, hpushS, hboundS,
      D, W, iS, iV, w, hiS, hiV, hwS, hwV, hcomm⟩ :=
    exists_snc_canonical_common_open_at_normal_model_divisor T X g hg hgk KT eKT
      ((rationalizeWeilDivisor X KX + boundary)) hK A hA hcoeff hsupport hbound V hnormal v hv x
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism := hS
  letI : IsProper π := hR.isProper
  let hbir : IsBirationalScheme π :=
    ⟨hR.birational.map_genericPoint, hR.birational.isIso_stalkMap_genericPoint⟩
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : IsOpenImmersion iS := hiS
  letI : IsOpenImmersion iV := hiV
  letI : IsIntegral W := CommonOpenCanonicalCoefficient.commonOpen_isIntegral iS w
  have hcompatible : BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom KS) =
      OpenCartierWeil.restrictedWeilHom U KU := hpushS.trans (hpush.trans hKU.symm)
  obtain ⟨F, hF, hForder⟩ :=
    NormalModelFrameNormalization.exists_normalized_frame S X π hbir v iS iV hcomm
      hR.over_base w x.val hwV D hwS KS eKS U hU KU eKU hcompatible
  refine ⟨⟨F, hF⟩, ?_⟩
  intro G hG n hn L hL
  have hGF : G.order = F.order :=
    LocalFrame.order_eq_of_isNormalized X U KU eKU v x.val G F hG hF
  have hraw := CommonOpenCanonicalLocalFrame.localFrame_order
    S X π v iS iV hcomm hR.over_base w x.val hwV KS eKS D hwS
  have hGorder : G.order =
      (CommonOpenCanonicalLocalFrame.localFrame
        S X π v iS iV hcomm hR.over_base w x.val hwV KS eKS).order :=
    hGF.trans (hForder.trans hraw.symm)
  have hformula := CommonOpenCanonicalLocalFrame.localFrame_discrepancy_eq
    S X π v iS iV hcomm hR.over_base w D x hwS hwV hnormal KS eKS
    ((rationalizeWeilDivisor X KX + boundary)) hK n hn L hL
  have hformulaG : discrepancyForCartierMultiple X v x.val G n L =
      (S.rationalCartierToWeilHom KS -
        QCartierPullback.pullback π ((rationalizeWeilDivisor X KX + boundary)) hK) D := by
    simpa only [discrepancyForCartierMultiple, hGorder] using hformula
  rw [hformulaG]
  exact hboundS D

/-- The original zero-boundary criterion is the proved specialization. -/
theorem isKltWithCanonicalDivisor_of_snc_discrepancy
    {k : Type u} [Field k] [IsAlgClosed k]
    (T X : NormalProjectiveSurface k) [IsSmooth T.structureMorphism]
    (g : T.toScheme ⟶ X.toScheme) [IsProper g] (hg : IsBirationalScheme g)
    (hgk : g ≫ X.structureMorphism = T.structureMorphism)
    (KT : CartierDivisor T.toScheme)
    (eKT : cartierDivisorModule T.toScheme KT ≅
      relativeDifferentialExterior T.structureMorphism 2)
    (KX : X.WeilDivisor) (hKX : IsCanonicalWeilDivisor X KX)
    (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (hpush : BirationalWeilPushforward.pushforward g hg (T.cartierToWeilHom KT) = KX)
    (A : CartierDivisor T.toScheme)
    (hA : IsStrictNormalCrossingsCartier T.toScheme A)
    (hcoeff : ∀ C : T.PrimeCurve,
      T.cartierToWeilHom A C = 0 ∨ T.cartierToWeilHom A C = 1) :
    letI : GenericPointPreserving g := ⟨hg.map_genericPoint⟩
    (T.rationalCartierToWeilHom KT -
      QCartierPullback.pullback g (rationalizeWeilDivisor X KX) hK).support ⊆
      (T.cartierToWeilHom A).support →
    (∀ C : T.PrimeCurve, (-1 : ℚ) <
      (T.rationalCartierToWeilHom KT -
        QCartierPullback.pullback g (rationalizeWeilDivisor X KX) hK) C) →
    IsKltWithCanonicalDivisor X KX := by
  letI : GenericPointPreserving g := ⟨hg.map_genericPoint⟩
  intro hsupport hbound
  apply (isKltPairWithCanonicalDivisor_zero_iff X KX).mp
  apply isKltPairWithCanonicalDivisor_of_snc_discrepancy T X g hg hgk KT eKT
    KX hKX 0 (fun _ => le_rfl) (by simpa only [add_zero] using hK) hpush A hA hcoeff
  · simpa only [add_zero] using hsupport
  · simpa only [add_zero] using hbound

end KltDP.Geometry

#check @KltDP.Geometry.isKltPairWithCanonicalDivisor_of_snc_discrepancy
#print axioms KltDP.Geometry.isKltPairWithCanonicalDivisor_of_snc_discrepancy
#check @KltDP.Geometry.isKltWithCanonicalDivisor_of_snc_discrepancy
#print axioms KltDP.Geometry.isKltWithCanonicalDivisor_of_snc_discrepancy
