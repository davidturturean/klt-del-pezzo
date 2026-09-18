import KltDP.Geometry.PointBlowupAtDiscrepancyBoundary
import KltDP.Geometry.PointBlowupAtCanonicalPushforward

/-!
# An original point step with exact canonical pushforward

The canonical divisor is the same explicit chart divisor pulled through
the isomorphism in the original point-blowup relation. Its exact Weil
pushforward is retained together with its actual canonical module and
the constructed SNC boundary and literal discrepancy bounds.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

open PointBlowupGluing PointBlowupExceptionalPrimeStalk
open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {S T X : NormalProjectiveSurface k}

private theorem pullback_eq_from_original_triangle
    (f g : S.toScheme ⟶ X.toScheme) [GenericPointPreserving f] [GenericPointPreserving g]
    (h : f = g) (B : X.RationalWeilDivisor) (hB : X.QCartier B) :
    QCartierPullback.pullback f B hB = QCartierPullback.pullback g B hB := by
  subst g
  rfl

local instance : IsLocallyNoetherian S.toScheme := S.isLocallyNoetherian
local instance : IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

/-- The actual new canonical representative has the specified original
Weil pushforward, and its discrepancy is contained in a constructed SNC
boundary with coefficients zero or one and every discrepancy coefficient
strictly greater than minus one. -/
theorem IsPointBlowupAt.exists_canonical_discrepancy_boundary_with_pushforward
    [IsSmooth T.structureMorphism] {b : S.toScheme ⟶ T.toScheme} {x : T.Point}
    (hb : IsPointBlowupAt S T b x)
    (g : T.toScheme ⟶ X.toScheme) [GenericPointPreserving g]
    (KT : CartierDivisor T.toScheme)
    (eKT : cartierDivisorModule T.toScheme KT ≅
      relativeDifferentialExterior T.structureMorphism 2)
    (BX : X.RationalWeilDivisor) (hBX : X.QCartier BX)
    (AT : CartierDivisor T.toScheme) (hAT : IsStrictNormalCrossingsCartier T.toScheme AT)
    (hcoeff : ∀ C : T.PrimeCurve,
      T.cartierToWeilHom AT C = 0 ∨ T.cartierToWeilHom AT C = 1)
    (hcontains : (T.rationalCartierToWeilHom KT - QCartierPullback.pullback g BX hBX).support ⊆
      (T.cartierToWeilHom AT).support)
    (hbound : ∀ C : T.PrimeCurve,
      (-1 : ℚ) < (T.rationalCartierToWeilHom KT - QCartierPullback.pullback g BX hBX) C) :
    letI : GenericPointPreserving b := hb.genericPointPreserving
    letI : IsProper b := hb.isProper
    ∃ (KS AS : CartierDivisor S.toScheme),
      Nonempty (cartierDivisorModule S.toScheme KS ≅
        relativeDifferentialExterior S.structureMorphism 2) ∧
      BirationalWeilPushforward.pushforward b hb.isBirationalScheme (S.cartierToWeilHom KS) =
        T.cartierToWeilHom KT ∧
      IsStrictNormalCrossingsCartier S.toScheme AS ∧
      (∀ C : S.PrimeCurve,
        S.cartierToWeilHom AS C = 0 ∨ S.cartierToWeilHom AS C = 1) ∧
      (S.rationalCartierToWeilHom KS - QCartierPullback.pullback (b ≫ g) BX hBX).support ⊆
        (S.cartierToWeilHom AS).support ∧
      ∀ C : S.PrimeCurve,
        (-1 : ℚ) < (S.rationalCartierToWeilHom KS -
          QCartierPullback.pullback (b ≫ g) BX hBX) C := by
  letI : GenericPointPreserving b := hb.genericPointPreserving
  letI : IsProper b := hb.isProper
  obtain ⟨c, e, he⟩ := hb.blowup
  letI := c.instCommRing
  letI := c.instOpenImmersion
  letI := c.instMaximal
  let W := sourceSurface T c.j c.q c.isClosed
  let e' : S.toScheme ≅ W.toScheme := e
  let π : W.toScheme ⟶ T.toScheme := projection c.j c.q c.isClosed
  letI : IsLocallyNoetherian W.toScheme := W.isLocallyNoetherian
  letI : GenericPointPreserving π :=
    ⟨(PointBlowupCanonicalCartier.isBirational_projection T c.j c.q c.isClosed).map_genericPoint⟩
  letI : GenericPointPreserving e'.hom := ⟨genericPoint_eq_of_isOpenImmersion e'.hom⟩
  have hprojection : e'.hom ≫ π = b := he
  have hstructure : e'.hom ≫ W.structureMorphism = S.structureMorphism := by
    change e'.hom ≫ (π ≫ T.structureMorphism) = _
    rw [← Category.assoc, hprojection, hb.over_base]
  let KW := PointBlowupCanonicalCartier.divisor T c.j c.q c.isClosed KT
  let eKW : cartierDivisorModule W.toScheme KW ≅
      relativeDifferentialExterior W.structureMorphism 2 :=
    PointBlowupCanonicalCartier.canonicalModuleIso T c.j c.q c.isClosed KT eKT
  obtain ⟨AW, hAW, hcoeffW, hcontainsW, hboundW⟩ :=
    PointBlowupDiscrepancy.exists_reduced_boundary_with_discrepancy_bounds
      T X c.j c.q c.isClosed g KT BX hBX AT hAT hcoeff hcontains hbound
  let KS := DominantCartierPullback.pullbackHom e'.hom KW
  let AS := DominantCartierPullback.pullbackHom e'.hom AW
  have eKS : cartierDivisorModule S.toScheme KS ≅
      relativeDifferentialExterior S.structureMorphism 2 :=
    CanonicalCartierOpenPullback.canonicalModuleIso e'.hom W.structureMorphism
      S.structureMorphism hstructure KW eKW
  have hpush : BirationalWeilPushforward.pushforward b hb.isBirationalScheme
      (S.cartierToWeilHom KS) = T.cartierToWeilHom KT :=
    hb.canonicalChart_pushforward c e he KT
  have hAS : IsStrictNormalCrossingsCartier S.toScheme AS :=
    DominantCartierPullback.isStrictNormalCrossingsCartier_of_iso e' AW hAW
  obtain ⟨hcoeffS, hcontainsS, hboundS⟩ := IsomorphismDiscrepancy.pullback_boundary_data
    e' (π ≫ g) KW BX hBX AW hcoeffW hcontainsW hboundW
  have hcomp : e'.hom ≫ (π ≫ g) = b ≫ g := by rw [← Category.assoc, hprojection]
  have hpullback := pullback_eq_from_original_triangle
    (e'.hom ≫ (π ≫ g)) (b ≫ g) hcomp BX hBX
  refine ⟨KS, AS, ⟨eKS⟩, hpush, hAS, hcoeffS, ?_, ?_⟩
  · simpa only [hpullback] using hcontainsS
  · simpa only [hpullback] using hboundS

end KltDP.Geometry

#check @KltDP.Geometry.IsPointBlowupAt.exists_canonical_discrepancy_boundary_with_pushforward
#print axioms KltDP.Geometry.IsPointBlowupAt.exists_canonical_discrepancy_boundary_with_pushforward
