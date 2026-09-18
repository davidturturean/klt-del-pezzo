import KltDP.Geometry.PointBlowupCanonicalDivisor
import KltDP.Geometry.IsomorphismDiscrepancy
import KltDP.Geometry.SurfacePointBlowupSequenceBirational

/-!
# Exact canonical pushforward through an original point-blowup chart

The actual source isomorphism preserves the Cartier coefficient at its
original image prime. Uniqueness of the prime above each original target
prime identifies the two pushforward evaluations. Applied to the proved
chart divisor, this gives its exact pushforward along the original b.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Original Cartier pullback through a source isomorphism preserves the
actual Weil pushforward along the commuting original morphisms. -/
theorem BirationalWeilPushforward.source_iso_cartier
    {S W T : NormalProjectiveSurface k} (e : S.toScheme ≅ W.toScheme)
    (b : S.toScheme ⟶ T.toScheme) [IsProper b] (hb : IsBirationalScheme b)
    (π : W.toScheme ⟶ T.toScheme) [IsProper π] (hπ : IsBirationalScheme π)
    (he : e.hom ≫ π = b) (D : CartierDivisor W.toScheme) :
    letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
    BirationalWeilPushforward.pushforward b hb
      (S.cartierToWeilHom (DominantCartierPullback.pullbackHom e.hom D)) =
      BirationalWeilPushforward.pushforward π hπ (W.cartierToWeilHom D) := by
  letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
  apply Finsupp.ext
  intro C
  let CS := BirationalPrimeCorrespondence.abovePrimeCurve b hb C
  obtain ⟨CW, hgen, _, hcoeff, _⟩ :=
    IsomorphismDiscrepancy.exists_prime_preserving_coefficients e CS
  have hπCW : π.base CW.genericPoint = C.genericPoint := by
    calc
      _ = π.base (e.hom.base CS.genericPoint) := congrArg π.base hgen.symm
      _ = b.base CS.genericPoint :=
        congrArg (fun f : S.toScheme ⟶ T.toScheme => f.base CS.genericPoint) he
      _ = _ := BirationalPrimeCorrespondence.abovePrimeCurve_map_genericPoint b hb C
  have hCW := BirationalPrimeCorrespondence.abovePrimeCurve_unique π hπ C CW hπCW
  change S.cartierToWeilHom (DominantCartierPullback.pullbackHom e.hom D) CS =
    W.cartierToWeilHom D (BirationalPrimeCorrespondence.abovePrimeCurve π hπ C)
  exact (hcoeff D).trans (congrArg (W.cartierToWeilHom D) hCW)

open PointBlowupGluing PointBlowupExceptionalPrimeStalk

/-- The specific original chart canonical divisor, pulled through the
isomorphism contained in hb, pushes exactly to the specified base divisor. -/
theorem IsPointBlowupAt.canonicalChart_pushforward
    {S T : NormalProjectiveSurface k} [IsSmooth T.structureMorphism]
    {b : S.toScheme ⟶ T.toScheme} {x : T.Point} (hb : IsPointBlowupAt S T b x)
    (c : PointBlowupChart T.toScheme x) (e : S.toScheme ≅ c.scheme)
    (he : e.hom ≫ c.projection = b) (KT : CartierDivisor T.toScheme) :
    letI := c.instCommRing
    letI := c.instOpenImmersion
    letI := c.instMaximal
    let W := sourceSurface T c.j c.q c.isClosed
    let e' : S.toScheme ≅ W.toScheme := e
    letI : GenericPointPreserving e'.hom := ⟨genericPoint_eq_of_isOpenImmersion e'.hom⟩
    letI : IsProper b := hb.isProper
    BirationalWeilPushforward.pushforward b hb.isBirationalScheme
      (S.cartierToWeilHom (DominantCartierPullback.pullbackHom e'.hom
        (PointBlowupCanonicalCartier.divisor T c.j c.q c.isClosed KT))) =
      T.cartierToWeilHom KT := by
  letI := c.instCommRing
  letI := c.instOpenImmersion
  letI := c.instMaximal
  let W := sourceSurface T c.j c.q c.isClosed
  let e' : S.toScheme ≅ W.toScheme := e
  let π : W.toScheme ⟶ T.toScheme := projection c.j c.q c.isClosed
  letI : GenericPointPreserving e'.hom := ⟨genericPoint_eq_of_isOpenImmersion e'.hom⟩
  letI : IsProper b := hb.isProper
  letI : IsProper π := projection_isProper_of_fg c.j c.q c.isClosed
    (T.affine_point_ideal_fg c.j c.q)
  have hπ : IsBirationalScheme π :=
    PointBlowupCanonicalCartier.isBirational_projection T c.j c.q c.isClosed
  exact (BirationalWeilPushforward.source_iso_cartier e' b hb.isBirationalScheme π hπ he
    (PointBlowupCanonicalCartier.divisor T c.j c.q c.isClosed KT)).trans
      (PointBlowupCanonicalCartier.divisor_pushforward T c.j c.q c.isClosed KT)

end KltDP.Geometry

#check @KltDP.Geometry.IsPointBlowupAt.canonicalChart_pushforward
#print axioms KltDP.Geometry.IsPointBlowupAt.canonicalChart_pushforward
