import KltDP.Geometry.CommonOpenCanonicalCoefficient

/-!
# Original normal-model discrepancy with every positive Cartier numerator

The common-open comparison holds for every positive integral Cartier
multiple of the original rational divisor. The original normal model need
not be proper. This makes the formula available without fixing a Cartier
index or choosing a rational-divisor pullback on that model.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CommonOpenCanonicalCoefficient

open OpenImmersionRational DominantCartierPullback

attribute [local instance] integralSchemeStalk_isDomain

local instance numeratorOpenGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (e : Y ⟶ Z) [IsOpenImmersion e] : GenericPointPreserving e :=
  ⟨genericPoint_eq_of_isOpenImmersion e⟩

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S X : NormalProjectiveSurface k)
    {V W : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    (π : S.toScheme ⟶ X.toScheme) (v : V ⟶ X.toScheme)
    [GenericPointPreserving π] [GenericPointPreserving v]
    (iS : W ⟶ S.toScheme) (iV : W ⟶ V)
    [IsOpenImmersion iS] [IsOpenImmersion iV]
    (hcomm : iS ≫ π = iV ≫ v)
    (w : W) (D : S.PrimeCurve) (x : CodimensionOnePoint V)
    (hwS : iS.base w = D.genericPoint) (hwV : iV.base w = x.val)
    [LocallyOfFiniteType (v ≫ X.structureMorphism)] (hnormal : IsNormalScheme V)

include hcomm hwS hwV in
/-- Every positive numerator computes the same original discrepancy. -/
theorem discrepancy_expression_of_positive_multiple
    (KS : CartierDivisor S.toScheme) (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.rationalCartierToWeilHom A = n • B) :
    letI := commonOpen_isDiscreteValuationRing X v iV w x hwV hnormal
    letI := normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
    (S.cartierToWeilHom KS D : ℚ) - QCartierPullback.pullback π B hB D =
      (cartierOrderAt W (pullbackHom iS KS) w : ℚ) -
        (n : ℚ)⁻¹ * (cartierOrderAt V (pullbackHom v A) x.val : ℚ) := by
  letI := commonOpen_isDiscreteValuationRing X v iV w x hwV hnormal
  letI := normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
  have hnum := QCartierPullback.pullbackToWeil_eq_of_positive_multiple π ⟨B, hB⟩ n hn A hA
  change (S.cartierToWeilHom KS D : ℚ) - QCartierPullback.pullbackToWeil π ⟨B, hB⟩ D = _
  rw [hnum]
  change (S.cartierToWeilHom KS D : ℚ) -
    (n : ℚ)⁻¹ * (S.cartierToWeilHom (pullbackHom π A) D : ℚ) = _
  rw [canonical_order S X v iS iV w D x hwS hwV hnormal,
    pullback_order S X π v iS iV hcomm w D x hwS hwV hnormal A]

end KltDP.Geometry.CommonOpenCanonicalCoefficient

#check @KltDP.Geometry.CommonOpenCanonicalCoefficient.discrepancy_expression_of_positive_multiple
#print axioms KltDP.Geometry.CommonOpenCanonicalCoefficient.discrepancy_expression_of_positive_multiple
