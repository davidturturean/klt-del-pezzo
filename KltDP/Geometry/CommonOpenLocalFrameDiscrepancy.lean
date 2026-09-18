import KltDP.Geometry.CommonOpenCanonicalLocalFrame
import KltDP.Geometry.NormalModelDiscrepancyNumerator

/-!
# The common-open local frame computes every Cartier numerator discrepancy

This identifies the actual local-frame expression at the original normal
model point with the source prime coefficient. Every positive Cartier
multiple of the original rational divisor is allowed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.CommonOpenCanonicalLocalFrame

attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {V W : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    (π : S.toScheme ⟶ X.toScheme) (v : V ⟶ X.toScheme)
    [GenericPointPreserving π] [GenericPointPreserving v]
    (iS : W ⟶ S.toScheme) (iV : W ⟶ V)
    [IsOpenImmersion iS] [IsOpenImmersion iV]
    (hcomm : iS ≫ π = iV ≫ v)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (w : W) (D : S.PrimeCurve) (x : CodimensionOnePoint V)
    (hwS : iS.base w = D.genericPoint) (hwV : iV.base w = x.val)
    [LocallyOfFiniteType (v ≫ X.structureMorphism)] (hnormal : IsNormalScheme V)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)

include hcomm hπ hwS hwV in
theorem localFrame_discrepancy_eq
    (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.rationalCartierToWeilHom A = n • B) :
    letI := normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
    NormalModelCanonical.discrepancyForCartierMultiple X v x.val
        (localFrame S X π v iS iV hcomm hπ w x.val hwV KS eKS) n A =
      (S.rationalCartierToWeilHom KS - QCartierPullback.pullback π B hB) D := by
  letI := normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
  letI := CommonOpenCanonicalCoefficient.commonOpen_isDiscreteValuationRing
    X v iV w x hwV hnormal
  have hnum := CommonOpenCanonicalCoefficient.discrepancy_expression_of_positive_multiple
    S X π v iS iV hcomm w D x hwS hwV hnormal KS B hB n hn A hA
  have horder := localFrame_order S X π v iS iV hcomm hπ w x.val hwV KS eKS D hwS
  have hlocal := CommonOpenCanonicalCoefficient.canonical_order
    S X v iS iV w D x hwS hwV hnormal KS
  change ((localFrame S X π v iS iV hcomm hπ w x.val hwV KS eKS).order : ℚ) -
    (cartierOrderAt V (DominantCartierPullback.pullbackHom v A) x.val : ℚ) / (n : ℚ) = _
  rw [horder]
  change (S.cartierToWeilHom KS D : ℚ) -
    (cartierOrderAt V (DominantCartierPullback.pullbackHom v A) x.val : ℚ) / (n : ℚ) =
      (S.cartierToWeilHom KS D : ℚ) - QCartierPullback.pullback π B hB D
  rw [hnum, ← hlocal]
  simp only [div_eq_mul_inv, mul_comm]

end KltDP.Geometry.CommonOpenCanonicalLocalFrame

#check @KltDP.Geometry.CommonOpenCanonicalLocalFrame.localFrame_discrepancy_eq
#print axioms KltDP.Geometry.CommonOpenCanonicalLocalFrame.localFrame_discrepancy_eq
