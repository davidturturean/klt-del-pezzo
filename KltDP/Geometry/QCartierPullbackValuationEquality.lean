import KltDP.Geometry.CartierPullbackValuationEquality
import KltDP.Geometry.QCartierPullback
import KltDP.Geometry.PrimeCurveOrder

/-!
# Equal original valuations give equal rational Cartier pullback coefficients

The integral comparison is the original Cartier order comparison. Clearing
one actual positive Cartier denominator then compares the original rational
pullbacks, with no chosen denominator in the final statement.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.QCartierPullback

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S V X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) (v : V.toScheme ⟶ X.toScheme)
  [GenericPointPreserving π] [GenericPointPreserving v]
  (D : S.PrimeCurve) (C : V.PrimeCurve)
  (hcenter : π.base D.genericPoint = v.base C.genericPoint)
  (horder : ∀ a : X.toScheme.functionFieldˣ,
    D.order (Units.map (functionFieldMap π).hom.toMonoidHom a) =
      C.order (Units.map (functionFieldMap v).hom.toMonoidHom a))

include hcenter horder

theorem cartier_coefficient_eq_of_valuation_eq (A : CartierDivisor X.toScheme) :
    S.cartierToWeilHom (DominantCartierPullback.pullbackHom π A) D =
      V.cartierToWeilHom (DominantCartierPullback.pullbackHom v A) C := by
  letI := D.genericPoint_isDiscreteValuationRing
  letI := C.genericPoint_isDiscreteValuationRing
  change cartierOrderAt S.toScheme _ D.genericPoint =
    cartierOrderAt V.toScheme _ C.genericPoint
  apply cartierOrderAt_pullback_eq_of_valuation_eq π v D.genericPoint C.genericPoint hcenter
  intro a
  simpa only [D.order_eq_stalkDivisorOrder, C.order_eq_stalkDivisorOrder] using horder a

/-- The actual Q-Cartier pullback coefficient depends only on its original valuation. -/
theorem coefficient_eq_of_valuation_eq (B : X.RationalWeilDivisor) (hB : X.QCartier B) :
    pullback π B hB D = pullback v B hB C := by
  obtain ⟨n, hn, A, hA⟩ := (X.qCartier_iff_exists_positive_multiple B).mp hB
  have hπ := pullbackToWeil_eq_of_positive_multiple π ⟨B, hB⟩ n hn A hA
  have hv := pullbackToWeil_eq_of_positive_multiple v ⟨B, hB⟩ n hn A hA
  change pullbackToWeil π ⟨B, hB⟩ D = pullbackToWeil v ⟨B, hB⟩ C
  rw [hπ, hv]
  change (n : ℚ)⁻¹ * (S.cartierToWeilHom
      (DominantCartierPullback.pullbackHom π A) D : ℚ) =
    (n : ℚ)⁻¹ * (V.cartierToWeilHom
      (DominantCartierPullback.pullbackHom v A) C : ℚ)
  rw [cartier_coefficient_eq_of_valuation_eq π v D C hcenter horder A]

end KltDP.Geometry.QCartierPullback

#check @KltDP.Geometry.QCartierPullback.coefficient_eq_of_valuation_eq
#print axioms KltDP.Geometry.QCartierPullback.coefficient_eq_of_valuation_eq
