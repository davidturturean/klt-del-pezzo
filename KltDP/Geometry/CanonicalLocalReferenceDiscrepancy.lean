import KltDP.Geometry.CanonicalLocalReferencePullbackOrder
import KltDP.Geometry.QCartierPullback

/-!
# The original rational discrepancy on a compatible local reference

Clear any actual positive Cartier numerator. Its local equality and the
original pullback/order square identify the coefficient of the original
rational Weil difference with the integer local canonical difference.
No fixed Cartier index or replacement rational divisor is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalLocalReferenceDiscrepancy

open NormalModelCanonical NormalProjectiveSurface DominantCartierPullback
open CanonicalLocalReferencePullbackOrder OpenImmersionRational

attribute [local instance] integralSchemeStalk_isDomain

local instance discrepancyIntegralOpen {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (W : X.toScheme.Opens) [Nonempty W.toScheme] :
    IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι

local instance discrepancyPrimeDVR {k : Type u} [Field k]
    (S : NormalProjectiveSurface k) (C : S.PrimeCurve) :
    IsDiscreteValuationRing (S.toScheme.presheaf.stalk C.genericPoint) :=
  C.genericPoint_isDiscreteValuationRing

/-- The actual rational Weil coefficient is the original integer difference
on the derived reference neighborhood, for every actual Cartier numerator. -/
theorem coefficient_eq_local_difference
    {k : Type u} [Field k] [IsAlgClosed k] (S X : NormalProjectiveSurface k)
    (π : S.toScheme ⟶ X.toScheme) [GenericPointPreserving π]
    (C : S.PrimeCurve) (G : LocalFrame (π ≫ X.structureMorphism) C.genericPoint)
    (W : X.toScheme.Opens) [Nonempty W.toScheme]
    (p : G.neighborhood ⟶ W.toScheme) (hp : p ≫ W.ι = G.toModel ≫ π)
    (KW : CartierDivisor W.toScheme) (KS : CartierDivisor S.toScheme)
    (hG : G.order = S.cartierToWeilHom KS C)
    (KX : X.WeilDivisor) (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.cartierToWeilHom A = n • KX)
    (hmultiple : n • KW = cartierRestrictionHom W.ι A) :
    letI := C.genericPoint_isDiscreteValuationRing
    letI := referenceMap_genericPointPreserving S X π C G W p hp
    (S.rationalCartierToWeilHom KS -
        QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK) C =
      ((G.order - cartierOrderAt G.neighborhood (pullbackHom p KW) G.point : ℤ) : ℚ) := by
  letI := C.genericPoint_isDiscreteValuationRing
  letI := referenceMap_genericPointPreserving S X π C G W p hp
  have hAr : X.rationalCartierToWeilHom A = n • rationalizeWeilDivisor X KX :=
    (congrArg (rationalizeWeilDivisor X) hA).trans
      ((rationalizeWeilDivisor X).map_nsmul KX n)
  have hnum := QCartierPullback.pullbackToWeil_eq_of_positive_multiple π
    ⟨rationalizeWeilDivisor X KX, hK⟩ n hn A hAr
  have hord := multiple_pullback_order S X π C G W p hp KW n A hmultiple
  have hcast : (S.cartierToWeilHom (pullbackHom π A) C : ℚ) =
      (n : ℚ) * (cartierOrderAt G.neighborhood (pullbackHom p KW) G.point : ℚ) := by
    simpa only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℚ)) hord.symm
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  change (S.cartierToWeilHom KS C : ℚ) -
    QCartierPullback.pullbackToWeil π ⟨rationalizeWeilDivisor X KX, hK⟩ C = _
  rw [hnum]
  change (S.cartierToWeilHom KS C : ℚ) -
    (n : ℚ)⁻¹ * (S.cartierToWeilHom (pullbackHom π A) C : ℚ) = _
  rw [← hG, hcast, ← mul_assoc, inv_mul_cancel₀ hnq, one_mul, Int.cast_sub]

end KltDP.Geometry.CanonicalLocalReferenceDiscrepancy

#check @KltDP.Geometry.CanonicalLocalReferenceDiscrepancy.coefficient_eq_local_difference
#print axioms KltDP.Geometry.CanonicalLocalReferenceDiscrepancy.coefficient_eq_local_difference
