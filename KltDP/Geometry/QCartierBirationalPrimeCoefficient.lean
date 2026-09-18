import KltDP.Geometry.QCartierPullback
import KltDP.Geometry.BirationalCartierPullbackPushforward

/-!
# Rational Cartier coefficients at the original corresponding prime

The original proper birational prime correspondence already preserves
integral Cartier orders. Clearing an actual positive Cartier denominator
gives the same statement for the existing rational pullback.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.QCartierPullback

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

theorem coefficient_above_prime (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (C : X.PrimeCurve) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    pullback π B hB (abovePrimeCurve π hbir C) = B C := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  obtain ⟨n, hn, A, hA⟩ := (X.qCartier_iff_exists_positive_multiple B).mp hB
  change pullbackToWeil π ⟨B, hB⟩ (abovePrimeCurve π hbir C) = B C
  rw [pullbackToWeil_eq_of_positive_multiple π ⟨B, hB⟩ n hn A hA]
  change (n : ℚ)⁻¹ *
    (S.cartierToWeilHom (DominantCartierPullback.pullbackHom π A)
      (abovePrimeCurve π hbir C) : ℚ) = B C
  rw [BirationalWeilPushforward.cartier_pullback_coefficient π hbir A C]
  have hC := congrArg (fun D : X.RationalWeilDivisor => D C) hA
  have hC' : (X.cartierToWeilHom A C : ℚ) = (n : ℚ) * B C := by
    simpa only [NormalProjectiveSurface.rationalizeWeilDivisor_apply,
      Finsupp.smul_apply, nsmul_eq_mul] using hC
  rw [hC', ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)), one_mul]

/-- No chosen correspondence witness is needed if the original prime
generic points have the stated image. -/
theorem coefficient_of_maps_to_prime (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (D : S.PrimeCurve) (C : X.PrimeCurve) (hD : π.base D.genericPoint = C.genericPoint) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    pullback π B hB D = B C := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  rw [abovePrimeCurve_unique π hbir C D hD]
  exact coefficient_above_prime π hbir B hB C

end KltDP.Geometry.QCartierPullback

#check @KltDP.Geometry.QCartierPullback.coefficient_of_maps_to_prime
#print axioms KltDP.Geometry.QCartierPullback.coefficient_of_maps_to_prime
