import KltDP.Geometry.BirationalCartierPullbackPushforward
import KltDP.Geometry.BirationalRationalWeilPushforward
import KltDP.Geometry.QCartierPullback

/-!
# Original Q-Cartier pullback followed by birational pushforward

The positive original Cartier numerator computes the existing Q-Cartier
pullback. Rational linearity and the proved integral Cartier comparison
recover that same numerator on the target; cancellation of its positive
denominator gives equality of the original rational Weil divisors.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QCartierPullback

open BirationalWeilPushforward BirationalPrimeCorrespondence

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- Original coefficient rationalization preserves the proved signed
Cartier pullback and pushforward identity. -/
theorem rationalPushforward_cartier_pullback (A : CartierDivisor X.toScheme) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    rationalPushforward π hbir
        (S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π A)) =
      X.rationalCartierToWeilHom A := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  exact (rationalPushforward_rationalize π hbir
    (S.cartierToWeilHom (DominantCartierPullback.pullbackHom π A))).trans
      (congrArg (NormalProjectiveSurface.rationalizeWeilDivisor X) (pushforward_cartier_pullback π hbir A))

/-- The original rational Cartier submodule pullback is a section of
the actual rational Weil pushforward. -/
theorem pushforward_pullbackToWeil (D : X.rationalCartierSubmodule) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    rationalPushforward π hbir (pullbackToWeil π D) = (D : X.RationalWeilDivisor) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  obtain ⟨n, hn, A, hA⟩ :=
    (X.qCartier_iff_exists_positive_multiple (D : X.RationalWeilDivisor)).mp D.property
  have hnum : X.rationalCartierToWeilHom A = n • (D : X.RationalWeilDivisor) := hA
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  calc
    rationalPushforward π hbir (pullbackToWeil π D) =
        rationalPushforward π hbir ((n : ℚ)⁻¹ •
          S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π A)) :=
      congrArg (rationalPushforward π hbir)
        (pullbackToWeil_eq_of_positive_multiple π D n hn A hnum)
    _ = (n : ℚ)⁻¹ • rationalPushforward π hbir
        (S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π A)) :=
      (rationalPushforward π hbir).map_smul _ _
    _ = (n : ℚ)⁻¹ • X.rationalCartierToWeilHom A :=
      congrArg (fun E : X.RationalWeilDivisor => (n : ℚ)⁻¹ • E)
        (rationalPushforward_cartier_pullback π hbir A)
    _ = (n : ℚ)⁻¹ • (n • (D : X.RationalWeilDivisor)) :=
      congrArg (fun E : X.RationalWeilDivisor => (n : ℚ)⁻¹ • E) hnum
    _ = (D : X.RationalWeilDivisor) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hnq, one_smul]

/-- Birational pushforward recovers the original Q-Cartier divisor
after its actual pullback. This is an equality of actual finite rational sums. -/
theorem pushforward_pullback (D : X.RationalWeilDivisor) (hD : X.QCartier D) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    rationalPushforward π hbir (pullback π D hD) = D := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  exact pushforward_pullbackToWeil π hbir ⟨D, hD⟩

/-- Every original nonexceptional prime coefficient is unchanged by
the actual Q-Cartier pullback. -/
theorem pullback_coefficient_above (D : X.RationalWeilDivisor) (hD : X.QCartier D)
    (C : X.PrimeCurve) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    pullback π D hD (abovePrimeCurve π hbir C) = D C := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  exact congrArg (fun E : X.RationalWeilDivisor => E C)
    (pushforward_pullback π hbir D hD)

end KltDP.Geometry.QCartierPullback
