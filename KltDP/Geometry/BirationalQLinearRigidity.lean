import KltDP.Geometry.BirationalPrincipalRigidity
import KltDP.Geometry.BirationalRationalWeilPushforward
import KltDP.Geometry.CartierPicardEndpointRationalClasses

/-!
# Rational linear equivalence with equal original pushforward is equality

The accepted rational linear-equivalence criterion clears denominators
to one original source principal divisor. Rational linear pushforward
and injective coefficient rationalization make its integral pushforward
zero. Principal rigidity then makes that divisor zero, and cancellation
of the positive denominator proves equality of the actual rational sums.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalWeilPushforward

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- Rationally linearly equivalent actual source divisors with the same
original proper birational pushforward are equal as rational Weil divisors. -/
theorem eq_of_qLinearlyEquivalent_of_rationalPushforward_eq
    (D E : S.RationalWeilDivisor) (hlin : S.QLinearlyEquivalent D E)
    (hpush : rationalPushforward π hbir D = rationalPushforward π hbir E) : D = E := by
  obtain ⟨n, hn, f, hf⟩ :=
    (S.qLinearlyEquivalent_iff_positive_principal_multiple D E).mp hlin
  have hpushf : pushforward π hbir (S.principalDivisor f) = 0 := by
    apply NormalProjectiveSurface.rationalizeWeilDivisor_injective (X := X)
    calc
      NormalProjectiveSurface.rationalizeWeilDivisor X
          (pushforward π hbir (S.principalDivisor f)) =
        rationalPushforward π hbir
          (NormalProjectiveSurface.rationalizeWeilDivisor S (S.principalDivisor f)) :=
        (rationalPushforward_rationalize π hbir (S.principalDivisor f)).symm
      _ = rationalPushforward π hbir (n • (D - E)) :=
        congrArg (rationalPushforward π hbir) hf.symm
      _ = 0 := by rw [map_nsmul, map_sub, hpush, sub_self, nsmul_zero]
      _ = NormalProjectiveSurface.rationalizeWeilDivisor X 0 :=
        (NormalProjectiveSurface.rationalizeWeilDivisor X).map_zero.symm
  have hprincipal : S.principalDivisor f = 0 :=
    principalDivisor_eq_zero_of_pushforward_eq_zero π hbir f hpushf
  have hmultiple : n • (D - E) = 0 :=
    hf.trans ((congrArg (NormalProjectiveSurface.rationalizeWeilDivisor S) hprincipal).trans
      (NormalProjectiveSurface.rationalizeWeilDivisor S).map_zero)
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hscaled := congrArg (fun F : S.RationalWeilDivisor => (n : ℚ)⁻¹ • F) hmultiple
  apply sub_eq_zero.mp
  simpa only [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hnq,
    one_smul, smul_zero] using hscaled

end KltDP.Geometry.BirationalWeilPushforward
