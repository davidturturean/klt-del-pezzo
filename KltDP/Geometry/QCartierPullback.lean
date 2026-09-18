import KltDP.Geometry.RationalCartierLocalization
import KltDP.Geometry.DominantCartierPullbackFunctorial

/-!
Pullback on the existing rational Cartier submodules is the localization
of the proved original signed Cartier pullback. Its value on every
positive Cartier numerator is derived from linearity, so the expression
is independent of the denominator and numerator chosen to represent the
original rational Weil divisor. Original target and source divisors are
retained throughout.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QCartierPullback

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : NormalProjectiveSurface k}
variable (π : X.toScheme ⟶ Y.toScheme) [GenericPointPreserving π]

/-- Rational pullback is the localization of the original signed map,
between the existing rational Cartier submodules. -/
def pullbackLinearMap : Y.rationalCartierSubmodule →ₗ[ℚ] X.rationalCartierSubmodule :=
  IsLocalizedModule.mapExtendScalars (nonZeroDivisors ℤ)
    Y.rationalCartierMap X.rationalCartierMap ℚ
    (DominantCartierPullback.pullbackHom π).toIntLinearMap

/-- Localization preserves the original integral Cartier numerator. -/
@[simp]
theorem pullbackLinearMap_cartier (A : CartierDivisor Y.toScheme) :
    pullbackLinearMap π (Y.rationalCartierMap A) =
      X.rationalCartierMap (DominantCartierPullback.pullbackHom π A) :=
  IsLocalizedModule.map_apply (nonZeroDivisors ℤ)
    Y.rationalCartierMap X.rationalCartierMap
    (DominantCartierPullback.pullbackHom π).toIntLinearMap A

/-- The same map with values in the original rational Weil divisor group. -/
def pullbackToWeil : Y.rationalCartierSubmodule →ₗ[ℚ] X.RationalWeilDivisor :=
  X.rationalCartierSubmodule.subtype.comp (pullbackLinearMap π)

@[simp]
theorem pullbackToWeil_cartier (A : CartierDivisor Y.toScheme) :
    pullbackToWeil π (Y.rationalCartierMap A) =
      X.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π A) :=
  congrArg Subtype.val (pullbackLinearMap_cartier π A)

/-- Any positive denominator and actual Cartier numerator compute the
same rational pullback. -/
theorem pullbackToWeil_eq_of_positive_multiple (D : Y.rationalCartierSubmodule)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor Y.toScheme)
    (hA : Y.rationalCartierToWeilHom A = n • (D : Y.RationalWeilDivisor)) :
    pullbackToWeil π D =
      (n : ℚ)⁻¹ • X.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π A) := by
  have hnum : Y.rationalCartierMap A = n • D := Subtype.ext hA
  have h := congrArg (pullbackToWeil π) hnum
  rw [pullbackToWeil_cartier, map_nsmul] at h
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hscaled := congrArg (fun E : X.RationalWeilDivisor => (n : ℚ)⁻¹ • E) h
  simpa only [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hnq, one_smul]
    using hscaled.symm

/-- Pullback of an original Q-Cartier rational Weil divisor. Its proof
of membership selects no denominator or alternate divisor representation. -/
def pullback (D : Y.RationalWeilDivisor) (hD : Y.QCartier D) : X.RationalWeilDivisor :=
  pullbackToWeil π ⟨D, hD⟩

/-- The resulting original rational Weil divisor is Q-Cartier. -/
theorem pullback_qCartier (D : Y.RationalWeilDivisor) (hD : Y.QCartier D) :
    X.QCartier (pullback π D hD) :=
  (pullbackLinearMap π ⟨D, hD⟩).property

/-- Two actual Cartier numerators for the same original rational
divisor give the same pulled divisor after clearing their denominators. -/
theorem denominator_independent (D : Y.RationalWeilDivisor) (hD : Y.QCartier D)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (A B : CartierDivisor Y.toScheme)
    (hA : Y.rationalCartierToWeilHom A = n • D)
    (hB : Y.rationalCartierToWeilHom B = m • D) :
    (n : ℚ)⁻¹ • X.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π A) =
      (m : ℚ)⁻¹ • X.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π B) :=
  (pullbackToWeil_eq_of_positive_multiple π ⟨D, hD⟩ n hn A hA).symm.trans
    (pullbackToWeil_eq_of_positive_multiple π ⟨D, hD⟩ m hm B hB)

end KltDP.Geometry.QCartierPullback
