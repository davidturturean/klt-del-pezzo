import KltDP.Geometry.QCartierPullback
import KltDP.Geometry.SelectedPrimeCurveCartierUnion
import KltDP.Geometry.DominantCartierPullbackEffective

/-!
# Actual prime multiplicities and finite expansion of rational pullback

Each prime is represented by its original Cartier--Weil inverse image.
The actual rational pullback is expanded on the original finite support;
the unweighted total is the pullback of the actual reduced prime sum.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u

namespace KltDP.Geometry.QCartierPullback

open NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The original Cartier representative of one actual prime with coefficient one. -/
def primeCartierRepresentative (Y : NormalProjectiveSurface k)
    [∀ y : Y.toScheme, UniqueFactorizationMonoid (Y.stalk y)]
    (C : Y.PrimeCurve) : CartierDivisor Y.toScheme :=
  Y.cartierWeilEquiv.symm (Finsupp.single C 1)

section Target

variable (Y : NormalProjectiveSurface k)
    [∀ y : Y.toScheme, UniqueFactorizationMonoid (Y.stalk y)]

@[simp]
theorem primeCartierRepresentative_weil (C : Y.PrimeCurve) :
    Y.cartierToWeilHom (primeCartierRepresentative Y C) = Finsupp.single C 1 :=
  Y.cartierWeilEquiv.apply_symm_apply (Finsupp.single C 1)

@[simp]
theorem primeCartierRepresentative_rationalWeil (C : Y.PrimeCurve) :
    Y.rationalCartierToWeilHom (primeCartierRepresentative Y C) =
      Finsupp.single C 1 := by
  change rationalizeWeilDivisor Y
    (Y.cartierToWeilHom (primeCartierRepresentative Y C)) = _
  rw [primeCartierRepresentative_weil, rationalizeWeilDivisor_single, Int.cast_one]

/-- The literal selected Cartier divisor is the sum of its original prime representatives. -/
theorem selectedPrimeCartier_eq_sum_representatives (s : Finset Y.PrimeCurve) :
    Y.selectedPrimeCartier s = ∑ C ∈ s, primeCartierRepresentative Y C := by
  classical
  change Y.cartierWeilEquiv.symm (∑ C ∈ s, Finsupp.single C 1) = _
  simp only [map_sum, primeCartierRepresentative]

/-- The existing rational Cartier submodule retains the actual finite prime expansion. -/
theorem rationalCartier_eq_sum_primes (B : Y.rationalCartierSubmodule) :
    B = ∑ C ∈ (B : Y.RationalWeilDivisor).support,
      (B : Y.RationalWeilDivisor) C • Y.rationalCartierMap (primeCartierRepresentative Y C) := by
  classical
  apply Subtype.ext
  change (B : Y.RationalWeilDivisor) = Y.rationalCartierSubmodule.subtype
    (∑ C ∈ (B : Y.RationalWeilDivisor).support,
      (B : Y.RationalWeilDivisor) C • Y.rationalCartierMap (primeCartierRepresentative Y C))
  rw [map_sum]
  simp only [map_smul]
  change (B : Y.RationalWeilDivisor) = ∑ C ∈ (B : Y.RationalWeilDivisor).support,
    (B : Y.RationalWeilDivisor) C • Y.rationalCartierToWeilHom (primeCartierRepresentative Y C)
  simp only [primeCartierRepresentative_rationalWeil, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact (divisor_sum_single (B : Y.RationalWeilDivisor)).symm

end Target

variable {X Y : NormalProjectiveSurface k}
    [∀ y : Y.toScheme, UniqueFactorizationMonoid (Y.stalk y)]
    (π : X.toScheme ⟶ Y.toScheme) [GenericPointPreserving π]

/-- The actual integral multiplicity at an original source prime. -/
def primeMultiplicity (E : X.PrimeCurve) (C : Y.PrimeCurve) : ℤ :=
  X.cartierToWeilHom
    (DominantCartierPullback.pullbackHom π (primeCartierRepresentative Y C)) E

/-- Actual singleton effectivity and original regular equations imply nonnegative multiplicity. -/
theorem primeMultiplicity_nonneg (E : X.PrimeCurve) (C : Y.PrimeCurve) :
    0 ≤ primeMultiplicity π E C := by
  classical
  have hC : EffectiveDivisor (Finsupp.single C (1 : ℤ)) := by
    intro F
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  exact DominantCartierPullback.pullbackHom_effective_of_regularEquations π
    (primeCartierRepresentative Y C)
    (Y.hasRegularCartierEquations_cartierWeilEquiv_symm (Finsupp.single C 1) hC) E

/-- The unweighted actual multiplicities sum to the actual reduced-support coefficient. -/
theorem sum_primeMultiplicity (E : X.PrimeCurve) (s : Finset Y.PrimeCurve) :
    (∑ C ∈ s, primeMultiplicity π E C) =
      X.cartierToWeilHom (DominantCartierPullback.pullbackHom π (Y.selectedPrimeCartier s)) E := by
  classical
  have h := congrArg (fun A : CartierDivisor Y.toScheme =>
    X.cartierToWeilHom (DominantCartierPullback.pullbackHom π A) E)
    (selectedPrimeCartier_eq_sum_representatives Y s)
  simpa only [map_sum, Finsupp.finset_sum_apply, primeMultiplicity] using h.symm

@[simp]
theorem pullbackToWeil_prime_apply (E : X.PrimeCurve) (C : Y.PrimeCurve) :
    pullbackToWeil π (Y.rationalCartierMap (primeCartierRepresentative Y C)) E =
      (primeMultiplicity π E C : ℚ) := by
  rw [pullbackToWeil_cartier]
  rfl

/-- The existing rational pullback uses the original weights and actual prime multiplicities. -/
theorem pullbackToWeil_apply_eq_sum (B : Y.rationalCartierSubmodule) (E : X.PrimeCurve) :
    pullbackToWeil π B E = ∑ C ∈ (B : Y.RationalWeilDivisor).support,
      (B : Y.RationalWeilDivisor) C * (primeMultiplicity π E C : ℚ) := by
  classical
  have h := congrArg (fun A : Y.rationalCartierSubmodule => pullbackToWeil π A E)
    (rationalCartier_eq_sum_primes Y B)
  simpa only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply,
    smul_eq_mul, pullbackToWeil_prime_apply] using h

/-- The same finite formula for an original rational divisor with its Q-Cartier membership. -/
theorem pullback_apply_eq_sum (B : Y.RationalWeilDivisor) (hB : Y.QCartier B)
    (E : X.PrimeCurve) :
    pullback π B hB E = ∑ C ∈ B.support, B C * (primeMultiplicity π E C : ℚ) :=
  pullbackToWeil_apply_eq_sum π ⟨B, hB⟩ E

end KltDP.Geometry.QCartierPullback
