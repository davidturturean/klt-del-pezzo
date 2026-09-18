import KltDP.Geometry.QCartierPullbackPrimeExpansion
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Actual pullback controlled by a larger reduced Cartier support

A rational boundary can omit components of the original reduced divisor.
Nonnegative actual prime multiplicities control its total and retain
support inclusion after the original pullback, even with negative weights.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u

namespace KltDP.Geometry.QCartierPullback

open NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A Cartier divisor with actual coefficients zero or one is its literal selected prime sum. -/
theorem cartier_eq_selectedPrimeCartier (Y : NormalProjectiveSurface k)
    [∀ y : Y.toScheme, UniqueFactorizationMonoid (Y.stalk y)]
    (D : CartierDivisor Y.toScheme)
    (hD : ∀ C, Y.cartierToWeilHom D C = 0 ∨ Y.cartierToWeilHom D C = 1) :
    D = Y.selectedPrimeCartier (Y.cartierToWeilHom D).support := by
  classical
  apply Y.cartierWeilEquiv.injective
  change Y.cartierToWeilHom D =
    Y.cartierToWeilHom (Y.selectedPrimeCartier (Y.cartierToWeilHom D).support)
  rw [Y.selectedPrimeCartier_weil]
  ext C
  rw [Y.selectedPrimeWeil_apply]
  by_cases hC : Y.cartierToWeilHom D C = 0
  · rw [if_neg (by simpa only [Finsupp.mem_support_iff] using not_not_intro hC)]
    exact hC
  · rw [if_pos (Finsupp.mem_support_iff.mpr hC)]
    exact (hD C).resolve_left hC

variable {X Y : NormalProjectiveSurface k}
    [∀ y : Y.toScheme, UniqueFactorizationMonoid (Y.stalk y)]
    (π : X.toScheme ⟶ Y.toScheme) [GenericPointPreserving π]

/-- Sum only the boundary's actual multiplicities inside the larger original reduced divisor. -/
theorem sum_primeMultiplicity_le_pullback_coefficient
    (E : X.PrimeCurve) (s : Finset Y.PrimeCurve) (D : CartierDivisor Y.toScheme)
    (hD : ∀ C, Y.cartierToWeilHom D C = 0 ∨ Y.cartierToWeilHom D C = 1)
    (hs : s ⊆ (Y.cartierToWeilHom D).support) :
    (∑ C ∈ s, primeMultiplicity π E C) ≤
      X.cartierToWeilHom (DominantCartierPullback.pullbackHom π D) E := by
  classical
  calc
    (∑ C ∈ s, primeMultiplicity π E C) ≤
        ∑ C ∈ (Y.cartierToWeilHom D).support, primeMultiplicity π E C :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun C _ _ => primeMultiplicity_nonneg π E C)
    _ = X.cartierToWeilHom (DominantCartierPullback.pullbackHom π
        (Y.selectedPrimeCartier (Y.cartierToWeilHom D).support)) E :=
      sum_primeMultiplicity π E _
    _ = X.cartierToWeilHom (DominantCartierPullback.pullbackHom π D) E :=
      congrArg (fun A : CartierDivisor Y.toScheme =>
        X.cartierToWeilHom (DominantCartierPullback.pullbackHom π A) E)
        (cartier_eq_selectedPrimeCartier Y D hD).symm

/-- The original weighted pullback cannot acquire a component outside the
pullback of the larger original reduced Cartier divisor. -/
theorem pullback_support_subset
    (B : Y.RationalWeilDivisor) (hB : Y.QCartier B) (D : CartierDivisor Y.toScheme)
    (hD : ∀ C, Y.cartierToWeilHom D C = 0 ∨ Y.cartierToWeilHom D C = 1)
    (hBD : B.support ⊆ (Y.cartierToWeilHom D).support) :
    (pullback π B hB).support ⊆
      (X.cartierToWeilHom (DominantCartierPullback.pullbackHom π D)).support := by
  classical
  intro E hE
  by_contra hnot
  have hDE : X.cartierToWeilHom (DominantCartierPullback.pullbackHom π D) E = 0 :=
    Finsupp.not_mem_support_iff.mp hnot
  have htotal : (∑ C ∈ B.support, primeMultiplicity π E C) ≤ 0 :=
    (sum_primeMultiplicity_le_pullback_coefficient π E B.support D hD hBD).trans_eq hDE
  have hzero : ∀ C ∈ B.support, primeMultiplicity π E C = 0 := by
    intro C hC
    have hle : primeMultiplicity π E C ≤ ∑ F ∈ B.support, primeMultiplicity π E F :=
      Finset.single_le_sum (fun F _ => primeMultiplicity_nonneg π E F) hC
    exact le_antisymm (hle.trans htotal) (primeMultiplicity_nonneg π E C)
  have hBE : pullback π B hB E = 0 := by
    rw [pullback_apply_eq_sum]
    apply Finset.sum_eq_zero
    intro C hC
    rw [hzero C hC, Int.cast_zero, mul_zero]
  exact (Finsupp.mem_support_iff.mp hE) hBE

end KltDP.Geometry.QCartierPullback
