import KltDP.Geometry.ActualExceptionalPullback
import KltDP.Geometry.AmpleSelfIntersectionPositive
import KltDP.Geometry.SelectedPrimeCurveCartierUnion
import KltDP.Geometry.OriginalCartierRamificationHalfLinePicard

/-!
# The actual exceptional branch half-line is orthogonal to original pullbacks

The original exceptional-curve predicate gives degree zero for each actual
pulled line sheaf. The original selected Weil coefficients therefore make
the branch pairing zero. Its original tensor-square isomorphism then makes
the half-line pairing zero, by cancellation in the integer-valued pairing.
No cancellation in the integral Picard group is used.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped BigOperators
universe u

namespace KltDP.Geometry.OriginalQuadraticCanonicalIntersection

open OriginalCartierRamificationSmooth

local instance exceptionalHalfLineModules (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S X : NormalProjectiveSurface k)
  (π : S.toScheme ⟶ X.toScheme)
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
  (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
  (hselected : S.cartierToWeilHom E = S.selectedPrimeWeil N)
  (hN : ∀ C ∈ N, IsExceptionalCurve π C)

include hπ hselected hN

/-- The actual selected exceptional branch pairs to zero with every class
pulled back along the original surface morphism. -/
theorem selectedExceptional_branchPairing_zero (p : X.toScheme.Pic) :
    S.picardPairing hS (cartierPicardClass S.toScheme E)
      (schemePicardPullbackHom π p) = 0 := by
  classical
  obtain ⟨M, rfl⟩ := RationalTreePicard.toPic_surjective p
  rw [schemePicardPullbackHom_toPic,
    AmpleSelfIntersectionPositive.picardPairing_cartierClass_eq_weil_sum S hS,
    hselected]
  unfold Finsupp.sum
  rw [S.selectedPrimeWeil_support]
  apply Finset.sum_eq_zero
  intro C hC
  rw [S.selectedPrimeWeil_apply, if_pos hC]
  change (1 : ℤ) * C.restrictionDegree (pullbackInvertibleSheaf π M) = 0
  simpa only [one_mul] using (hN C hC).restrictionDegree_pullback_eq_zero π hπ C M

variable (L : InvertibleSheaf S.toScheme)
  (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E)

include e

/-- The original half-branch line has zero pairing with every original
pulled Picard class. Only the integer pairing is divided by two. -/
theorem selectedExceptional_halfLinePairing_zero (p : X.toScheme.Pic) :
    S.picardPairing hS L.toPic (schemePicardPullbackHom π p) = 0 := by
  have he : cartierPicardClass S.toScheme E = L.toPic * L.toPic := by
    have he' := congrArg Additive.toMul (original_branchPicard_eq_twice_line S E L e)
    simpa only [cartierPicardHom_apply, two_nsmul, toMul_add, toMul_ofMul] using he'
  have hz := selectedExceptional_branchPairing_zero S X π hπ hS N E hselected hN p
  rw [he, S.picardPairing_mul_left_of_regular] at hz
  omega

end KltDP.Geometry.OriginalQuadraticCanonicalIntersection

#print axioms KltDP.Geometry.OriginalQuadraticCanonicalIntersection.selectedExceptional_branchPairing_zero
#print axioms KltDP.Geometry.OriginalQuadraticCanonicalIntersection.selectedExceptional_halfLinePairing_zero
