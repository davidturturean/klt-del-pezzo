import KltDP.Geometry.CartierDiscrepancyPullback
import KltDP.Geometry.CartierBoundarySupport
import KltDP.Geometry.QCartierPullbackSupportBound

/-!
# The actual discrepancy remains inside the reduced total boundary

The old discrepancy may vanish on some components of the SNC boundary.
The original rational pullback preserves support inclusion, and an effective
Cartier correction enlarges the containing reduced boundary without any
assumption that the discrepancy itself is effective.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.CartierDiscrepancyPullback

open QCartierPullback

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S Y X : NormalProjectiveSurface k}
  [∀ s : S.toScheme, UniqueFactorizationMonoid (S.stalk s)]
  [∀ y : Y.toScheme, UniqueFactorizationMonoid (Y.stalk y)]
  (π : S.toScheme ⟶ Y.toScheme) (f : Y.toScheme ⟶ X.toScheme)
  [GenericPointPreserving π] [GenericPointPreserving f]

theorem support_subset_reduced_total
    (K : CartierDivisor Y.toScheme) (E : CartierDivisor S.toScheme)
    (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (A : CartierDivisor Y.toScheme)
    (hA : HasRegularCartierEquations Y.toScheme A)
    (hE : HasRegularCartierEquations S.toScheme E)
    (hcoeff : ∀ C, Y.cartierToWeilHom A C = 0 ∨ Y.cartierToWeilHom A C = 1)
    (hsupport : (Y.rationalCartierToWeilHom K - pullback f B hB).support ⊆
      (Y.cartierToWeilHom A).support) :
    (S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π K + E) -
        pullback (π ≫ f) B hB).support ⊆
      (S.cartierToWeilHom (S.reducedSupportCartier
        (DominantCartierPullback.pullbackHom π A + E))).support := by
  rw [pullback_add_formula, S.reducedSupportCartier_finsupp_support]
  let Δ : Y.rationalCartierSubmodule :=
    Y.rationalCartierMap K - pullbackLinearMap f ⟨B, hB⟩
  apply S.rational_boundary_add_support_subset
    (pullbackToWeil π Δ) (DominantCartierPullback.pullbackHom π A) E
      (DominantCartierPullback.pullbackHom_effective_of_regularEquations π A hA)
      (S.effective_cartierToWeilHom_of_regularEquations E hE)
  exact pullback_support_subset π (Δ : Y.RationalWeilDivisor) Δ.property A hcoeff hsupport

end KltDP.Geometry.CartierDiscrepancyPullback

#check @KltDP.Geometry.CartierDiscrepancyPullback.support_subset_reduced_total
#print axioms KltDP.Geometry.CartierDiscrepancyPullback.support_subset_reduced_total
