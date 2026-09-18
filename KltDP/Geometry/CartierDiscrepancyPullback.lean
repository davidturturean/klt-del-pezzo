import KltDP.Geometry.QCartierPullbackFunctorial
import Mathlib.Tactic.Abel

/-!
# The actual discrepancy divisor under a Cartier pullback plus correction

The formula takes place in the existing rational Weil divisor groups and
uses the original composite morphism. It is algebraic: the canonical and
exceptional interpretation of the Cartier divisors is supplied separately.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.CartierDiscrepancyPullback

open QCartierPullback

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S Y X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ Y.toScheme) (f : Y.toScheme ⟶ X.toScheme)
  [GenericPointPreserving π] [GenericPointPreserving f]

/-- The original composed discrepancy is the pulled original discrepancy
plus the actual Cartier correction. No coefficient formula is assumed. -/
theorem pullback_add_formula (K : CartierDivisor Y.toScheme)
    (E : CartierDivisor S.toScheme) (B : X.RationalWeilDivisor) (hB : X.QCartier B) :
    S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π K + E) -
        pullback (π ≫ f) B hB =
      S.rationalCartierToWeilHom E +
        pullbackToWeil π (Y.rationalCartierMap K - pullbackLinearMap f ⟨B, hB⟩) := by
  rw [map_add, map_sub, pullbackToWeil_cartier, pullback_comp]
  change S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π K) +
      S.rationalCartierToWeilHom E - pullback π (pullback f B hB) _ =
    S.rationalCartierToWeilHom E +
      (S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π K) -
        pullback π (pullback f B hB) _)
  abel

end KltDP.Geometry.CartierDiscrepancyPullback

#check @KltDP.Geometry.CartierDiscrepancyPullback.pullback_add_formula
#print axioms KltDP.Geometry.CartierDiscrepancyPullback.pullback_add_formula
