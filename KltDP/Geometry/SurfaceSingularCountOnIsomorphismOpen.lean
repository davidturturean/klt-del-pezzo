import KltDP.Geometry.SurfaceRegularityOnIsomorphismOpen
import Mathlib.Data.Set.Card

/-!
# Bounding the actual singular-point count by a finite isomorphism complement

The original singular-point inclusion and finite-set cardinality monotonicity
give the bound. No point in the complement is asserted to be singular.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RegularPointsOnIsomorphismOpen

/-- The number of actual singular surface points is at most the number of
points in the finite complement of the original isomorphism open. -/
theorem singularPoints_card_le_natCard_compl {k : Type u} [Field k] {X : Scheme.{u}}
    (Y : NormalProjectiveSurface k) (π : X ⟶ Y.toScheme) (U : Y.toScheme.Opens)
    [IsIso (π ∣_ U)] (hreg : ∀ x : X, RegularPoint X x)
    (hfinite : ((U : Set Y.Point)ᶜ).Finite) :
    Y.singularPoints.card ≤ Nat.card ↥((U : Set Y.Point)ᶜ) := by
  rw [Set.Nat.card_coe_set_eq, ← Set.ncard_coe_Finset Y.singularPoints]
  exact Set.ncard_le_ncard (singularPoints_subset_compl Y π U hreg) hfinite

end KltDP.Geometry.RegularPointsOnIsomorphismOpen
