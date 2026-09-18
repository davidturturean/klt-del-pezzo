import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Smooth structure morphisms on an isomorphism open

The original source structure morphism restricts to the preimage of the target
open. The actual restricted isomorphism then transports relative smoothness to
the target structure morphism, using the original commuting triangle.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace KltDP.Geometry.SmoothStructureOnIsomorphismOpen

/-- Relative smoothness descends through an actual isomorphism over a target open. -/
theorem isSmoothOfRelativeDimension {S X Y : Scheme.{u}} (n : ℕ)
    (f : X ⟶ S) (σ : Y ⟶ S) (π : X ⟶ Y) (hπ : π ≫ σ = f)
    [IsSmoothOfRelativeDimension n f] (U : Y.Opens) [IsIso (π ∣_ U)] :
    IsSmoothOfRelativeDimension n (U.ι ≫ σ) := by
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := @IsSmoothOfRelativeDimension n) (π ∣_ U) (U.ι ≫ σ)).mp
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hπ]
  exact IsLocalAtSource.comp (P := @IsSmoothOfRelativeDimension n)
    (inferInstance : IsSmoothOfRelativeDimension n f) (π ⁻¹ᵁ U).ι

end KltDP.Geometry.SmoothStructureOnIsomorphismOpen
