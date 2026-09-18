import KltDP.Geometry.CartierDivisorPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Surjectivity of an original proper generic-point-preserving map

The original image is closed and contains the actual generic point of the
integral target, hence contains every target point. This applies directly
to the finite maps constructed from genus zero, without a birationality or
point-surjectivity assumption.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

theorem surjective_of_proper_genericPointPreserving
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (π : X ⟶ Y) [IsProper π] [hπ : GenericPointPreserving π] :
    Surjective π := by
  have hclosed : IsClosed (Set.range π.base) := by
    simpa only [Set.image_univ] using π.isClosedMap Set.univ isClosed_univ
  have hgeneric : genericPoint Y ∈ Set.range π.base :=
    ⟨genericPoint X, hπ.base_genericPoint⟩
  have hall : (Set.univ : Set Y) ⊆ Set.range π.base :=
    ((genericPoint_spec Y).mem_closed_set_iff hclosed).mp hgeneric
  exact ⟨fun y => hall (Set.mem_univ y)⟩

end KltDP.Geometry

#check @KltDP.Geometry.surjective_of_proper_genericPointPreserving
#print axioms KltDP.Geometry.surjective_of_proper_genericPointPreserving
