import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Surjective stalk restriction through an original closed immersion

This isolates the stalk-composition argument with arbitrary schemes and maps.
A supplied commuting square and an actual ambient stalk isomorphism force
surjectivity of the original restricted map. The geometric caller derives
both inputs for the actual corresponding prime curves.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- Stalk surjectivity descends through the original closed-immersion square. -/
theorem stalkMap_surjective_of_closedImmersion_square
    {A B S T : Scheme.{u}} (i : A ⟶ S) [IsClosedImmersion i]
    (j : B ⟶ T) (f : S ⟶ T) (g : A ⟶ B)
    (h : g ≫ j = i ≫ f) (a : A) [IsIso (f.stalkMap (i.base a))] :
    Function.Surjective (g.stalkMap a).hom := by
  have hs : Function.Surjective ((i ≫ f).stalkMap a).hom := by
    rw [Scheme.stalkMap_comp]
    exact (i.stalkMap_surjective a).comp
      (asIso (f.stalkMap (i.base a))).commRingCatIsoToRingEquiv.surjective
  have ht : Function.Surjective ((g ≫ j).stalkMap a).hom := by
    rw [h]
    exact hs
  rw [Scheme.stalkMap_comp] at ht
  exact Function.Surjective.of_comp ht

end KltDP.Geometry

#check @KltDP.Geometry.stalkMap_surjective_of_closedImmersion_square
#print axioms KltDP.Geometry.stalkMap_surjective_of_closedImmersion_square
