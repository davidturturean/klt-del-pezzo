import KltDP.Geometry.BirationalPrimeCurveMap
import KltDP.Geometry.BirationalOfGenericStalkSurjective
import KltDP.Geometry.ClosedImmersionStalkSurjectivityTransfer

/-!
# The original strict-transform restriction is birational

The ambient birational map is already proved to induce an isomorphism at
the original point above the target prime. Composing that original stalk
map with the source curve's surjective inclusion-stalk map is surjective.
The literal inclusion square then makes the restriction's generic-stalk
map surjective, hence an isomorphism between the original function fields.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.BirationalPrimeCurveMap

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
  (C : X.PrimeCurve)

theorem restriction_generic_stalkMap_surjective :
    Function.Surjective ((restriction π hbir C).stalkMap
      (_root_.genericPoint (abovePrimeCurve π hbir C).toScheme)).hom := by
  letI : IsIso (π.stalkMap ((abovePrimeCurve π hbir C).inclusion.base
      (_root_.genericPoint (abovePrimeCurve π hbir C).toScheme))) := by
    rw [NormalProjectiveSurface.PrimeCurve.inclusion_genericPoint_eq]
    exact abovePrimeCurve_stalkMap_isIso π hbir C
  exact stalkMap_surjective_of_closedImmersion_square
    (abovePrimeCurve π hbir C).inclusion C.inclusion π (restriction π hbir C)
    (restriction_inclusion π hbir C)
    (_root_.genericPoint (abovePrimeCurve π hbir C).toScheme)

/-- The actual corresponding prime curves have a birational restriction
map, with no whole-curve isomorphism or curve smoothness hypothesis. -/
theorem restriction_isBirationalScheme : IsBirationalScheme (restriction π hbir C) :=
  isBirationalScheme_of_generic_stalkMap_surjective (restriction π hbir C)
    (restriction_generic_stalkMap_surjective π hbir C)

end KltDP.Geometry.BirationalPrimeCurveMap

#check @KltDP.Geometry.BirationalPrimeCurveMap.restriction_isBirationalScheme
#print axioms KltDP.Geometry.BirationalPrimeCurveMap.restriction_isBirationalScheme
