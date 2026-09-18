import KltDP.Geometry.CodimensionOneOpen
import KltDP.Geometry.ProperBirationalCodimensionOne

/-!
# Original valuation points under open immersions

The original stalk isomorphism transports both local dimension and the
valuation-ring property. The latter is the pinned Mathlib theorem
Function.Surjective.valuationRing applied to the actual stalk equivalence
and its inverse.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.OpenImmersionValuationPoint

attribute [local instance] integralSchemeStalk_isDomain

/-- The original point map preserves the original local dimension. -/
def mapPoint {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (x : CodimensionOnePoint Y) : CodimensionOnePoint X :=
  ⟨j.base x.val, (ringKrullDim_stalk_openImmersion j x.val).trans x.property⟩

/-- The original open-immersion stalk map and its inverse transport the
valuation property of the original local rings. -/
theorem stalk_valuationRing_iff {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    ValuationRing (X.presheaf.stalk (j.base y)) ↔
      ValuationRing (Y.presheaf.stalk y) := by
  let e := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  constructor
  · intro h
    letI := h
    exact Function.Surjective.valuationRing e.toRingHom e.surjective
  · intro h
    letI := h
    exact Function.Surjective.valuationRing e.symm.toRingHom e.symm.surjective

end KltDP.Geometry.OpenImmersionValuationPoint

#check @KltDP.Geometry.OpenImmersionValuationPoint.stalk_valuationRing_iff
#print axioms KltDP.Geometry.OpenImmersionValuationPoint.stalk_valuationRing_iff
