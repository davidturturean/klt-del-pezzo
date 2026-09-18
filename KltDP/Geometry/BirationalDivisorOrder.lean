import KltDP.Geometry.StalkDivisorOrderPullback
import KltDP.Geometry.BirationalPrimeCorrespondence
import KltDP.Geometry.PrimeCurveOrder

/-!
# The actual orders along corresponding birational prime curves

The source prime and its isomorphic original stalk map are already proved.
This transports the original rational function, without choosing another
function-field equivalence or assuming any order compatibility.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalDivisorOrder

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- The unique original source prime has exactly the target prime's
order on the pullback of the original nonzero rational function. -/
theorem abovePrimeCurve_order (C : X.PrimeCurve) (f : X.toScheme.functionFieldˣ) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    (abovePrimeCurve π hbir C).order
        (Units.map (functionFieldMap π).hom.toMonoidHom f) = C.order f := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : IsDiscreteValuationRing
      (S.toScheme.presheaf.stalk (abovePrimeCurve π hbir C).genericPoint) :=
    (abovePrimeCurve π hbir C).genericPoint_isDiscreteValuationRing
  letI : IsDiscreteValuationRing (X.toScheme.presheaf.stalk C.genericPoint) :=
    C.genericPoint_isDiscreteValuationRing
  letI : IsIso (π.stalkMap (abovePrimeCurve π hbir C).genericPoint) :=
    abovePrimeCurve_stalkMap_isIso π hbir C
  exact stalkDivisorOrder_map_of_stalkMap_isIso π
    (abovePrimeCurve π hbir C).genericPoint C.genericPoint
    (abovePrimeCurve_map_genericPoint π hbir C) f

end KltDP.Geometry.BirationalDivisorOrder
