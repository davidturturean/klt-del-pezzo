import KltDP.Geometry.DivisorOrderFieldTransport
import KltDP.Geometry.FunctionFieldStalkMap

/-!
# Order transport through an original isomorphic stalk map

The DVR equivalence is the original stalk map. Its compatibility with
the original function-field map is proved by stalk naturality.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

attribute [local instance] integralSchemeStalk_isDomain

variable {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (π : S ⟶ X) [GenericPointPreserving π]

/-- At corresponding DVR points where the original stalk map is an
isomorphism, pullback by the original function-field map preserves order. -/
theorem stalkDivisorOrder_map_of_stalkMap_isIso (x : S) (y : X)
    (hxy : π.base x = y) [IsDiscreteValuationRing (S.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk y)] [IsIso (π.stalkMap x)]
    (f : X.functionFieldˣ) :
    stalkDivisorOrder S x (Units.map (functionFieldMap π).hom.toMonoidHom f) =
      stalkDivisorOrder X y f := by
  subst y
  exact RingTheory.divisorOrder_map_of_ringEquiv
    (asIso (π.stalkMap x)).commRingCatIsoToRingEquiv (functionFieldMap π).hom
    (fun r => (functionFieldMap_stalk_algebraMap π x r).symm) f

end KltDP.Geometry
