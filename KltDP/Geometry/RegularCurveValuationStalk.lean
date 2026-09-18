import KltDP.Geometry.NormalStalkDVR
import KltDP.Geometry.RegularLocalDimensionTwo
import KltDP.Geometry.DivisorOrder

/-! The original stalks of an integral regular scheme of dimension at most
one are valuation rings. At the generic point the original stalk is a
field; at any other point the existing dimension bounds give a DVR. -/

noncomputable section
open AlgebraicGeometry TopologicalSpace
universe u

namespace KltDP.Geometry.RegularCurveValuationStalk

attribute [local instance] integralSchemeStalk_isDomain

/-- No valuation structure or local-dimension premise is supplied. -/
theorem valuationRing (X : Scheme.{u}) [IsIntegral X]
    (hregular : ∀ x : X, RegularPoint X x)
    (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    ValuationRing (X.presheaf.stalk x) := by
  by_cases hx : x = genericPoint X
  · subst x
    exact inferInstance
  · have hd : ringKrullDim (X.presheaf.stalk x) = 1 :=
      le_antisymm ((ringKrullDim_stalk_le_topologicalKrullDim X x).trans hdim)
        (one_le_ringKrullDim_stalk_of_ne_genericPoint X x hx)
    letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      isDiscreteValuationRing_of_regularLocal_of_ringKrullDim_eq_one
        (X.presheaf.stalk x) (hregular x) hd
    infer_instance

end KltDP.Geometry.RegularCurveValuationStalk
