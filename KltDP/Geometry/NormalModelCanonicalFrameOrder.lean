import KltDP.Geometry.NormalModelCanonicalFrame
import KltDP.Geometry.CartierOrderOpenRestriction

/-!
# The original local Cartier order of an actual canonical frame

The neighborhood stalk is a DVR by its original open-immersion stalk map.
The transported original equation therefore has the same order as the
actual Cartier divisor on the original neighborhood. No order or DVR
comparison is a field of the frame.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical.LocalFrame

attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] {V : Scheme.{u}} [IsIntegral V]
    {σ : V ⟶ Spec (CommRingCat.of k)} {x : V} (F : LocalFrame σ x)
    [IsDiscreteValuationRing (V.presheaf.stalk x)]

/-- The actual neighborhood stalk inherits the DVR structure from the
original model stalk through the original open immersion. -/
instance neighborhood_stalk_isDiscreteValuationRing :
    IsDiscreteValuationRing (F.neighborhood.presheaf.stalk F.point) :=
  OpenImmersionRational.stalk_isDiscreteValuationRing_of_isOpenImmersion
    F.toModel F.point x F.point_eq

/-- The frame order is the actual Cartier order at its original point. -/
theorem order_eq_cartierOrderAt :
    F.order = cartierOrderAt F.neighborhood F.divisor F.point := by
  let e := OpenImmersionRational.functionFieldIso F.toModel
  have hcancel : Units.map e.hom.hom.toMonoidHom F.equationOnModel =
      F.equationChart.equation := by
    apply Units.ext
    change e.hom (e.inv (F.equationChart.equation : F.neighborhood.functionField)) = _
    have h := ConcreteCategory.congr_hom e.inv_hom_id
      (F.equationChart.equation : F.neighborhood.functionField)
    change e.hom (e.inv (F.equationChart.equation : F.neighborhood.functionField)) =
      (F.equationChart.equation : F.neighborhood.functionField) at h
    exact h
  calc
    F.order = stalkDivisorOrder F.neighborhood F.point
        (Units.map e.hom.hom.toMonoidHom F.equationOnModel) :=
      (OpenImmersionRational.stalkDivisorOrder_functionFieldIso
        F.toModel F.point x F.point_eq F.equationOnModel).symm
    _ = stalkDivisorOrder F.neighborhood F.point F.equationChart.equation :=
      congrArg (stalkDivisorOrder F.neighborhood F.point) hcancel
    _ = cartierOrderAt F.neighborhood F.divisor F.point :=
      (cartierOrderAt_eq_of_equation F.neighborhood F.divisor F.point
        F.equationChart.openSet F.point_mem_equation F.equationChart.equation
        F.equationChart.represents).symm

end KltDP.Geometry.NormalModelCanonical.LocalFrame

#check @KltDP.Geometry.NormalModelCanonical.LocalFrame.order_eq_cartierOrderAt
#print axioms KltDP.Geometry.NormalModelCanonical.LocalFrame.order_eq_cartierOrderAt
