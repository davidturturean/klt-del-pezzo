import KltDP.Geometry.CartierFrameSectionCoefficient
import KltDP.Geometry.DominantCartierPullbackEquations

/-!
# Cartier coefficient order from an original module-map value

Restriction and signed Cartier order are proved with abstract module objects.
The only value input concerns the actual map applied to the original target
Cartier frame; its coefficient and order are then derived from the existing
equation-section equivalence and the original signed pullback equations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.CartierMapCoefficientOrder

open CartierRationalCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] integralSchemeStalk_isDomain

/-- The actual rational value of a module coordinate is unchanged by
restriction between the original nonempty opens. -/
theorem coordinate_value_restrict (Y : Scheme.{u}) [IsIntegral Y]
    (M : Y.Modules) (c : M ⟶ rationalFunctionModule Y)
    (U V : Y.Opens) [Nonempty U] [Nonempty V] (h : V ≤ U)
    (t : M.val.obj (op U)) :
    rationalFunctionModuleSectionsEquiv Y V
        (c.val.app (op V) (M.val.map (homOfLE h).op t)) =
      rationalFunctionModuleSectionsEquiv Y U (c.val.app (op U) t) := by
  rw [_root_.PresheafOfModules.naturality_apply c.val (homOfLE h).op t,
    rationalFunctionModuleSectionsEquiv_naturality]

/-- An original section whose coordinate is the pulled inverse target
equation has the signed Cartier-difference order. -/
theorem coefficient_order_of_equation_value
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (q : Y ⟶ X) [GenericPointPreserving q]
    (DX : CartierDivisor X) (DY : CartierDivisor Y)
    (MY : Y.Modules) (eY : cartierDivisorModule Y DY ≅ MY)
    (cS : CartierEquationChart Y DY) (cT : CartierEquationChart X DX)
    (hST : cS.openSet ≤ q ⁻¹ᵁ cT.openSet)
    (t : MY.val.obj (op (q ⁻¹ᵁ cT.openSet)))
    (hvalue : rationalFunctionModuleSectionsEquiv Y (q ⁻¹ᵁ cT.openSet)
        ((coordinate Y DY MY eY).val.app (op (q ⁻¹ᵁ cT.openSet)) t) =
      functionFieldMap q ((cT.equation⁻¹ : X.functionFieldˣ) : X.functionField))
    (y : Y) [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    (hy : y ∈ cS.openSet) :
    let s := MY.val.map (homOfLE hST).op t
    let r := Units.map (functionFieldMap q).hom.toMonoidHom cT.equation⁻¹ * cS.equation
    (r : Y.functionField) = Y.germToFunctionField cS.openSet
        (sectionCoefficient Y DY MY eY cS s) ∧
      stalkDivisorOrder Y y r =
        cartierOrderAt Y DY y -
          cartierOrderAt Y (DominantCartierPullback.pullbackHom q DX) y := by
  let s := MY.val.map (homOfLE hST).op t
  let rT := Units.map (functionFieldMap q).hom.toMonoidHom cT.equation⁻¹
  have hrestricted : rationalFunctionModuleSectionsEquiv Y cS.openSet
      ((coordinate Y DY MY eY).val.app (op cS.openSet) s) =
        (rT : Y.functionField) :=
    (coordinate_value_restrict Y MY (coordinate Y DY MY eY)
      (q ⁻¹ᵁ cT.openSet) cS.openSet hST t).trans hvalue
  have hcoefficient := sectionCoefficient_order Y DY MY eY cS s rT
    hrestricted.symm y hy
  have hpull : cartierOrderAt Y (DominantCartierPullback.pullbackHom q DX) y =
      stalkDivisorOrder Y y
        (Units.map (functionFieldMap q).hom.toMonoidHom cT.equation) :=
    cartierOrderAt_eq_of_equation Y _ y (q ⁻¹ᵁ cT.openSet) (hST hy)
      (Units.map (functionFieldMap q).hom.toMonoidHom cT.equation)
      (DominantCartierPullback.pullbackHom_globalEquation_preimage q DX cT.openSet
        cT.equation cT.represents)
  have horder : stalkDivisorOrder Y y rT =
      -cartierOrderAt Y (DominantCartierPullback.pullbackHom q DX) y := by
    change stalkDivisorOrder Y y
      (Units.map (functionFieldMap q).hom.toMonoidHom cT.equation⁻¹) = _
    rw [map_inv, stalkDivisorOrder_inv, ← hpull]
  exact ⟨hcoefficient.1,
    hcoefficient.2.trans (by rw [horder, sub_eq_add_neg, add_comm])⟩

/-- For an actual map of pulled modules, its established field-value
equality on the original target frame determines the original coefficient
and signed Cartier order. No coefficient or Cartier compatibility is assumed. -/
theorem coefficient_order_of_frame_value
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (q : Y ⟶ X) [GenericPointPreserving q]
    (DX : CartierDivisor X) (DY : CartierDivisor Y)
    (MX : X.Modules) (MY : Y.Modules)
    (eX : cartierDivisorModule X DX ≅ MX)
    (eY : cartierDivisorModule Y DY ≅ MY)
    (a : (schemeModulePullback q).obj MX ⟶ MY)
    (cS : CartierEquationChart Y DY) (cT : CartierEquationChart X DX)
    (hST : cS.openSet ≤ q ⁻¹ᵁ cT.openSet)
    (hvalue : rationalFunctionModuleSectionsEquiv Y (q ⁻¹ᵁ cT.openSet)
        ((coordinate Y DY MY eY).val.app (op (q ⁻¹ᵁ cT.openSet))
          (a.val.app (op (q ⁻¹ᵁ cT.openSet))
            (pullbackSection q MX cT.openSet (frame X DX MX eX cT)))) =
      functionFieldMap q (rationalFunctionModuleSectionsEquiv X cT.openSet
        ((coordinate X DX MX eX).val.app (op cT.openSet) (frame X DX MX eX cT))))
    (y : Y) [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    (hy : y ∈ cS.openSet) :
    let t := a.val.app (op (q ⁻¹ᵁ cT.openSet))
      (pullbackSection q MX cT.openSet (frame X DX MX eX cT))
    let s := MY.val.map (homOfLE hST).op t
    let r := Units.map (functionFieldMap q).hom.toMonoidHom cT.equation⁻¹ * cS.equation
    (r : Y.functionField) = Y.germToFunctionField cS.openSet
        (sectionCoefficient Y DY MY eY cS s) ∧
      stalkDivisorOrder Y y r =
        cartierOrderAt Y DY y -
          cartierOrderAt Y (DominantCartierPullback.pullbackHom q DX) y := by
  exact coefficient_order_of_equation_value q DX DY MY eY cS cT hST
    (a.val.app (op (q ⁻¹ᵁ cT.openSet))
      (pullbackSection q MX cT.openSet (frame X DX MX eX cT)))
    (hvalue.trans (congrArg (fun z : X.functionField => functionFieldMap q z)
      (coordinate_frame_value X DX MX eX cT))) y hy

end KltDP.Geometry.CartierMapCoefficientOrder

#check @KltDP.Geometry.CartierMapCoefficientOrder.coefficient_order_of_frame_value
#print axioms KltDP.Geometry.CartierMapCoefficientOrder.coefficient_order_of_frame_value
