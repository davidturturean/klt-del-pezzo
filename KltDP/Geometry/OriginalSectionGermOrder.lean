import KltDP.Geometry.DivisorOrderPositiveLocalElement

/-!
# Original section germs and their actual divisor orders

These equations identify a section's original germ with its original
function-field value. They let a native maximal-ideal calculation apply
to the same rational unit already computed by the Cartier-frame formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.OriginalSectionGermOrder

attribute [local instance] integralSchemeStalk_isDomain

variable (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
    (x : X) (hx : x ∈ U) (a : Γ(X, U))

/-- The literal original section germ has its literal original field value. -/
theorem germ_field :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx a) =
      X.germToFunctionField U a :=
  ConcreteCategory.congr_hom
    (X.presheaf.germ_stalkSpecializes hx ((genericPoint_spec X).specializes trivial)) a

/-- An actual unit field value proves the original local section germ is nonzero. -/
theorem germ_ne_zero (r : X.functionFieldˣ)
    (hr : (r : X.functionField) = X.germToFunctionField U a) :
    X.presheaf.germ U x hx a ≠ 0 := by
  intro hzero
  apply r.ne_zero
  exact hr.trans ((germ_field X U x hx a).symm.trans (by rw [hzero, map_zero]))

/-- This identifies the exact fraction-field unit used by the original DVR
order with the exact unit computed from the original section. -/
theorem fractionFieldUnit_germ_eq
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (r : X.functionFieldˣ) (hr : (r : X.functionField) = X.germToFunctionField U a) :
    RingTheory.fractionFieldUnit (X.presheaf.stalk x) X.functionField
        (X.presheaf.germ U x hx a) (germ_ne_zero X U x hx a r hr) = r := by
  apply Units.ext
  exact (germ_field X U x hx a).trans hr.symm

/-- Native maximal-ideal membership proves positivity of the order of that
same original rational unit, with nonzeroness derived from its section value. -/
theorem order_pos_of_germ_mem_maximalIdeal
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (r : X.functionFieldˣ) (hr : (r : X.functionField) = X.germToFunctionField U a)
    (hm : X.presheaf.germ U x hx a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    0 < stalkDivisorOrder X x r := by
  rw [← fractionFieldUnit_germ_eq X U x hx a r hr]
  exact stalkDivisorOrder_algebraMap_pos_of_mem_maximalIdeal X x _
    (germ_ne_zero X U x hx a r hr) hm

end KltDP.Geometry.OriginalSectionGermOrder

#check @KltDP.Geometry.OriginalSectionGermOrder.fractionFieldUnit_germ_eq
#check @KltDP.Geometry.OriginalSectionGermOrder.order_pos_of_germ_mem_maximalIdeal
#print axioms KltDP.Geometry.OriginalSectionGermOrder.order_pos_of_germ_mem_maximalIdeal
