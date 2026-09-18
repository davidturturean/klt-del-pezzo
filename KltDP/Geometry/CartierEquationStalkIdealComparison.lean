import KltDP.Geometry.StalkCurveUnit
import KltDP.Geometry.EffectiveCartierIdeal
import KltDP.Geometry.CartierWeilMap

/-!
# Original Cartier equation ideals with equal local curve coefficients

Equality of the actual Cartier-to-Weil coefficients on every curve through
a point makes the two original coefficient germs differ by an actual stalk
unit. Their generated ideals are therefore equal. The unit is derived
from the original curve-order comparison, not given as an extra premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- Equal actual local Weil coefficients give equality of the original
principal stalk ideals of any two original regular Cartier equations. -/
theorem regularCartierEquation_span_germ_eq_of_curveCoefficients
    (E F : CartierDivisor X.toScheme)
    (c : RegularCartierEquationChart X.toScheme E)
    (d : RegularCartierEquationChart X.toScheme F)
    (x : X.toScheme) (hxc : x ∈ c.chart.openSet) (hxd : x ∈ d.chart.openSet)
    [UniqueFactorizationMonoid (X.stalk x)]
    (hcoeff : ∀ C : X.PrimeCurve, x ∈ C → X.cartierToWeilHom E C = X.cartierToWeilHom F C) :
    Ideal.span ({X.toScheme.presheaf.germ c.chart.openSet x hxc c.coefficient} : Set (X.stalk x)) =
      Ideal.span ({X.toScheme.presheaf.germ d.chart.openSet x hxd d.coefficient} : Set (X.stalk x)) := by
  let a : X.stalk x := X.toScheme.presheaf.germ c.chart.openSet x hxc c.coefficient
  let b : X.stalk x := X.toScheme.presheaf.germ d.chart.openSet x hxd d.coefficient
  have ha : algebraMap (X.stalk x) X.toScheme.functionField a =
      (c.chart.equation : X.toScheme.functionField) :=
    (ConcreteCategory.congr_hom (X.toScheme.presheaf.germ_stalkSpecializes hxc
      ((genericPoint_spec X.toScheme).specializes trivial)) c.coefficient).trans c.germ_eq
  have hb : algebraMap (X.stalk x) X.toScheme.functionField b =
      (d.chart.equation : X.toScheme.functionField) :=
    (ConcreteCategory.congr_hom (X.toScheme.presheaf.germ_stalkSpecializes hxd
      ((genericPoint_spec X.toScheme).specializes trivial)) d.coefficient).trans d.germ_eq
  have horders (C : X.PrimeCurve) (hxC : x ∈ C) : C.order c.chart.equation = C.order d.chart.equation :=
    (X.cartierToWeilHom_apply_of_equation E C c.chart.openSet
      (C.genericPoint_mem_of_mem ⟨x, hxc⟩ hxC) c.chart.equation c.chart.represents).symm.trans
      ((hcoeff C hxC).trans (X.cartierToWeilHom_apply_of_equation F C d.chart.openSet
        (C.genericPoint_mem_of_mem ⟨x, hxd⟩ hxC) d.chart.equation d.chart.represents))
  obtain ⟨u, hu⟩ := X.exists_stalk_unit_of_equal_curve_orders x c.chart.equation d.chart.equation horders
  have humul : Units.map (algebraMap (X.stalk x) X.toScheme.functionField) u * d.chart.equation =
      c.chart.equation := by
    rw [hu]
    exact inv_mul_cancel_right c.chart.equation d.chart.equation
  have huv : algebraMap (X.stalk x) X.toScheme.functionField (u : X.stalk x) *
      (d.chart.equation : X.toScheme.functionField) = (c.chart.equation : X.toScheme.functionField) :=
    congrArg (fun z : X.toScheme.functionFieldˣ => (z : X.toScheme.functionField)) humul
  have heq : a = (u : X.stalk x) * b := by
    apply IsFractionRing.injective (X.stalk x) X.toScheme.functionField
    rw [map_mul, ha, hb]
    exact huv.symm
  change Ideal.span ({a} : Set (X.stalk x)) = Ideal.span ({b} : Set (X.stalk x))
  rw [heq]
  exact Ideal.span_singleton_mul_left_unit u.isUnit b

end KltDP.Geometry.NormalProjectiveSurface
