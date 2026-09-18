import KltDP.Geometry.CartierWeilMap
import KltDP.Geometry.NormalStalkDVR
import KltDP.Geometry.EffectiveCartierSection

/-!
# Original Cartier coefficients from a uniformizer germ

The regular equation's actual germ maps to its original function-field
equation. When that germ is irreducible in the original curve DVR, the
accepted uniformizer-order theorem gives coefficient one. No equation,
field map or valuation is replaced by a chosen comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

/-- An original regular Cartier equation whose actual curve germ is a
uniformizer has coefficient one at that original prime curve. -/
theorem cartierToWeilHom_eq_one_of_irreducible_germ
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (D : CartierDivisor X.toScheme) (c : RegularCartierEquationChart X.toScheme D)
    (C : X.PrimeCurve) (hx : C.genericPoint ∈ c.chart.openSet)
    (hr : Irreducible
      (X.toScheme.presheaf.germ c.chart.openSet C.genericPoint hx c.coefficient)) :
    X.cartierToWeilHom D C = 1 := by
  let g := X.toScheme.presheaf.germ c.chart.openSet C.genericPoint hx c.coefficient
  letI : IsDiscreteValuationRing (X.stalk C.genericPoint) := C.genericPoint_isDiscreteValuationRing
  have hfield : algebraMap (X.stalk C.genericPoint) X.toScheme.functionField g =
      (c.chart.equation : X.toScheme.functionField) := by
    change X.toScheme.presheaf.stalkSpecializes
        ((genericPoint_spec X.toScheme).specializes trivial)
        (X.toScheme.presheaf.germ c.chart.openSet C.genericPoint hx c.coefficient) = _
    exact (ConcreteCategory.congr_hom
      (X.toScheme.presheaf.germ_stalkSpecializes hx
        ((genericPoint_spec X.toScheme).specializes trivial)) c.coefficient).trans c.germ_eq
  have heq : c.chart.equation =
      RingTheory.fractionFieldUnit (X.stalk C.genericPoint) X.toScheme.functionField g hr.ne_zero :=
    Units.ext hfield.symm
  calc
    X.cartierToWeilHom D C = C.order c.chart.equation :=
      X.cartierToWeilHom_apply_of_equation D C c.chart.openSet hx
        c.chart.equation c.chart.represents
    _ = 1 := by
      rw [heq, C.order_eq_stalkDivisorOrder]
      exact stalkDivisorOrder_uniformizer X.toScheme C.genericPoint g hr

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.cartierToWeilHom_eq_one_of_irreducible_germ
#print axioms KltDP.Geometry.NormalProjectiveSurface.cartierToWeilHom_eq_one_of_irreducible_germ
