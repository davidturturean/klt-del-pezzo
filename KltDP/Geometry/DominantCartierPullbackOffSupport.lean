import KltDP.Geometry.DominantCartierPullbackEquations
import KltDP.Geometry.FunctionFieldStalkMap
import KltDP.Geometry.CartierWeilMap
import KltDP.Geometry.PrimeCurveCartierRestriction

/-!
# The original Cartier pullback has zero coefficient off the original support

The original equation germ is a unit at the image of the original source
prime. Its image under the original scheme stalk map is a unit, and the
original stalk-to-function-field square identifies it with the pulled
rational equation. Thus its actual Weil coefficient is zero. This applies
in particular to an exceptional prime whose original centre is off the
boundary, without assuming any multiplicity or pullback coefficient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.DominantCartierPullback

variable {k : Type u} [Field k] {S : NormalProjectiveSurface k}
    {X : Scheme.{u}} [IsIntegral X]
    (π : S.toScheme ⟶ X) [GenericPointPreserving π]

/-- A unit germ of the original regular equation gives zero actual
coefficient at the original source prime under signed Cartier pullback. -/
theorem coefficient_eq_zero_of_isUnit_germ (D : CartierDivisor X)
    (c : RegularCartierEquationChart X D) (C : S.PrimeCurve)
    (hx : π.base C.genericPoint ∈ c.chart.openSet)
    (hu : IsUnit (X.presheaf.germ c.chart.openSet
      (π.base C.genericPoint) hx c.coefficient)) :
    S.cartierToWeilHom (pullbackHom π D) C = 0 := by
  let v : (S.toScheme.presheaf.stalk C.genericPoint)ˣ :=
    Units.map (π.stalkMap C.genericPoint).hom.toMonoidHom hu.unit
  have hregular :
      algebraMap (X.presheaf.stalk (π.base C.genericPoint)) X.functionField
        (X.presheaf.germ c.chart.openSet (π.base C.genericPoint) hx c.coefficient) =
      (c.chart.equation : X.functionField) := by
    change X.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes trivial)
        (X.presheaf.germ c.chart.openSet (π.base C.genericPoint) hx c.coefficient) =
      (c.chart.equation : X.functionField)
    exact (ConcreteCategory.congr_hom
      (X.presheaf.germ_stalkSpecializes hx
        ((genericPoint_spec X).specializes trivial)) c.coefficient).trans c.germ_eq
  have hmap :
      Units.map (algebraMap (S.toScheme.presheaf.stalk C.genericPoint)
        S.toScheme.functionField) v =
      Units.map (functionFieldMap π).hom.toMonoidHom c.chart.equation := by
    apply Units.ext
    change algebraMap (S.toScheme.presheaf.stalk C.genericPoint)
        S.toScheme.functionField
        (π.stalkMap C.genericPoint
          (hu.unit : X.presheaf.stalk (π.base C.genericPoint))) =
      functionFieldMap π (c.chart.equation : X.functionField)
    rw [hu.unit_spec, ← functionFieldMap_stalk_algebraMap π C.genericPoint]
    exact congrArg (functionFieldMap π) hregular
  letI : Nonempty (π ⁻¹ᵁ c.chart.openSet) := ⟨⟨C.genericPoint, hx⟩⟩
  calc
    S.cartierToWeilHom (pullbackHom π D) C =
        C.order (Units.map (functionFieldMap π).hom.toMonoidHom c.chart.equation) :=
      S.cartierToWeilHom_apply_of_equation (pullbackHom π D) C
        (π ⁻¹ᵁ c.chart.openSet) hx _
        (pullbackHom_globalEquation_preimage π D c.chart.openSet
          c.chart.equation c.chart.represents)
    _ = 0 := by
      rw [← hmap]
      exact C.order_map_local_unit v

/-- If the image of an original source prime lies off the support of the
original effective Cartier divisor, its actual pulled coefficient is zero. -/
theorem coefficient_eq_zero_of_not_mem_support (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) (C : S.PrimeCurve)
    (hx : π.base C.genericPoint ∉
      (effectiveCartierIdealDataOfRegularEquations X D hD).support) :
    S.cartierToWeilHom (pullbackHom π D) C = 0 := by
  classical
  obtain ⟨c, hc⟩ := hD (π.base C.genericPoint)
  apply coefficient_eq_zero_of_isUnit_germ π D c C hc
  by_contra hu
  exact hx ((NormalProjectiveSurface.PrimeCurve.mem_support_iff_not_isUnit_germ
    D hD c (π.base C.genericPoint) hc).mpr hu)

end KltDP.Geometry.DominantCartierPullback
