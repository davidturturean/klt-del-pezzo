import KltDP.Geometry.StrictNormalCrossingsCartierIdealData
import KltDP.Geometry.CartierDivisorPullbackIdeal

/-!
# The actual pulled Cartier ideal at an original stalk

The accepted regular pullback chart is used through its original
coefficient. The actual scheme stalk-map/germ equation identifies the
target ideal with extension of the original source ideal. The two
affine neighborhoods are arbitrary neighborhoods of the actual points.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (π : X ⟶ Y) [GenericPointPreserving π]

/-- The original pulled Cartier ideal at a stalk is extension of the
original source Cartier ideal through the original scheme stalk map. -/
theorem pullbackIdealData_map_germ (D : CartierDivisor Y)
    (hD : HasRegularCartierEquations Y D)
    (U : Y.affineOpens) (W : X.affineOpens) (x : X)
    (hxW : x ∈ W.1) (hxU : π.base x ∈ U.1) :
    Ideal.map (X.presheaf.germ W.1 x hxW).hom ((pullbackIdealData π D hD).ideal W) =
      Ideal.map (π.stalkMap x).hom
        (Ideal.map (Y.presheaf.germ U.1 (π.base x) hxU).hom
          ((effectiveCartierIdealDataOfRegularEquations Y D hD).ideal U)) := by
  obtain ⟨c, hxc⟩ := hD (π.base x)
  have htarget := regularCartierIdealData_map_germ_eq_span X
    (pullbackDivisor π D hD) (pullbackDivisor_hasRegularEquations π D hD)
    (pullbackDivisor_regularChart π D hD c) W x hxW hxc
  have hsource := regularCartierIdealData_map_germ_eq_span Y D hD c U (π.base x) hxU hxc
  change Ideal.map (X.presheaf.germ W.1 x hxW).hom
    ((pullbackIdealData π D hD).ideal W) = _ at htarget
  rw [htarget, hsource, Ideal.map_span, Set.image_singleton]
  change Ideal.span ({X.presheaf.germ (π ⁻¹ᵁ c.chart.openSet) x hxc
      (π.app c.chart.openSet c.coefficient)} : Set (X.presheaf.stalk x)) =
    Ideal.span ({π.stalkMap x (Y.presheaf.germ c.chart.openSet (π.base x) hxc c.coefficient)} :
      Set (X.presheaf.stalk x))
  rw [Scheme.stalkMap_germ_apply]

end KltDP.Geometry
