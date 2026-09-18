import KltDP.Geometry.DominantCartierPullbackCharts
import KltDP.Geometry.PullbackTransitionUnitGluing

/-!
# Signed Cartier equation units commute with the original pullback

Both sides are actual regular units. Injectivity of the original germ
map reduces their comparison to the proved equation ratio formula and
the original generic-stalk map's compatibility with `π.appLE`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.DominantCartierPullback

open TransitionUnitGluing TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (π : X ⟶ Y) [GenericPointPreserving π]

/-- The actual pulled equation atlas has the pullback of the original
Cartier module's extracted transition units. -/
theorem pulledAtlas_transitionUnits (D : CartierDivisor Y)
    (c d : CartierEquationChart Y D) :
    transitionUnits X (cartierDivisorModule X (pullbackHom π D))
        (pulledAtlas π D) c d =
      RationalTreePicard.pullbackUnits π (fun a : CartierEquationChart Y D => a.openSet)
        (transitionUnits Y (cartierDivisorModule Y D)
          (cartierDivisorLocalTrivializations Y D)) c d := by
  let U : Y.Opens := c.openSet ⊓ d.openSet
  let W : X.Opens := π ⁻¹ᵁ c.openSet ⊓ π ⁻¹ᵁ d.openSet
  letI : Nonempty U := ⟨⟨genericPoint Y,
    genericPoint_mem_nonempty_open Y c.openSet,
    genericPoint_mem_nonempty_open Y d.openSet⟩⟩
  letI : Nonempty W := ⟨⟨genericPoint X,
    genericPoint_mem_preimage π c.openSet,
    genericPoint_mem_preimage π d.openSet⟩⟩
  have hY := CartierEquationAtlas.transitionUnits_germ Y D
    (fun a : CartierEquationChart Y D => a) (cartierEquationCharts_coversTop Y D) c d
  have hX := CartierEquationAtlas.transitionUnits_germ X (pullbackHom π D)
    (pulledChart π D) (pulledCharts_coversTop π D) c d
  apply Units.ext
  apply X.germToFunctionField_injective W
  calc
    _ = (↑((pulledChart π D c).equation / (pulledChart π D d).equation) :
        X.functionField) := hX
    _ = functionFieldMap π (↑(c.equation / d.equation) : Y.functionField) :=
      congrArg Units.val
        ((Units.map (functionFieldMap π).hom.toMonoidHom).map_div
          c.equation d.equation).symm
    _ = functionFieldMap π (Y.germToFunctionField U
        (transitionUnits Y (cartierDivisorModule Y D)
          (cartierDivisorLocalTrivializations Y D) c d).val) :=
      congrArg (functionFieldMap π) hY.symm
    _ = _ := functionFieldMap_germ_appLE π U W
      (RationalTreePicard.preimage_inf_le π
        (fun a : CartierEquationChart Y D => a.openSet) c d)
      (transitionUnits Y (cartierDivisorModule Y D)
        (cartierDivisorLocalTrivializations Y D) c d).val

end KltDP.Geometry.DominantCartierPullback
