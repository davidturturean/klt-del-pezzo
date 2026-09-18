import KltDP.Geometry.DominantCartierPullbackEquations
import KltDP.Geometry.CartierEquationAtlasTransition

/-!
# The actual signed pullback equation atlas

Package the already proved inverse-image equations as original Cartier
charts, and use the accepted equation trivializations on their cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.DominantCartierPullback

open TransitionUnitGluing TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (π : X ⟶ Y) [GenericPointPreserving π]

/-- The actual inverse image of an original signed Cartier equation chart. -/
def pulledChart (D : CartierDivisor Y) (c : CartierEquationChart Y D) :
    CartierEquationChart X (pullbackHom π D) where
  openSet := π ⁻¹ᵁ c.openSet
  nonempty := inferInstance
  equation := Units.map (functionFieldMap π).hom.toMonoidHom c.equation
  represents := pullbackHom_globalEquation_preimage π D c.openSet c.equation c.represents

/-- The existing actual preimage cover, expressed in the original atlas API. -/
theorem pulledCharts_coversTop (D : CartierDivisor Y) :
    (Opens.grothendieckTopology X).CoversTop
      (fun c : CartierEquationChart Y D => (pulledChart π D c).openSet) :=
  opens_coversTop X _ (top_unique (preimageEquationCharts_cover π D))

/-- The actual module of the signed Cartier pullback, trivialized by its pulled equations. -/
def pulledAtlas (D : CartierDivisor Y) :
    KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf)
      (cartierDivisorModule X (pullbackHom π D)) :=
  CartierEquationAtlas.atlas X (pullbackHom π D) (pulledChart π D)
    (pulledCharts_coversTop π D)

end KltDP.Geometry.DominantCartierPullback
