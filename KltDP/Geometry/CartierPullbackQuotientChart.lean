import KltDP.Geometry.CartierDivisorPullbackIdeal
import KltDP.Compatibility.QuotientIdealPullback

/-!
An original affine chart of the actual pulled Cartier zero scheme is
the actual base change of the target equation quotient. The two maps
use the original appLE and quotient maps. No fiber comparison is assumed.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.CartierPullbackQuotientChart

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (π : X ⟶ Y) [GenericPointPreserving π]
  (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)
  (c : RegularCartierEquationChart Y D) (W : X.affineOpens) [Nonempty W.1]
  (hW : W.1 ≤ π ⁻¹ᵁ c.chart.openSet)

/-- The original map carries the original equation ideal to the actual
pulled divisor ideal on the original affine source chart. -/
theorem map_equationIdeal :
    Ideal.map (π.appLE c.chart.openSet W.1 hW).hom (Ideal.span {c.coefficient}) =
      (pullbackIdealData π D hD).ideal W := by
  rw [Ideal.map_span, Set.image_singleton, pullbackIdealData_ideal π D hD c W hW]

/-- The actual quotient-chart square is a categorical pullback. -/
theorem isPullback_chart :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((pullbackIdealData π D hD).ideal W))))
      (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap ((pullbackIdealData π D hD).ideal W)
          (π.appLE c.chart.openSet W.1 hW).hom
          (Ideal.map_le_iff_le_comap.mp (map_equationIdeal π D hD c W hW).le))))
      (Spec.map (π.appLE c.chart.openSet W.1 hW))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c.coefficient})))) :=
  KltDP.QuotientIdealPullback.isPullback (π.appLE c.chart.openSet W.1 hW).hom
    (Ideal.span {c.coefficient}) ((pullbackIdealData π D hD).ideal W)
    (map_equationIdeal π D hD c W hW)

#check KltDP.Geometry.CartierPullbackQuotientChart.isPullback_chart
#print axioms KltDP.Geometry.CartierPullbackQuotientChart.isPullback_chart

end KltDP.Geometry.CartierPullbackQuotientChart
