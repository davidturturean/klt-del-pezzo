import KltDP.Geometry.DominantCartierPullbackCharts
import KltDP.Geometry.CartierDivisorPullback

/-!
# Signed pullback of an original Cartier divisor with regular equations

The existing signed pullback and the existing regular-equation pullback
have identical original equations on the actual inverse-image cover.
Their equality is therefore sheaf locality. The same original section
maps give regular equation charts for the signed pullback directly.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace KltDP.Geometry.DominantCartierPullback
attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (π : X ⟶ Y) [GenericPointPreserving π]

/-- The original pulled regular coefficient represents the signed pullback
on the actual inverse image of the original regular equation chart. -/
def pulledRegularChart (D : CartierDivisor Y) (c : RegularCartierEquationChart Y D) :
    RegularCartierEquationChart X (pullbackHom π D) where
  chart := pulledChart π D c.chart
  coefficient := π.app c.chart.openSet c.coefficient
  germ_eq := germ_pulledCoefficient π D c

/-- The inverse images of the original regular equation charts cover the
source, so the actual signed pullback has regular equations. -/
theorem pullbackHom_hasRegularEquations (D : CartierDivisor Y)
    (hD : HasRegularCartierEquations Y D) :
    HasRegularCartierEquations X (pullbackHom π D) := by
  intro x
  obtain ⟨c, hc⟩ := hD (π.base x)
  exact ⟨pulledRegularChart π D c, hc⟩

/-- The signed sheaf pullback is the original regular-equation pullback
whenever the original divisor has regular equations. -/
theorem pullbackHom_eq_pullbackDivisor (D : CartierDivisor Y)
    (hD : HasRegularCartierEquations Y D) :
    pullbackHom π D = pullbackDivisor π D hD := by
  apply cartierDivisor_eq_of_restrict_eq X
    (fun c : RegularCartierEquationChart Y D => π ⁻¹ᵁ c.chart.openSet)
    (pulled_cover π D hD)
  intro c
  exact (pullbackHom_globalEquation_preimage π D c.chart.openSet
    c.chart.equation c.chart.represents).symm.trans
      (pullbackDivisor_restrict π D hD c).symm

end KltDP.Geometry.DominantCartierPullback

#print axioms KltDP.Geometry.DominantCartierPullback.pullbackHom_eq_pullbackDivisor
#print axioms KltDP.Geometry.DominantCartierPullback.pullbackHom_hasRegularEquations
