import KltDP.Examples.ProjectiveLinePointAtInfinity
import KltDP.Examples.FrobeniusGraphPicardClassPowerCharts

/-!
# The power morphism fixes the point at infinity

On the second polynomial chart the accepted `projectivePowerMorphism p` is the substitution
`X ↦ X^p` (accepted `polynomialChartMap_power_both`), and evaluation at `0` after `X ↦ X^p` is
evaluation at `0` when `0 < p`; hence `∞ ≫ F = ∞` (`infinityMorphism_projectivePowerMorphism`) and
`F(∞) = ∞` on points (`projectivePowerMorphism_infinityPoint`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusPowerInfinity

open KltDP.Geometry ProjectiveLineComparison FrobeniusProjectivePoints FrobeniusProjectiveMorphism
  FrobeniusGlobalGraphCompatibility FrobeniusGraphPicardClassPowerCharts
  ProjectiveLinePointAtInfinity

variable {k : Type u} [Field k]

theorem evalRingHom_zero_comp_polynomialPowerHom (p : ℕ) (hp : 0 < p) :
    (Polynomial.evalRingHom (0 : k)).comp (polynomialPowerHom p) = Polynomial.evalRingHom 0 := by
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp [hp.ne']

/-- The power morphism fixes the rational point `∞`. -/
theorem infinityMorphism_projectivePowerMorphism (p : ℕ) (hp : 0 < p) :
    infinityMorphism ≫ projectivePowerMorphism (k := k) p = infinityMorphism := by
  rw [infinityMorphism, Category.assoc, polynomialChartMap_power_both, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, evalRingHom_zero_comp_polynomialPowerHom p hp]

/-- The power morphism fixes the point at infinity. -/
theorem projectivePowerMorphism_infinityPoint (p : ℕ) (hp : 0 < p) :
    (projectivePowerMorphism (k := k) p).base infinityPoint = infinityPoint := by
  rw [← fieldMorphismPoint_infinityMorphism]
  change fieldMorphismPoint (infinityMorphism ≫ projectivePowerMorphism (k := k) p) = _
  rw [infinityMorphism_projectivePowerMorphism p hp]

end KltDP.Examples.FrobeniusPowerInfinity
