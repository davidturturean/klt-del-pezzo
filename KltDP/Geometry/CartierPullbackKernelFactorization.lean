import KltDP.Geometry.CartierIdealKernelEquations
import KltDP.Geometry.CartierDivisorPullback

/-!
The actual pulled Cartier ideal has the expected factorization criterion.
This follows from the original pulled coefficients and the original
scheme composition map on sections, before any fiber isomorphism is built.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.CartierPullbackKernelFactorization

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (π : X ⟶ Y) [GenericPointPreserving π] [QuasiCompact π]
  (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)
  (f : Z ⟶ X) [QuasiCompact f]

/-- The original pulled ideal is killed exactly when the original target
ideal is killed by the original composite morphism. -/
theorem le_ker_iff :
    pullbackIdealData π D hD ≤ f.ker ↔
      effectiveCartierIdealDataOfRegularEquations Y D hD ≤ (f ≫ π).ker := by
  rw [pullbackIdealData,
    CartierIdealKernelEquations.le_ker_iff_coefficients_eq_zero
      (pullbackDivisor π D hD) (pullbackDivisor_hasRegularEquations π D hD) f
      (pullbackDivisor_regularChart π D hD) (fun x => hD (π.base x)),
    CartierIdealKernelEquations.le_ker_iff_coefficients_eq_zero
      D hD (f ≫ π) (fun c => c) hD]
  apply forall_congr'
  intro c
  change f.app (π ⁻¹ᵁ c.chart.openSet) (π.app c.chart.openSet c.coefficient) = 0 ↔
    (f ≫ π).app c.chart.openSet c.coefficient = 0
  rw [Scheme.comp_app]
  rfl

#check KltDP.Geometry.CartierPullbackKernelFactorization.le_ker_iff
#print axioms KltDP.Geometry.CartierPullbackKernelFactorization.le_ker_iff

end KltDP.Geometry.CartierPullbackKernelFactorization
