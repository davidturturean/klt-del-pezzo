import KltDP.Geometry.QCartierPullbackFunctorial
import Mathlib.Tactic.Abel

/-!
Relative differences of actual rational Weil divisors compose along the
original morphisms. Applied to compatible canonical representatives, this
is the divisor identity needed to compare discrepancies on higher models.
It does not supply a canonical blowup formula, an SNC assertion, or a
dominating model; those are separate geometric obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QCartierPullback

variable {k : Type u} [Field k] [IsAlgClosed k]
    {X Y Z : NormalProjectiveSurface k}

/-- Subtraction is preserved on the original Q-Cartier Weil divisors,
including their original membership proofs. -/
theorem pullback_sub (f : X.toScheme ⟶ Y.toScheme)
    [GenericPointPreserving f]
    (D E : Y.RationalWeilDivisor) (hD : Y.QCartier D) (hE : Y.QCartier E) :
    pullback (X := X) (Y := Y) f (D - E) (Y.rationalCartierSubmodule.sub_mem hD hE) =
      pullback (X := X) (Y := Y) f D hD - pullback (X := X) (Y := Y) f E hE := by
  let d : Y.rationalCartierSubmodule := ⟨D, hD⟩
  let e : Y.rationalCartierSubmodule := ⟨E, hE⟩
  let F : Y.rationalCartierSubmodule →ₗ[ℚ] X.RationalWeilDivisor :=
    pullbackToWeil (X := X) (Y := Y) f
  change F (d - e) = F d - F e
  exact F.map_sub d e

/-- The relative difference for the composite is the first relative
difference plus the actual pullback of the second. No positivity of the
divisors or their coefficients is required. -/
theorem relative_difference_comp
    (f : X.toScheme ⟶ Y.toScheme) (g : Y.toScheme ⟶ Z.toScheme)
    [GenericPointPreserving f] [GenericPointPreserving g]
    (DX : X.RationalWeilDivisor) (DY : Y.RationalWeilDivisor)
    (DZ : Z.RationalWeilDivisor) (hY : Y.QCartier DY) (hZ : Z.QCartier DZ) :
    DX - pullback (X := X) (Y := Z) (f ≫ g) DZ hZ =
      (DX - pullback (X := X) (Y := Y) f DY hY) +
        pullback (X := X) (Y := Y) f (DY - pullback (X := Y) (Y := Z) g DZ hZ)
          (Y.rationalCartierSubmodule.sub_mem hY (pullback_qCartier (X := Y) (Y := Z) g DZ hZ)) := by
  rw [pullback_comp (X := X) (Y := Y) (Z := Z),
    pullback_sub (X := X) (Y := Y)]
  abel

end KltDP.Geometry.QCartierPullback
