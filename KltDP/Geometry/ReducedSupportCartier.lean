import KltDP.Geometry.RegularCartierIdealSupport
import KltDP.Geometry.SelectedPrimeCurveCartierUnion

/-!
# The actual reduced Cartier support on a locally factorial surface

Use the existing Cartier inverse of the finite set of actual prime curves
in the original divisor. Its regular-equation ideal is exactly the radical
of the original effective divisor ideal, with no auxiliary line bundle.
For a point blowup this construction applies to the actual total boundary
including the exceptional divisor; SNC preservation is a separate theorem.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace KltDP.Geometry.NormalProjectiveSurface
variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
variable [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]

/-- Coefficient one on every actual component of the original Cartier divisor. -/
def reducedSupportCartier (D : CartierDivisor X.toScheme) :
    CartierDivisor X.toScheme :=
  X.selectedPrimeCartier (X.cartierToWeilHom D).support

theorem reducedSupportCartier_effective (D : CartierDivisor X.toScheme) :
    EffectiveDivisor (X.cartierToWeilHom (X.reducedSupportCartier D)) :=
  X.selectedPrimeCartier_effective _

theorem reducedSupportCartier_le_one (D : CartierDivisor X.toScheme) (C : X.PrimeCurve) :
    X.cartierToWeilHom (X.reducedSupportCartier D) C ≤ 1 :=
  X.selectedPrimeCartier_le_one _ C

theorem reducedSupportCartier_coefficient (D : CartierDivisor X.toScheme)
    (C : X.PrimeCurve) :
    X.cartierToWeilHom (X.reducedSupportCartier D) C =
      if X.cartierToWeilHom D C ≠ 0 then 1 else 0 := by
  classical
  change X.cartierToWeilHom (X.selectedPrimeCartier _) C = _
  rw [X.selectedPrimeCartier_weil, X.selectedPrimeWeil_apply]
  simp only [Finsupp.mem_support_iff]

theorem reducedSupportCartier_support (D : CartierDivisor X.toScheme) :
    divisorSupport (X.cartierToWeilHom (X.reducedSupportCartier D)) =
      divisorSupport (X.cartierToWeilHom D) := by
  change divisorSupport (X.cartierToWeilHom (X.selectedPrimeCartier _)) = _
  rw [X.selectedPrimeCartier_weil, X.selectedPrimeWeil_divisorSupport]
  rfl

/-- The actual Cartier ideal is the radical of the original effective ideal. -/
theorem reducedSupportCartier_idealData (D : CartierDivisor X.toScheme)
    (hD : EffectiveDivisor (X.cartierToWeilHom D)) :
    effectiveCartierIdealDataOfRegularEquations X.toScheme (X.reducedSupportCartier D)
        (X.hasRegularCartierEquations_of_effective_weil _
          (X.reducedSupportCartier_effective D)) =
      (effectiveCartierIdealDataOfRegularEquations X.toScheme D
        (X.hasRegularCartierEquations_of_effective_weil D hD)).radical := by
  rw [X.regularCartierIdealData_eq_vanishingIdeal _
      (X.reducedSupportCartier_effective D) (X.reducedSupportCartier_le_one D),
    X.regularCartierIdealData_radical_eq_vanishingIdeal D hD]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  exact SetLike.coe_injective (X.reducedSupportCartier_support D)

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.reducedSupportCartier_idealData
#print axioms KltDP.Geometry.NormalProjectiveSurface.reducedSupportCartier_idealData
