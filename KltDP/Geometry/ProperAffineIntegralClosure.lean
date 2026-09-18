import KltDP.Geometry.ProperAffineSectionsFinite
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# The actual integral closure on a proper affine-base chart

The original finite section algebra is integral over the original base.
Its actual integral-closure subalgebra is therefore the full section algebra.
The comparison below is an ordinary algebra isomorphism induced by this
equality, preserving the original scalar map and the original elements.
It is the chart comparison needed by the normalization clause of Stein
factorization, including nonreduced and nonnormal source schemes.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ProperAffineSections

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

/-- Integrality concerns the exact original affine-base scalar map. -/
theorem baseScalar_isIntegral : (baseScalar f).IsIntegral :=
  (baseScalar_finite f).to_isIntegral

/-- The actual integral closure in the original section ring is the whole ring. -/
theorem integralClosure_eq_top :
    letI := (baseScalar f).toAlgebra
    integralClosure R Γ(X, ⊤) = ⊤ := by
  letI := (baseScalar f).toAlgebra
  exact integralClosure_eq_top_iff.mpr ⟨baseScalar_isIntegral f⟩

/-- This is the original integral-closure inclusion, now an algebra isomorphism. -/
def integralClosureEquiv :
    letI := (baseScalar f).toAlgebra
    integralClosure R Γ(X, ⊤) ≃ₐ[R] Γ(X, ⊤) := by
  letI := (baseScalar f).toAlgebra
  exact (Subalgebra.equivOfEq _ _ (integralClosure_eq_top f)).trans Subalgebra.topEquiv

@[simp] theorem integralClosureEquiv_apply :
    letI := (baseScalar f).toAlgebra
    ∀ x : integralClosure R Γ(X, ⊤), integralClosureEquiv f x = x.val := by
  letI := (baseScalar f).toAlgebra
  intro x
  rfl

end KltDP.Geometry.ProperAffineSections
