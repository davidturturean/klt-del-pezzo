/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors

The transition identities are adapted from frenzymath/Algebraic-Geometry
9223d85c786394721963a9d642b08d066b72a594,
MainProjects/AlgebraicJacobian/PicardAlbanese/AlgebraicJacobian/Algebra/
BaseChangeTrivialization.lean:128-154. The unit itself is constructed from
the pinned Mathlib equivalences for linear automorphisms and endomorphisms
of the rank-one module. Uniqueness is stated for the full source module.
-/
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.Algebra.Group.Units.Opposite

/-!
# Transition units between actual linear trivializations

Two linear identifications of the same R-module with R differ by a unit
of R. The unit is obtained from their actual composite automorphism, and
its value is the image of the first trivialization's inverse of 1 under
the second trivialization. All identities concern the original module
and scalar ring; no tensor presentation or base change is assumed.
-/

noncomputable section

namespace KltDP.Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (t₁ t₂ t₃ : M ≃ₗ[R] R)

/-- The unit carrying coordinates in the first trivialization to the second. -/
def transitionUnit : Rˣ :=
  MulOpposite.unop
    (Units.opEquiv
      (Units.map (RingEquiv.moduleEndSelf R).symm.toMulEquiv.toMonoidHom
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (t₁.symm.trans t₂))))

@[simp]
theorem transitionUnit_val : (transitionUnit t₁ t₂ : R) = t₂ (t₁.symm 1) := rfl

/-- The original transition unit sends every coordinate to its other chart value. -/
theorem transitionUnit_mul_apply (x : M) :
    (transitionUnit t₁ t₂ : R) * t₁ x = t₂ x := by
  rw [transitionUnit_val, mul_comm]
  have h1 : t₁ x • t₁.symm (1 : R) = x := by
    rw [← map_smul, smul_eq_mul, mul_one, t₁.symm_apply_apply]
  rw [← smul_eq_mul, ← map_smul, h1]

@[simp]
theorem transitionUnit_self (t : M ≃ₗ[R] R) : transitionUnit t t = 1 :=
  Units.ext (by rw [transitionUnit_val, t.apply_symm_apply, Units.val_one])

/-- The transition units satisfy the telescoping, or triple-cocycle, identity. -/
theorem transitionUnit_mul_transitionUnit :
    transitionUnit t₂ t₃ * transitionUnit t₁ t₂ = transitionUnit t₁ t₃ :=
  Units.ext (transitionUnit_mul_apply t₂ t₃ (t₁.symm 1))

/-- A common change of the source module preserves the transition unit. -/
@[simp]
theorem transitionUnit_trans {M' : Type*} [AddCommGroup M'] [Module R M']
    (φ : M' ≃ₗ[R] M) :
    transitionUnit (φ.trans t₁) (φ.trans t₂) = transitionUnit t₁ t₂ := by
  apply Units.ext
  rw [transitionUnit_val, transitionUnit_val, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- A unit with the coordinate-change identity on the full module is the transition unit. -/
theorem transitionUnit_eq_of {a : Rˣ}
    (h : ∀ x : M, (a : R) * t₁ x = t₂ x) : transitionUnit t₁ t₂ = a := by
  have h1 := h (t₁.symm 1)
  rw [t₁.apply_symm_apply, mul_one] at h1
  exact Units.ext ((transitionUnit_val t₁ t₂).trans h1.symm)

end KltDP.Module
