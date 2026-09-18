/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu

Bounded compatibility port of Mathlib/Algebra/Polynomial/Bivariate.lean,
lines 211–279, official commit 59e84018b299993f5d4ca6d8cb4012b08bc55241.
Archived source SHA256:
8819789b9bf91cef22c40ffd06b9e337b35ad4a681f3ce625691109e079baba3.
The original namespaces and general commutative-semiring signatures are
retained. Only the evaluation proofs are adapted to Mathlib's pinned API.
-/
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Bivariate algebra evaluation and variable interchange

This module ports only the evaluation equivalence and swap section needed
by the compatible Lüroth proof. The earlier bivariate API is already in
the pin. No differentiation or later bivariate section is included.
-/

open scoped Polynomial.Bivariate

namespace Polynomial

noncomputable section

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

variable (R A) in
/-- Given valuations `x` and `y` in an `R`-algebra `A`, the bijection with
the unique algebra homomorphism sending `X` to `x` and `Y` to `y`. -/
@[simps! apply_apply symm_apply]
def aevalAevalEquiv : A × A ≃ (R[X][Y] →ₐ[R] A) where
  toFun xy := aeval xy.fst |>.restrictScalars R |>.comp <|
    letI := Polynomial.algebra
    aeval (R := R[X]) (C xy.snd) |>.restrictScalars R
  invFun f := ⟨f <| C X, f Y⟩
  left_inv f := by simp
  right_inv f := algHom_ext' (by ext; simp) (by simp)

/-- The unique `R`-algebra homomorphism evaluating the two variables at
the given elements of the original `R`-algebra. -/
abbrev aevalAeval (x y : A) : R[X][Y] →ₐ[R] A :=
  aevalAevalEquiv R A ⟨x, y⟩

lemma aevalAevalEquiv_apply (xy : A × A) :
    aevalAevalEquiv R A xy = aevalAeval xy.1 xy.2 := rfl

theorem coe_aevalAeval_eq_evalEval (x y : A) : ⇑(aevalAeval x y) = evalEval x y := by
  ext p
  change eval x (eval₂ (mapRingHom (RingHom.id A)) (C y) p) =
    eval x (eval (C y) p)
  rw [mapRingHom_id]
  rfl

lemma aevalAeval_C (x y : A) (p : R[X]) :
    (C p).aevalAeval x y = aeval x p := by simp

lemma aevalAeval_X (x y : A) : (C X : R[X][Y]).aevalAeval x y = x := by
  rw [aevalAeval_C, aeval_X]

lemma aevalAeval_Y (x y : A) : (Y : R[X][Y]).aevalAeval x y = y := by simp

/-- The original `R`-algebra automorphism interchanging the two variables. -/
def Bivariate.swap : R[X][Y] ≃ₐ[R] R[X][Y] := by
  apply AlgEquiv.ofAlgHom (aevalAeval (Y : R[X][Y]) (C X))
    (aevalAeval (Y : R[X][Y]) (C X)) <;> (ext n m <;> simp)

@[simp]
theorem Bivariate.swap_symm : swap.symm = (swap (R := R)) := rfl

theorem Bivariate.swap_apply (p : R[X][Y]) :
    swap p = p.aevalAeval (A := R[X][Y]) Y (C X) := rfl

attribute [local simp] Bivariate.swap_apply

theorem Bivariate.swap_X : swap (R := R) (C X) = Y := by simp

theorem Bivariate.swap_Y : swap (R := R) Y = (C X) := by simp

theorem Bivariate.swap_C_C (r : R) : swap (C (C r)) = C (C r) := by simp

theorem Bivariate.swap_C (f : R[X]) : swap (C f) = f.map C := by
  rw [swap_apply, aevalAeval_C]
  rfl

theorem Bivariate.swap_swap_apply (p : R[X][Y]) : swap (swap p) = p :=
  AlgEquiv.symm_apply_apply swap p

theorem Bivariate.swap_map_C (f : R[X]) : swap (f.map C) = C f := by
  rw [← swap_C, swap_swap_apply]

theorem Bivariate.swap_monomial (n : ℕ) (f : R[X]) :
    swap (monomial n f) = f.map C * C (X ^ n) := by
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, swap_C, swap_Y, C_pow]

end
end Polynomial

#print axioms Polynomial.aevalAevalEquiv
#print axioms Polynomial.Bivariate.swap
#print axioms Polynomial.Bivariate.swap_monomial
