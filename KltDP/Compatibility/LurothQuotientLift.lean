/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
import KltDP.Compatibility.LurothPolynomialRelation
import KltDP.Compatibility.PrimitivePolynomialLifts

/-! The original quotient first descends from rational coefficients to a
bivariate polynomial, then becomes a univariate polynomial by the proved
swap-degree bound. Ported from official Mathlib commit
59e84018b299993f5d4ca6d8cb4012b08bc55241, Luroth.lean 355-405. -/

variable {K : Type*} [Field K]
open IntermediateField

namespace RatFunc.Luroth
noncomputable section
open _root_.IntermediateField.algebraAdjoinAdjoin Polynomial
open scoped Polynomial.Bivariate
variable {E : IntermediateField K (RatFunc K)}

lemma Q₀_mem_lifts (h : E ≠ ⊥) : Q₀ E ∈ lifts (algebraMap K[X] (RatFunc K)) := by
  classical
  apply (KltDP.Compatibility.PrimitivePolynomialLifts.mul_map_mem_lifts_iff
    (Φ' E).isPrimitive_primPart).mp
  rw [Q₀_mul_Φ h]
  exact ⟨_, rfl⟩

/-- A bivariate polynomial `Q₁` that satisfies `Q₁ * Φ = θ`. -/
abbrev Q₁ (h : E ≠ ⊥) : K[X][Y] := (Q₀_mem_lifts h).choose

lemma map_Q₁ (h : E ≠ ⊥) : (Q₁ h).map (algebraMap K[X] (RatFunc K)) = Q₀ E :=
  (Q₀_mem_lifts h).choose_spec

lemma Q₁_ne_zero (h : E ≠ ⊥) : Q₁ h ≠ 0 := by
  apply_fun Polynomial.map (algebraMap K[X] (RatFunc K))
  rw [map_Q₁, Polynomial.map_zero]
  exact Q₀_ne_zero h

/-- Equation (11.3.8) from Cohn's proof, viewed as an equation of bivariate polynomials. -/
lemma Q₁_mul_Φ (h : E ≠ ⊥) : Q₁ h * Φ E = θ E := by
  apply_fun Polynomial.map (algebraMap K[X] (RatFunc K)) using
    Polynomial.map_injective _ (algebraMap_injective K)
  rw [Polynomial.map_mul, map_Q₁, Q₀_mul_Φ h]

lemma swap_Q₁_natDegree (h : E ≠ ⊥) : (Bivariate.swap (Q₁ h)).natDegree = 0 := by
  have : Q₁ h * Φ E = θ E := Q₁_mul_Φ h
  apply_fun Bivariate.swap at this
  rw [map_mul] at this
  apply_fun natDegree at this
  rw [natDegree_mul
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Q₁_ne_zero h))
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h))] at this
  have h₁ : (Bivariate.swap (θ E)).natDegree ≤ m E := by
    rw [swap_θ, natDegree_neg]
    exact θ_natDegree_le h
  have h₂ := m_le_swap_Φ_natDegree h
  omega

/-- A univariate polynomial `Q₂` that satisfies `Q₂ * Φ = θ`. -/
abbrev Q₂ (h : E ≠ ⊥) : K[X] := (Bivariate.swap (Q₁ h)).coeff 0

lemma Q₂_map (h : E ≠ ⊥) : (Q₂ h).map Polynomial.C = Q₁ h := by
  have := eq_C_of_natDegree_eq_zero (swap_Q₁_natDegree h)
  apply_fun Bivariate.swap at this
  rw [Bivariate.swap_swap_apply, Bivariate.swap_C] at this
  exact this.symm

lemma Q₂_ne_zero (h : E ≠ ⊥) : Q₂ h ≠ 0 := by
  apply_fun Polynomial.map Polynomial.C
  rw [Polynomial.map_zero, Q₂_map]
  exact Q₁_ne_zero h

/-- Equation (11.3.8) from Cohn's proof, where we view `Q` as a univariate polynomial. -/
lemma Q₂_mul_Φ (h : E ≠ ⊥) : (Q₂ h).map Polynomial.C * Φ E = θ E := by
  rw [Q₂_map h, Q₁_mul_Φ h]


end
end RatFunc.Luroth

#print axioms RatFunc.Luroth.Q₁_mul_Φ
#print axioms RatFunc.Luroth.Q₂_mul_Φ
