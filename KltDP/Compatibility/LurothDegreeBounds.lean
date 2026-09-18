/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
import KltDP.Compatibility.LurothPrimitiveNormalization
import KltDP.Compatibility.BivariateSwapCoefficients

/-! Compatible port of the original degree bounds in Lüroth's proof,
Mathlib commit 59e84018b299993f5d4ca6d8cb4012b08bc55241, Luroth.lean
239-276. A direct coefficient identity for the original swap polynomial
replaces the newer independent-monomial-sum degree lemma. -/

variable {K : Type*} [Field K]
open IntermediateField

namespace RatFunc.Luroth
noncomputable section
open _root_.IntermediateField.algebraAdjoinAdjoin Polynomial
open scoped Polynomial.Bivariate
variable {E : IntermediateField K (RatFunc K)}

lemma le_Φ_coeff_generatorIndex_natDegree (h : E ≠ ⊥) :
    (f E).natDegree ≤ ((Φ E).coeff (generatorIndex h)).natDegree := by
  have := congr($(Φ_coeff_generatorIndex h) * algebraMap K[X] (RatFunc K) (g E))
  conv at this => enter [2, 1, 2]; rw [← num_div_denom (generator E)]
  rw [mul_assoc, div_mul_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero),
    ← map_mul, ← map_mul] at this
  replace this := congr($(algebraMap_injective K this).natDegree)
  rw [natDegree_mul (Φ_coeff_generatorIndex_ne_zero h) (generator E).denom_ne_zero,
    natDegree_mul (num_ne_zero (c_ne_zero h)) (num_ne_zero (generator_ne_zero h))] at this
  have hle := natDegree_le_of_dvd (generator_denom_dvd_c_num h)
    (num_ne_zero (c_ne_zero h))
  dsimp only [f, g] at this hle ⊢
  omega

lemma le_Φ_coeff_natDegree_natDegree (h : E ≠ ⊥) :
    (g E).natDegree ≤ ((Φ E).coeff (φ E).natDegree).natDegree := by
  rw [Φ_coeff_φ_natDegree' h]
  exact natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h))

variable (E) in
/-- The height of `generator E`. -/
abbrev m : ℕ := max (f E).natDegree (g E).natDegree

lemma m_le_swap_Φ_natDegree (h : E ≠ ⊥) :
    m E ≤ (Bivariate.swap (Φ E)).natDegree := by
  exact max_le
    ((le_Φ_coeff_generatorIndex_natDegree h).trans
      (KltDP.Compatibility.BivariateSwapCoefficients.natDegree_coeff_le_natDegree_swap
        (Φ E) (generatorIndex h)))
    ((le_Φ_coeff_natDegree_natDegree h).trans
      (KltDP.Compatibility.BivariateSwapCoefficients.natDegree_coeff_le_natDegree_swap
        (Φ E) (φ E).natDegree))

end
end RatFunc.Luroth

#print axioms RatFunc.Luroth.m_le_swap_Φ_natDegree
