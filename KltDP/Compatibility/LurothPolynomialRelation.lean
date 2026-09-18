/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
import KltDP.Compatibility.LurothDegreeBounds
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring

/-! Compatible port of the original quotient-polynomial identity in
Mathlib commit 59e84018b299993f5d4ca6d8cb4012b08bc55241, Luroth.lean
278-353. All polynomials, intermediate fields and scalar maps are the
original ones from the proof; no polynomial relation is assumed. -/

variable {K : Type*} [Field K]
open IntermediateField

namespace RatFunc.Luroth
noncomputable section
open _root_.IntermediateField.algebraAdjoinAdjoin Polynomial
open scoped Polynomial.Bivariate
variable {E : IntermediateField K (RatFunc K)}

private theorem coe_adjoin_algebraMap (x : Algebra.adjoin K {generator E}) :
    ((algebraMap (Algebra.adjoin K {generator E}) K⟮generator E⟯ x :
      K⟮generator E⟯) : RatFunc K) = x := rfl

instance : Algebra K⟮generator E⟯ E :=
  (IntermediateField.inclusion adjoin_generator_le).toAlgebra

/-- Since `minpolyX` of our `generator` annihilates `X`, the minimal polynomial `φ`
must divide it. -/
lemma φ_dvd_generator_minpolyX :
    φ E ∣ ((generator E).minpolyX K⟮generator E⟯).map (algebraMap _ E) := by
  apply minpoly.dvd
  rw [aeval_def, eval₂_map]
  change (aeval (X : RatFunc K))
    ((generator E).minpolyX K⟮generator E⟯) = 0
  exact (generator E).minpolyX_aeval_X

variable (E) in
/-- A polynomial `q` that satisfies `φ * q = (generator E).minpolyX`. -/
abbrev q : E[X] := φ_dvd_generator_minpolyX.choose

lemma φ_mul_q :
    φ E * q E = ((generator E).minpolyX K⟮generator E⟯).map (algebraMap _ E) :=
  φ_dvd_generator_minpolyX.choose_spec.symm

lemma q_ne_zero (h : E ≠ ⊥) : q E ≠ 0 := right_ne_zero_of_mul <|
  φ_mul_q (E := E) ▸ Polynomial.map_ne_zero <|
    (generator E).minpolyX_eq_zero_iff.not.mpr (generator_ne_C h)

-- The next series of definitions concerns the polynomial `Q` in Cohn's proof.
-- A priori, it will be a polynomial with coefficients in `(RatFunc K)`, which we call `Q₀`.
-- We then show that `Q₀` is also a polynomial in the other variable, hence we get
-- a bivariate polynomial `Q₁`. Then we show that it is independent of `X`, hence we may
-- replace it by a univariate polynomial `Q₂`. Finally, we prove that it is also independent
-- of `x`, hence we replace it by a constant `Q₃`.

variable (E) in
/-- A polynomial `Q₀` with coefficients in `(RatFunc K)` that satisfies `Q₀ * Φ = θ`. -/
abbrev Q₀ : (RatFunc K)[X] :=
  Polynomial.C ((algebraMap K[X] (RatFunc K) (g E)) / c E) * (q E).map (algebraMap E (RatFunc K))

lemma Q₀_ne_zero (h : E ≠ ⊥) : Q₀ E ≠ 0 := by
  apply mul_ne_zero
  · exact C_ne_zero.mpr (div_ne_zero (algebraMap_ne_zero (generator E).denom_ne_zero) (c_ne_zero h))
  · exact Polynomial.map_ne_zero (q_ne_zero h)

variable (E) in
/-- The bivariate polynomial `g(X) * f(Y) - f(X) * g(Y)`, where `f` and `g` are
the numerator and denominator of `generator`. This is an auxiliary definition
for the proof of Lüroth's theorem. -/
abbrev θ : K[X][Y] :=
  Polynomial.C (g E) * (f E).map Polynomial.C - Polynomial.C (f E) * (g E).map Polynomial.C

lemma swap_θ : Bivariate.swap (θ E) = -(θ E) := by
  rw [map_sub, map_mul, map_mul, Bivariate.swap_C, Bivariate.swap_map_C, Bivariate.swap_C,
    Bivariate.swap_map_C]
  ring

lemma θ_natDegree_le (h : E ≠ ⊥) : (θ E).natDegree ≤ m E := by
  convert natDegree_sub_le _ _ using 3
  · rw [natDegree_mul (C_ne_zero.mpr (generator E).denom_ne_zero)
      (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h))), natDegree_C, zero_add,
      natDegree_map]
  · rw [natDegree_mul (C_ne_zero.mpr (num_ne_zero (generator_ne_zero h)))
      (Polynomial.map_ne_zero (generator E).denom_ne_zero), natDegree_C, zero_add, natDegree_map]

/-- Equation (11.3.8) from Cohn's proof, viewed as an equation of polynomials with coefficients
in `(RatFunc K)`. -/
lemma Q₀_mul_Φ (h : E ≠ ⊥) :
    Q₀ E * (Φ E).map (algebraMap K[X] (RatFunc K)) = (θ E).map (algebraMap K[X] (RatFunc K)) := by
  suffices
    Polynomial.C ((algebraMap K[X] (RatFunc K)) (g E)) * (q E).map (algebraMap (↥E) (RatFunc K)) *
       (φ E).map (algebraMap (↥E) (RatFunc K)) = (θ E).map (algebraMap K[X] (RatFunc K)) by
    rw [← C_c_mul_φ h, mul_assoc, ← mul_assoc _ (Polynomial.C (c E)) _,
      mul_comm _ (Polynomial.C (c E))]
    simpa only [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (c_ne_zero h)] using this
  rw [mul_assoc, ← Polynomial.map_mul, mul_comm (q E) (φ E), φ_mul_q, Polynomial.map_map,
    Polynomial.map_sub, Polynomial.map_mul, map_C, RingHom.coe_comp, Function.comp_apply,
    IntermediateField.algebraMap_apply, Polynomial.map_map, Polynomial.map_map, mul_sub,
    ← mul_assoc, ← map_mul, (inclusion adjoin_generator_le).algebraMap_toAlgebra,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_inclusion, coe_adjoin_algebraMap]
  conv => enter [1, 2, 1, 2, 2]; rw [← num_div_denom (generator E)]
  rw [mul_div_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero), Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_mul, map_C, map_C, Polynomial.map_map, Polynomial.map_map]
  rfl

end
end RatFunc.Luroth

#print axioms RatFunc.Luroth.Q₀_mul_Φ
