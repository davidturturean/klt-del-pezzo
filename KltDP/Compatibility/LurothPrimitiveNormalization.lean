/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu

Compatible port of the original arbitrary-field Lüroth proof, official
Mathlib commit 59e84018b299993f5d4ca6d8cb4012b08bc55241,
Mathlib/FieldTheory/RatFunc/Luroth.lean. Frozen source SHA256:
ed03b3d45046b546268647434d4aca96f4b6925d995ef7172b6e6d37bd5ca82f.
-/
import KltDP.Compatibility.LurothGenerator
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! The actual integer normalization and primitive part of the original
minimal polynomial; no extension-degree result or Lüroth conclusion is used. -/

variable {K : Type*} [Field K]
open IntermediateField

namespace RatFunc.Luroth
noncomputable section

open _root_.IntermediateField.algebraAdjoinAdjoin Polynomial
open scoped Polynomial.Bivariate
variable {E : IntermediateField K (RatFunc K)}

variable (E) in
/-- The integer normalization of `φ` as a bivariate polynomial. -/
abbrev Φ' : K[X][Y] :=
  IsLocalization.integerNormalization (nonZeroDivisors K[X]) ((φ E).map (algebraMap E (RatFunc K)))

lemma Φ'_ne_zero (h : E ≠ ⊥) : Φ' E ≠ 0 :=
  IsFractionRing.integerNormalization_eq_zero_iff.not.mpr (map_ne_zero (φ_ne_zero h))

variable (E) in
/-- A polynomial `b` that satisfies `b * φ = Φ'`. -/
def b : K[X] :=
  (IsLocalization.integerNormalization_spec (nonZeroDivisors K[X])
    ((φ E).map (algebraMap E (RatFunc K)))).choose

lemma b_ne_zero : b E ≠ 0 :=
  nonZeroDivisors.ne_zero <| (IsLocalization.integerNormalization_spec _
    ((φ E).map (algebraMap ..))).choose.property

lemma Φ'_map :
    (Φ' E).map (algebraMap K[X] (RatFunc K)) = (b E) • (φ E).map (algebraMap ..) := by
  ext i
  rw [coeff_map, coeff_smul]
  exact (IsLocalization.integerNormalization_spec _
    ((φ E).map (algebraMap ..))).choose_spec i

variable (E) in
open scoped Classical in
/-- A rational function `c` that satisfies `c * φ = Φ`. This is `ν₀(x)` in Cohn's notation. -/
abbrev c : (RatFunc K) :=
  (algebraMap K[X] (RatFunc K) (Φ' E).content)⁻¹ * (algebraMap K[X] (RatFunc K) (b E))

open scoped Classical in
lemma c_ne_zero (h : E ≠ ⊥) : c E ≠ 0 :=
  mul_ne_zero_iff.mpr ⟨inv_ne_zero <| (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr <|
    content_eq_zero_iff.not.mpr (Φ'_ne_zero h),
  (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr b_ne_zero⟩

variable (E) in
open scoped Classical in
/-- The primitive part of `Φ'`. -/
abbrev Φ : K[X][Y] := (Φ' E).primPart

/-- We have `c * φ = Φ` as polynomials with coefficients in `Ratfunc K`. See Equation
  (11.3.5) in Cohn's proof. -/
lemma C_c_mul_φ (h : E ≠ ⊥) :
    Polynomial.C (c E) * (φ E).map (algebraMap E (RatFunc K)) = (Φ E).map (algebraMap ..) := by
  classical
  rw [map_mul, mul_assoc]
  conv =>
    enter [1, 2]
    rw [← Polynomial.smul_eq_C_mul, algebraMap_smul, ← Φ'_map, eq_C_content_mul_primPart (Φ' E)]
  rw [Polynomial.map_mul, map_C, ← mul_assoc, ← C_mul, inv_mul_cancel₀, map_one, one_mul]
  · rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff]
    exact Φ'_ne_zero h

lemma Φ_natDegree_eq_φ_natDegree (h : E ≠ ⊥) : (Φ E).natDegree = (φ E).natDegree := by
  rw [← natDegree_map_eq_of_injective (algebraMap_injective K), ← C_c_mul_φ h,
    natDegree_mul (C_ne_zero.mpr (c_ne_zero h)) (map_ne_zero (φ_ne_zero h)), natDegree_C,
    natDegree_map, zero_add]

lemma Φ_coeff_φ_natDegree (h : E ≠ ⊥) :
    algebraMap K[X] (RatFunc K) ((Φ E).coeff (φ E).natDegree) = c E := by
  have := congr($(C_c_mul_φ h).coeff (φ E).natDegree)
  rw [coeff_C_mul, coeff_map, coeff_map, coeff_natDegree, IntermediateField.algebraMap_apply,
    φ_monic h, OneMemClass.coe_one, mul_one] at this
  exact this.symm

lemma c_denom (h : E ≠ ⊥) : (c E).denom = 1 := by
  rw [← Φ_coeff_φ_natDegree h]
  exact denom_algebraMap _

lemma Φ_coeff_φ_natDegree' (h : E ≠ ⊥) :
    (Φ E).coeff (φ E).natDegree = (c E).num := by
  apply algebraMap_injective
  rw [Φ_coeff_φ_natDegree h]
  conv_lhs => rw [← num_div_denom (c E), c_denom h, map_one, div_one]

lemma Φ_coeff_φ_natDegree_ne_zero (h : E ≠ ⊥) :
    (Φ E).coeff (φ E).natDegree ≠ 0 := by
  rw [Φ_coeff_φ_natDegree' h]
  exact num_ne_zero (c_ne_zero h)

lemma Φ_coeff_generatorIndex (h : E ≠ ⊥) :
    algebraMap K[X] (RatFunc K) ((Φ E).coeff (generatorIndex h)) =
    algebraMap K[X] (RatFunc K) (c E).num * generator E := by
  have := congr($(C_c_mul_φ h).coeff (generatorIndex h))
  rw [coeff_map, coeff_C_mul, coeff_map, IntermediateField.algebraMap_apply,
    ← num_div_denom (c E), c_denom h, map_one, div_one] at this
  rw [generator_eq_coeff h]
  exact this.symm

lemma Φ_coeff_generatorIndex_ne_zero (h : E ≠ ⊥) :
    (Φ E).coeff (generatorIndex h) ≠ 0 := by
  apply_fun algebraMap K[X] (RatFunc K)
  rw [map_zero, Φ_coeff_generatorIndex h]
  exact mul_ne_zero_iff.mpr ⟨algebraMap_ne_zero (num_ne_zero (c_ne_zero h)), generator_ne_zero h⟩

lemma generator_denom_dvd_c_num (h : E ≠ ⊥) : (g E) ∣ (c E).num := by
  rw [denom_dvd (num_ne_zero (c_ne_zero h))]
  use (Φ E).coeff (generatorIndex h)
  rw [Φ_coeff_generatorIndex h,
    mul_div_cancel_left₀ _ (algebraMap_ne_zero (num_ne_zero (c_ne_zero h)))]

lemma Φ_ne_zero (h : E ≠ ⊥) : Φ E ≠ 0 := by
  intro H
  have := Φ_coeff_φ_natDegree' h ▸ congr($(H).coeff (φ E).natDegree)
  rw [coeff_zero] at this
  exact num_ne_zero (c_ne_zero h) this

end
end RatFunc.Luroth

#print axioms RatFunc.Luroth.C_c_mul_φ
#print axioms RatFunc.Luroth.Φ_ne_zero
