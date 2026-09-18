/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
import KltDP.Compatibility.LurothQuotientLift
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The actual quotient is constant: evaluation at a root in an algebraic
closure and the original coprime numerator/denominator force degree zero.
Ported from official Mathlib commit 59e84018b299993f5d4ca6d8cb4012b08bc55241,
Luroth.lean 407-475. No algebraic-closure assumption on the original field
is introduced; its algebraic closure is constructed inside the proof. -/

variable {K : Type*} [Field K]
open IntermediateField

namespace RatFunc.Luroth
noncomputable section
open _root_.IntermediateField.algebraAdjoinAdjoin Polynomial
open scoped Polynomial.Bivariate
variable {E : IntermediateField K (RatFunc K)}

attribute [local instance] Polynomial.algebra in
lemma Q₂_natDegree (h : E ≠ ⊥) : (Q₂ h).natDegree = 0 := by
  -- We have f(X)*g(Y) - g(X)*f(Y) = Q₂(X) * Φ
  -- Assume Q₂ has positive degree, take a root in an algebraic extension
  by_contra H
  apply (generator E).eq_C_iff.not.mp (generator_ne_C h)
  let F := AlgebraicClosure K
  rw [natDegree_eq_zero_iff_degree_le_zero.not, ← degree_map _ (algebraMap K F)] at H
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root ((Q₂ h).map (algebraMap K F)) (fun hzero => H hzero.le)
  -- Evaluate at the root, get that f(α)*g(Y) = g(α)*f(Y)
  rw [IsRoot.def, eval_map_algebraMap] at hα
  have eq :
      (Polynomial.mapRingHom (algebraMap K F)) (g E) * Polynomial.C ((aeval α) (f E)) =
      (Polynomial.mapRingHom (algebraMap K F)) (f E) * Polynomial.C ((aeval α) (g E)) := by
    have := congr(aeval (Polynomial.C α) $(Q₂_mul_Φ h)).symm
    rwa [aeval_mul, ← map_aeval_eq_aeval_map (by ext; simp), hα, map_zero, zero_mul, map_sub,
      aeval_mul, aeval_mul, aeval_C, aeval_C, ← map_aeval_eq_aeval_map (by ext; simp),
      ← map_aeval_eq_aeval_map (by ext; simp), algebraMap_def, coe_mapRingHom, sub_eq_zero,
      ← Polynomial.coe_mapRingHom] at this
  obtain ⟨isUnit₁, isUnit₂⟩ :
      IsUnit (Polynomial.C <| aeval α (f E)) ∧ IsUnit (Polynomial.C <| aeval α (g E)) := by
    rw [Polynomial.isUnit_C, isUnit_iff_ne_zero, Polynomial.isUnit_C, isUnit_iff_ne_zero]
    obtain (H | H) := aeval_ne_zero_of_isCoprime (generator E).isCoprime_num_denom α
    · refine ⟨H, Polynomial.C_injective.ne_iff.mp ?_⟩
      rw [map_zero, ← mul_ne_zero_iff_left <| Polynomial.map_ne_zero <|
        num_ne_zero (generator_ne_zero h)]
      exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (generator E).denom_ne_zero) <|
        Polynomial.C_ne_zero.mpr H
    · refine ⟨Polynomial.C_injective.ne_iff.mp ?_, H⟩
      rw [map_zero, ← mul_ne_zero_iff_left <| Polynomial.map_ne_zero (generator E).denom_ne_zero]
      exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h))) <|
        Polynomial.C_ne_zero.mpr H
  -- obtain contradiction because f and g are coprime
  have isCoprime := IsCoprime.map (generator E).isCoprime_num_denom <|
    Polynomial.mapRingHom (algebraMap K F)
  have : Associated ((f E).mapRingHom (algebraMap K F)) ((g E).mapRingHom (algebraMap K F)) := by
    rw [← associated_mul_isUnit_left_iff isUnit₂, Associated.comm]
    exact ⟨isUnit₁.unit, by simpa⟩
  have hunit₁ := isCoprime.isUnit_of_dvd this.dvd
  have hunit₂ := isCoprime.symm.isUnit_of_dvd this.symm.dvd
  exact ⟨by simpa using (natDegree_eq_zero_of_isUnit hunit₁),
    by simpa using (natDegree_eq_zero_of_isUnit hunit₂)⟩

/-- A constant `Q₃` that satisfies `Q₃ * Φ = θ`. -/
abbrev Q₃ (h : E ≠ ⊥) : K := (Q₂ h).coeff 0

lemma Q₃_map (h : E ≠ ⊥) : Polynomial.C (Q₃ h) = Q₂ h :=
  (eq_C_of_natDegree_eq_zero (Q₂_natDegree h)).symm

/-- Equation (11.3.8) from Cohn's proof, where we view `Q` as a constant. -/
lemma Q₃_mul_Φ (h : E ≠ ⊥) : (Polynomial.C (Q₃ h)).map Polynomial.C * Φ E = θ E := by
  rw [Q₃_map h, Q₂_mul_Φ h]

lemma Φ_natDegree_eq_θ_natDegree (h : E ≠ ⊥) :
    (Φ E).natDegree = (θ E).natDegree := by
  have := congr($(Q₂_mul_Φ h).natDegree)
  rwa [natDegree_mul (Polynomial.map_ne_zero (Q₂_ne_zero h)) (Φ_ne_zero h), natDegree_map,
    Q₂_natDegree h, zero_add] at this

lemma swap_Φ_natDegree_eq_θ_natDegree (h : E ≠ ⊥) :
    (Bivariate.swap (Φ E)).natDegree = (θ E).natDegree := by
  have := congr((Bivariate.swap $(Q₃_mul_Φ h)).natDegree)
  rwa [map_mul, Polynomial.map_C, Bivariate.swap_C_C,
    natDegree_mul (C_ne_zero.mpr (Q₃_map h ▸ Q₂_ne_zero h))
      ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h)),
    natDegree_C, zero_add, swap_θ, natDegree_neg] at this


end
end RatFunc.Luroth

#print axioms RatFunc.Luroth.Q₂_natDegree
#print axioms RatFunc.Luroth.swap_Φ_natDegree_eq_θ_natDegree
