/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu

Compatible port of the algebraicity and degree part of
Mathlib/FieldTheory/RatFunc/IntermediateField.lean, official commit
59e84018b299993f5d4ca6d8cb4012b08bc55241. Every field is retained;
new notation is expanded and the pinned adjoin inclusion API is reused.
-/
import KltDP.Compatibility.RatFuncPolynomialSupport
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Algebraic.Integral

/-! This first block does not depend on irreducibility or a Lüroth theorem. -/

variable {K : Type*} [Field K]

namespace RatFunc

open IntermediateField algebraAdjoinAdjoin Polynomial Algebra

noncomputable section

variable (f : (RatFunc K))

/-- The pinned simple-adjoin inclusion is the original subtype inclusion. -/
private theorem coe_adjoin_algebraMap (x : Algebra.adjoin K {f}) :
    ((algebraMap (Algebra.adjoin K {f}) K⟮f⟯ x : K⟮f⟯) : RatFunc K) = x := rfl

theorem adjoin_X : K⟮(X : (RatFunc K))⟯ = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩

theorem IntermediateField.adjoin_X (E : IntermediateField K (RatFunc K)) :
    E⟮(X : (RatFunc K))⟯ = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, RatFunc.adjoin_X]
  simp

/-- The equivalence between `E⟮X⟯` and `(RatFunc K)` as `E`-algebras. -/
noncomputable def IntermediateField.adjoinXEquiv (E : IntermediateField K (RatFunc K)) :
    E⟮(X : (RatFunc K))⟯ ≃ₐ[E] (RatFunc K) :=
  (equivOfEq (adjoin_X E)).trans topEquiv

/-- The minimal polynomial of `X` over `K⟮f⟯`. It is defined as `f.num - f * f.denom`, viewed
as a polynomial with coefficients in `A`, where `A` is a `(Algebra.adjoin K {f})`-algebra. -/
noncomputable abbrev minpolyX (A : Type*) [CommRing A] [Algebra K A] [Algebra (Algebra.adjoin K {f}) A] : A[X] :=
  f.num.map (algebraMap K A) -
  Polynomial.C (algebraMap (Algebra.adjoin K {f}) A (⟨f, self_mem_adjoin_singleton K f⟩ : (Algebra.adjoin K {f}))) *
    f.denom.map (algebraMap K A)

theorem minpolyX_map (A : Type*) [CommRing A] [Algebra K A] [Algebra (Algebra.adjoin K {f}) A]
    (B : Type*) [CommRing B] [Algebra K B] [Algebra (Algebra.adjoin K {f}) B] [Algebra A B] [IsScalarTower K A B]
    [IsScalarTower (Algebra.adjoin K {f}) A B] : (f.minpolyX A).map (algebraMap A B) = f.minpolyX B := by
  simp [minpolyX, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

@[simp]
theorem C_minpolyX (x : K) : (C x).minpolyX K⟮C x⟯ = 0 := by
  simp [minpolyX, sub_eq_zero, Subtype.ext_iff, coe_adjoin_algebraMap]

theorem minpolyX_aeval_X : (f.minpolyX K⟮f⟯).aeval (X : (RatFunc K)) = 0 := by
  simp only [minpolyX, map_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C,
    IntermediateField.algebraMap_apply, coe_adjoin_algebraMap]
  nth_rw 2 [← num_div_denom f]
  rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _

theorem eq_C_of_minpolyX_coeff_eq_zero
  (hf : (f.minpolyX K⟮f⟯).coeff f.denom.natDegree = (0 : (RatFunc K))) : ∃ c, f = C c := by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀, eq_div_iff ((_root_.map_ne_zero C).mpr
    (leadingCoeff_ne_zero.mpr f.denom_ne_zero)), eq_comm]
  simpa [sub_eq_zero] using hf

theorem minpolyX_eq_zero_iff : (f.minpolyX K⟮f⟯) = 0 ↔ ∃ c, f = C c :=
  ⟨fun h ↦ f.eq_C_of_minpolyX_coeff_eq_zero (by simp [h]), by rintro ⟨c, rfl⟩; simp⟩

theorem isAlgebraic_adjoin_simple_X (hf : ¬∃ c, f = C c) : IsAlgebraic K⟮f⟯ (X : (RatFunc K)) :=
  ⟨f.minpolyX K⟮f⟯, fun H ↦ hf (f.minpolyX_eq_zero_iff.mp H), f.minpolyX_aeval_X⟩

theorem isAlgebraic_adjoin_simple_X' (hf : ¬∃ c, f = C c) :
    Algebra.IsAlgebraic K⟮f⟯ (RatFunc K) := by
  have : Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮(X : (RatFunc K))⟯ :=
    isAlgebraic_adjoin_simple <| isAlgebraic_iff_isIntegral.mp <| f.isAlgebraic_adjoin_simple_X hf
  exact (IntermediateField.adjoinXEquiv K⟮f⟯).isAlgebraic

theorem natDegree_denom_le_natDegree_minpolyX (hf : ¬∃ c, f = C c) :
    f.denom.natDegree ≤ (f.minpolyX K⟮f⟯).natDegree :=
  le_natDegree_of_ne_zero fun H ↦ hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

theorem natDegree_num_le_natDegree_minpolyX (hf : ¬∃ c, f = C c) :
    f.num.natDegree ≤ (f.minpolyX K⟮f⟯).natDegree := by
  have f_ne_zero : f ≠ 0 := by
    rintro rfl
    exact hf ⟨0, (RingHom.map_zero C).symm⟩
  apply le_natDegree_of_ne_zero
  intro H
  replace H := congr($(H).val)
  simp only [coeff_sub, coeff_map, coeff_natDegree, coeff_C_mul, AddSubgroupClass.coe_sub,
    SubalgebraClass.coe_algebraMap, algebraMap_eq_C, MulMemClass.coe_mul, coe_adjoin_algebraMap,
    ZeroMemClass.coe_zero] at H
  rw [sub_eq_zero, ← mul_right_inj' (inv_ne_zero f_ne_zero), ← mul_assoc, inv_mul_cancel₀ f_ne_zero,
    one_mul, ← eq_div_iff <| (_root_.map_ne_zero C).mpr <| Polynomial.leadingCoeff_ne_zero.mpr
    (num_ne_zero f_ne_zero), ← inv_inj, inv_inv, ← map_div₀, ← map_inv₀] at H
  exact hf ⟨_, H⟩

theorem natDegree_minpolyX :
    (f.minpolyX K⟮f⟯).natDegree = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    simp
  apply le_antisymm
  · have hgen : algebraMap (Algebra.adjoin K {f}) K⟮f⟯
        ⟨f, self_mem_adjoin_singleton K f⟩ ≠ 0 := by
      intro H
      have hval : f = 0 := congrArg (fun z : K⟮f⟯ ↦ (z : RatFunc K)) H
      exact hf ⟨0, by simpa only [map_zero] using hval⟩
    have : (f.minpolyX K⟮f⟯).natDegree ≤ _ := natDegree_sub_le _ _
    rw [natDegree_map, natDegree_C_mul hgen, natDegree_map] at this
    exact this
  · exact max_le (natDegree_num_le_natDegree_minpolyX f hf) <| le_natDegree_of_ne_zero
      fun H ↦ hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

theorem transcendental_of_ne_C (hf : ¬∃ c, f = C c) : Transcendental K f := by
  intro H
  have := isAlgebraic_adjoin_simple H.isIntegral
  have tr : Algebra.Transcendental K (RatFunc K) := by infer_instance
  rw [Algebra.transcendental_iff_not_isAlgebraic] at tr
  exact tr <| Algebra.IsAlgebraic.trans _ _ _ (alg := f.isAlgebraic_adjoin_simple_X' hf)

theorem IntermediateField.isAlgebraic_X {E : IntermediateField K (RatFunc K)} (hE : E ≠ ⊥) :
    IsAlgebraic E (X : (RatFunc K)) := by
  rw [ne_eq, ← le_bot_iff, SetLike.not_le_iff_exists] at hE
  obtain ⟨f, hf₁, hf₂⟩ := hE
  exact IsAlgebraic.tower_top_of_subalgebra_le (adjoin_simple_le_iff.mpr hf₁) <|
    f.isAlgebraic_adjoin_simple_X (by rintro ⟨c, rfl⟩; exact hf₂ ⟨c, rfl⟩)


end
end RatFunc

#print axioms RatFunc.isAlgebraic_adjoin_simple_X
#print axioms RatFunc.natDegree_minpolyX
#print axioms RatFunc.transcendental_of_ne_C
#print axioms RatFunc.IntermediateField.isAlgebraic_X
