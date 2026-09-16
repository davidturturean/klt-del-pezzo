/-
Copyright (c) 2025 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sihan Su, Wan Lin, Xiaoyang Su
-/
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.List.Indexes
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# An integral map from one fewer polynomial variable

This file reuses the variable-elimination construction from
`Mathlib/RingTheory/NoetherNormalization.lean` at Mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (Lean 4.19.0).
The upstream source SHA-256 is
`3af1743f2df361237e5a91be41d55748dbee32adbdc67ce87b412f2cc928a194`.

Source:
https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/RingTheory/NoetherNormalization.lean

The copied construction is placed in `KltDP.Compatibility.NoetherNormalizationDrop`;
its auxiliary `T1` is made private. The other proof bodies are unchanged.
The public existence theorem below exposes the one-variable decrease that the
upstream private `hom2` construction already proves. It asserts integrality of
an actual algebra map, with no injectivity or dimension conclusion.
-/

namespace KltDP.Compatibility

open Polynomial MvPolynomial Ideal BigOperators Nat RingHom List

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

namespace NoetherNormalizationDrop

section equivT

/-- `up` is defined as `2 + f.totalDegree`. Any big enough number would work. -/
local notation3 "up" => 2 + f.totalDegree

variable {f v} in
private lemma lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  intro l h
  rw [mem_ofFn] at h
  obtain ⟨y, rfl⟩ := h
  exact vlt y

/-- `r` maps `(i : Fin (n + 1))` to `up ^ i`. -/
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- We construct an algebra map `T1 f c` which maps `X_i` into `X_i + c • X_0 ^ r_i` when `i ≠ 0`
and `X_0` to `X_0`. -/
private noncomputable abbrev T1 (c : k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

private lemma t1_comp_t1_neg (c : k) : (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

/- `T1 f 1` leads to an algebra equiv `T f`. -/
private noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (t1_comp_t1_neg f 1) (by simpa using t1_comp_t1_neg f (-1))

private lemma sum_r_mul_neq (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (neq : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine neq <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.coe_cast, mul_comm, sum_ofFn] using h

private lemma degreeOf_zero_t {a : k} (ha : a ≠ 0) : ((T f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _  _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

/- `T` maps different monomials of `f` to polynomials with different degrees in `X_0`. -/
private lemma degreeOf_t_neq_of_neq (hv : v ∈ f.support) (hw : w ∈ f.support) (neq : v ≠ w) :
    (T f <| monomial v <| coeff v f).degreeOf 0 ≠
    (T f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hv, degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_neq f v w (fun i ↦ ?_) (fun i ↦ ?_) neq <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i)) (by omega)

private lemma leadingCoeff_finSuccEquiv_t  :
    (finSuccEquiv k n ((T f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

/- `T` maps `f` into some polynomial in `X_0` such that the leading coefficient is invertible. -/
private lemma T_leadingcoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (T f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((T f) (h x))).degree <
      (finSuccEquiv k n ((T f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_t_neq_of_neq f _ _ h1 vin <| ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n ((T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((T f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((T f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_diff_singleton vin h]
  rw [leadingCoeff_finSuccEquiv_t] at coeff
  simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

end equivT

section intmaps

variable (I : Ideal (MvPolynomial (Fin (n + 1)) k))

/- `hom1` is a homomorphism from `k[X_0,...X_{n-1}]` to `k[X_1,...X_n][X]/φ(T(I))`,
where `φ` is the isomorphism from `k[X_0,...X_{n-1}]` to `k[X_1,...X_n][X]`. -/
private noncomputable abbrev hom1 : MvPolynomial (Fin n) k →ₐ[MvPolynomial (Fin n) k]
    (MvPolynomial (Fin n) k)[X] ⧸ (I.map <| T f).map (finSuccEquiv k n) :=
  (Quotient.mkₐ (MvPolynomial (Fin n) k) (map (finSuccEquiv k n) (map (T f) I))).comp
  (Algebra.ofId (MvPolynomial (Fin n) k) ((MvPolynomial (Fin n) k)[X]))

/- `hom1 f I` is integral. -/
private lemma hom1_isIntegral (fne : f ≠ 0) (fi : f ∈ I): (hom1 f I).IsIntegral := by
  obtain u := T_leadingcoeff_isUnit f fne
  exact (monic_of_isUnit_leadingCoeff_inv_smul u).quotient_isIntegral <|
    Submodule.smul_of_tower_mem _ u.unit⁻¹.val <| mem_map_of_mem _ <| mem_map_of_mem _ fi

/- `eqv1` is the isomorphism from `k[X_1,...X_n][X]/φ(T(I))`
to `k[X_0,...,X_n]/T(I)`, induced by `φ`. -/
private noncomputable abbrev eqv1 :
    ((MvPolynomial (Fin n) k)[X] ⧸ (I.map (T f)).map (finSuccEquiv k n)) ≃ₐ[k]
    MvPolynomial (Fin (n + 1)) k ⧸ I.map (T f) := quotientEquivAlg
  ((I.map (T f)).map (finSuccEquiv k n)) (I.map (T f)) (finSuccEquiv k n).symm <| by
  set g := (finSuccEquiv k n)
  have : g.symm.toRingEquiv.toRingHom.comp g = RingHom.id _ :=
    g.toRingEquiv.symm_toRingHom_comp_toRingHom
  calc
    _ = Ideal.map ((RingHom.id _).comp <| T f) I := by rw [id_comp, Ideal.map_coe]
    _ = (I.map (T f)).map (RingHom.id _)  := by simp only [← Ideal.map_map, Ideal.map_coe]
    _ = (I.map (T f)).map (g.symm.toAlgHom.toRingHom.comp g) :=
      congrFun (congrArg Ideal.map this.symm) (I.map (T f))
    _ = _ := by simp [← Ideal.map_map, Ideal.map_coe]

/- `eqv2` is the isomorphism from `k[X_0,...,X_n]/T(I)` into `k[X_0,...,X_n]/I`,
induced by `T`. -/
private noncomputable abbrev eqv2 :
    (MvPolynomial (Fin (n + 1)) k ⧸ I.map (T f)) ≃ₐ[k] MvPolynomial (Fin (n + 1)) k ⧸ I
  := quotientEquivAlg (R₁ := k) (I.map (T f)) I (T f).symm <| by
  calc
    _ = I.map ((T f).symm.toRingEquiv.toRingHom.comp (T f)) := by
      have : (T f).symm.toRingEquiv.toRingHom.comp (T f) = RingHom.id _ :=
        RingEquiv.symm_toRingHom_comp_toRingHom _
      rw [this, Ideal.map_id]
    _ = _ := by
      rw [← Ideal.map_map, Ideal.map_coe, Ideal.map_coe]
      exact congrArg _ rfl

/- `hom2` is the composition of maps above, from `k[X_0,...X_(n-1)]` to `k[X_0,...X_n]/I`. -/
private noncomputable def hom2 : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k ⧸ I :=
  (eqv2 f I).toAlgHom.comp ((eqv1 f I).toAlgHom.comp ((hom1 f I).restrictScalars k))

/- `hom2 f I` is integral. -/
private lemma hom2_isIntegral (fne : f ≠ 0) (fi : f ∈ I): (hom2 f I).IsIntegral :=
  ((hom1_isIntegral f I fne fi).trans _ _ <| isIntegral_of_surjective _ (eqv1 f I).surjective).trans
    _ _ <| isIntegral_of_surjective _ (eqv2 f I).surjective

end intmaps
end NoetherNormalizationDrop

/-- A quotient of a polynomial ring in `n + 1` variables by a nonzero ideal
receives an integral algebra map from a polynomial ring in `n` variables.
The ideal may be the unit ideal; injectivity of the map is not asserted. -/
theorem exists_integral_drop_variables (K : Type*) [Field K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (hI : I ≠ ⊥) :
    ∃ f : MvPolynomial (Fin n) K →ₐ[K] (MvPolynomial (Fin (n + 1)) K ⧸ I),
      f.IsIntegral := by
  obtain ⟨p, hp, hpne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact ⟨NoetherNormalizationDrop.hom2 p I,
    NoetherNormalizationDrop.hom2_isIntegral p I hpne hp⟩

end KltDP.Compatibility
