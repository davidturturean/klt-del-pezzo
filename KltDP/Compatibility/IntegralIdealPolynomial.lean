/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Integral polynomial equations over an actual ideal

Bounded port of official Mathlib
`RingTheory/IntegralClosure/Algebra/Ideal.lean` at revision
`5aedf732b6987e8c26ab3c9ebc855314f82b045f`, whole-file SHA-256
`3acd66ff2b7e8b4295d04f4a8331bea898fd60abe2021c683a37a626379d006b`.

An element of an extended ideal in an integral algebra satisfies an actual
monic polynomial whose nonleading coefficients belong to the original
ideal. The stronger power-of-ideal statement is proved by homogenizing in
an auxiliary polynomial variable. Newer syntax and theorem names are
adapted to the unchanged Lean 4.19 Mathlib pin.
-/

noncomputable section

namespace KltDP.Compatibility.IntegralIdealPolynomial

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem coeff_mem_pow_of_mem_adjoin_C_mul_X
    {I : Ideal R} {P : R[X]} (hP : P ∈ Algebra.adjoin R { C r * X | r ∈ I }) (i : ℕ) :
    P.coeff i ∈ I ^ i := by
  induction hP using Algebra.adjoin_induction generalizing i with
  | mem x hx =>
    obtain ⟨r, hrI, rfl⟩ := hx
    simp +contextual [coeff_X, apply_ite, hrI, @eq_comm _ 1]
  | algebraMap r => simp +contextual [coeff_C, apply_ite]
  | add x y _ _ hx hy =>
    simpa only [coeff_add] using (Ideal.add_mem (I ^ i) (hx i) (hy i))
  | mul x y _ _ hx hy =>
    rw [coeff_mul]
    refine Submodule.sum_mem _ (fun ⟨j₁, j₂⟩ hj => ?_)
    obtain rfl : j₁ + j₂ = i := by simpa using hj
    exact pow_add I j₁ j₂ ▸ Ideal.mul_mem_mul (hx _) (hy _)

local instance polynomialAlgebra : Algebra R[X] S[X] := Polynomial.algebra R S

theorem exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral
    {I : Ideal R} {x : S}
    (hx : IsIntegral (Algebra.adjoin R { C r * X | r ∈ I }) (C x * X)) :
    ∃ p : R[X], p.Monic ∧ aeval x p = 0 ∧ ∀ i, p.coeff i ∈ I ^ (p.natDegree - i) := by
  cases subsingleton_or_nontrivial R
  · use 0
    simp [Monic, Subsingleton.elim (α := R) 0 1]
  obtain ⟨p, hp, e⟩ := hx
  let q : R[X] := ∑ i ∈ Finset.range (p.natDegree + 1),
    C ((p.coeff i).1.coeff (p.natDegree - i)) * X ^ i
  have hq : q.natDegree = p.natDegree := by
    refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_sum_le_of_forall_le _ _ ?_) ?_
    · exact fun i hi => (natDegree_C_mul_X_pow_le _ _).trans
        (by simpa [Nat.lt_succ_iff] using hi)
    · simp [q, hp]
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [← hq] using (show q.coeff p.natDegree = 1 by simp [q, hp])
  · replace e := congrArg (fun t : S[X] => t.coeff p.natDegree) e
    simp only [eval₂_eq_sum_range, finset_sum_coeff, coeff_zero] at e
    simp only [q, map_sum, map_mul, aeval_C, map_pow, aeval_X]
    refine (Finset.sum_congr rfl fun i hi => ?_).trans e
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
    rw [mul_pow, mul_left_comm, ← map_pow, coeff_C_mul, coeff_mul_X_pow',
      if_pos hi, mul_comm]
    simp [Subalgebra.algebraMap_eq, Polynomial.algebraMap_def]
  · rw [hq]
    simp [q, apply_ite, coeff_mem_pow_of_mem_adjoin_C_mul_X (p.coeff _).2]

theorem exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map [Algebra.IsIntegral R S]
    {I : Ideal R} {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    ∃ p : R[X], p.Monic ∧ aeval x p = 0 ∧ ∀ i, p.coeff i ∈ I ^ (p.natDegree - i) := by
  let A : Subalgebra R R[X] := Algebra.adjoin R { C r * X | r ∈ I }
  refine exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral ?_
  induction hx using Submodule.span_induction with
  | zero => simp [isIntegral_zero]
  | add x y _ _ hx hy => simpa [add_mul] using hx.add hy
  | mem x h =>
    obtain ⟨x, hx, rfl⟩ := h
    have hint := isIntegral_algebraMap (R := A) (A := S[X])
      (x := ⟨C x * X, Algebra.subset_adjoin ⟨x, hx, rfl⟩⟩)
    change IsIntegral A ((C x * X).map (algebraMap R S)) at hint
    simpa only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X] using hint
  | smul a x _ hx =>
    simp only [smul_eq_mul, map_mul, mul_assoc]
    refine IsIntegral.mul ?_ hx
    exact ((Algebra.IsIntegral.isIntegral (R := R) a).map
      (IsScalarTower.toAlgHom R S S[X])).tower_top

/-- An element of the actual extended ideal has a monic equation with
all nonleading coefficients in the original ideal. -/
theorem exists_monic_aeval_eq_zero_forall_mem_of_mem_map [Algebra.IsIntegral R S]
    {I : Ideal R} {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    ∃ p : R[X], p.Monic ∧ aeval x p = 0 ∧ ∀ i ≠ p.natDegree, p.coeff i ∈ I := by
  obtain ⟨p, hp, e, h⟩ := exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map hx
  refine ⟨p, hp, e, fun i hi => ?_⟩
  obtain hi | hi := lt_or_gt_of_ne hi
  · exact Ideal.pow_le_self (by omega) (h _)
  · simp [coeff_eq_zero_of_natDegree_lt hi]

end KltDP.Compatibility.IntegralIdealPolynomial
