/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu

Compatible port of the original arbitrary-field Lüroth proof, official
Mathlib commit 59e84018b299993f5d4ca6d8cb4012b08bc55241,
Mathlib/FieldTheory/RatFunc/Luroth.lean. Frozen source SHA256:
ed03b3d45046b546268647434d4aca96f4b6925d995ef7172b6e6d37bd5ca82f.
-/
import KltDP.Compatibility.RatFuncIntermediateFieldBasic
import KltDP.Compatibility.BivariateSwap
import Mathlib.Algebra.Polynomial.Lifts

/-! The original minimal polynomial and its selected nonconstant coefficient.
The pinned coefficientwise polynomial-lifting criterion replaces the newer
notMem_map_range spelling. No hypotheses on characteristic are added. -/

variable {K : Type*} [Field K]
open IntermediateField

namespace RatFunc.Luroth
noncomputable section

open _root_.IntermediateField.algebraAdjoinAdjoin Polynomial
open scoped Polynomial.Bivariate
variable {E : IntermediateField K (RatFunc K)}

variable (E) in
/-- The minimal polynomial of `X` with coefficients in `E`. -/
abbrev φ : E[X] := minpoly E (X : (RatFunc K))

lemma φ_ne_zero (h : E ≠ ⊥) : φ E ≠ 0 :=
  minpoly.ne_zero (IntermediateField.isAlgebraic_X h).isIntegral

lemma φ_monic (h : E ≠ ⊥) : (φ E).Monic :=
  minpoly.monic (IntermediateField.isAlgebraic_X h).isIntegral

lemma φ_natDegree (h : E ≠ ⊥) : (φ E).natDegree = Module.finrank E (RatFunc K) := by
  rw [← (IntermediateField.adjoinXEquiv E).toLinearEquiv.finrank_eq,
    adjoin.finrank (IntermediateField.isAlgebraic_X h).isIntegral]

/-- Since `X` is transcendental over `K`, not all coefficients of `φ` can be in `K`. -/
lemma exists_φ_coeff_not_mem (h : E ≠ ⊥) :
    ∃ i, (φ E).coeff i ∉ (algebraMap K E).range := by
  classical
  by_contra hcoeff
  have hcoeff' : ∀ i, (φ E).coeff i ∈ Set.range (algebraMap K E) := by
    intro i
    by_contra hi
    exact hcoeff ⟨i, hi⟩
  obtain ⟨f, hf⟩ := (mem_lifts (φ E)).mp ((lifts_iff_coeff_lifts (φ E)).mpr hcoeff')
  refine transcendental_X ⟨f, ?_, ?_⟩
  · intro hf0
    apply φ_ne_zero h
    rw [← hf, hf0, Polynomial.map_zero]
  · simpa using congrArg (aeval (X : RatFunc K)) hf

/-- A choice of coefficient index `i` such that `φ.coeff i` is not in `K`. -/
def generatorIndex (h : E ≠ ⊥) : ℕ :=
  (exists_φ_coeff_not_mem h).choose

variable (E) in
open scoped Classical in
/-- A choice of a generator for Lüroth's theorem, see `Luroth.eq_adjoin_generator`. -/
def generator : (RatFunc K) :=
  if h : E = ⊥ then 0 else (φ E).coeff (generatorIndex h)

lemma generator_eq_zero (h : E = ⊥) : generator E = 0 :=
  by simp [generator, h]

lemma generator_eq_coeff (h : E ≠ ⊥) : generator E = (φ E).coeff (generatorIndex h) :=
  by simp [generator, h]

lemma generator_mem : generator E ∈ E := by
  by_cases h : E = ⊥
  · rw [generator_eq_zero h]
    exact E.zero_mem
  · rw [generator_eq_coeff h]
    exact SetLike.coe_mem _

lemma generator_spec (h : E ≠ ⊥) : generator E ∉ (algebraMap K (RatFunc K)).range := by
  rw [generator_eq_coeff h]
  intro ⟨f, hf⟩
  exact (exists_φ_coeff_not_mem h).choose_spec ⟨f, by ext; exact hf⟩

lemma generator_ne_C (h : E ≠ ⊥) : ¬ ∃ c, generator E = C c :=
  fun ⟨c, hc⟩ ↦ generator_spec h ⟨c, (by simpa using hc.symm)⟩

lemma transcendental_generator (h : E ≠ ⊥) : Transcendental K (generator E) :=
  (generator E).transcendental_of_ne_C (generator_ne_C h)

lemma generator_ne_zero (h : E ≠ ⊥) : generator E ≠ 0 :=
  fun H ↦ generator_ne_C h ⟨0, by simp [H]⟩

lemma adjoin_generator_le : K⟮generator E⟯ ≤ E :=
  adjoin_simple_le_iff.mpr generator_mem

variable (E) in
/-- The numerator of the generator. -/
abbrev f : K[X] := (generator E).num

variable (E) in
/-- The denominator of the generator. -/
abbrev g : K[X] := generator E |>.denom

end
end RatFunc.Luroth

#print axioms RatFunc.Luroth.transcendental_generator
#print axioms RatFunc.Luroth.adjoin_generator_le
