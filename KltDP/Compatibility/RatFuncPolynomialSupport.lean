/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, María Inés de Frutos-Fernández, Filippo A. E. Nuccio

Bounded port of Mathlib/FieldTheory/RatFunc/AsPolynomial.lean from official
commit 59e84018b299993f5d4ca6d8cb4012b08bc55241, lines 83-86, 127-133,
and 257-265. The domain and field scopes are unchanged.
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Polynomial.Tower

/-! Only the missing rational-function lemmas used by the intermediate-field
proof are included. The evaluation proof reuses the pinned tower API. -/

noncomputable section
open scoped Polynomial

namespace RatFunc

variable {K : Type*}

section Domain
variable [CommRing K] [IsDomain K]

@[simp]
theorem aeval_X_left_eq_algebraMap (p : K[X]) :
    p.aeval (X : RatFunc K) = algebraMap K[X] (RatFunc K) p := by
  rw [← algebraMap_X, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_X_left_apply]

lemma transcendental_X : Transcendental K (X : RatFunc K) := by
  rw [← RatFunc.algebraMap_X, transcendental_algebraMap_iff (algebraMap_injective K)]
  exact Polynomial.transcendental_X K

instance transcendental : Algebra.Transcendental K (RatFunc K) := ⟨X, transcendental_X⟩

end Domain

section Field
variable [Field K]

theorem eq_C_iff (f : RatFunc K) :
    (∃ c, f = C c) ↔ f.num.natDegree = 0 ∧ f.denom.natDegree = 0 := by
  refine ⟨by rintro ⟨c, rfl⟩; simp, ?_⟩
  rw [Polynomial.natDegree_eq_zero, Polynomial.natDegree_eq_zero]
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  use a / b
  rw [← num_div_denom f, ← ha, ← hb, algebraMap_C, algebraMap_C, map_div₀]

end Field
end RatFunc

#print axioms RatFunc.aeval_X_left_eq_algebraMap
#print axioms RatFunc.transcendental_X
#print axioms RatFunc.eq_C_iff
