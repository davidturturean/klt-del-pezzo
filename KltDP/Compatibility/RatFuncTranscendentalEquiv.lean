/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import KltDP.Compatibility.TranscendentalAdjoinPolynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Polynomial.Tower

/-!
Port of the original transcendental rational-function equivalence and its
three forward evaluation laws, AsPolynomial.lean 223-245, official commit
59e84018b299993f5d4ca6d8cb4012b08bc55241. The exact original polynomial
adjoin and intermediate field are connected by the pinned fraction-ring
algebra equivalence; no abstract choice of field isomorphism is assumed.
-/

noncomputable section
namespace RatFunc
open _root_.IntermediateField _root_.IntermediateField.algebraAdjoinAdjoin Polynomial
open scoped Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (f : L) (h : Transcendental K f)

/-- Given a transcendental `f : L`, the `K`-algebra isomorphism between `RatFunc K` and `L` given
by sending `X` to `f`. -/
noncomputable def algEquivOfTranscendental : RatFunc K ≃ₐ[K] K⟮f⟯ :=
  IsFractionRing.algEquivOfAlgEquiv (Polynomial.algEquivOfTranscendental K f h)

@[simp]
theorem algEquivOfTranscendental_algebraMap (g : K[X]) :
    algEquivOfTranscendental f h (algebraMap K[X] (RatFunc K) g) =
    aeval (AdjoinSimple.gen K f) g := by
  rw [algEquivOfTranscendental, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change algebraMap (Algebra.adjoin K {f}) K⟮f⟯
      (aeval (⟨f, Algebra.self_mem_adjoin_singleton K f⟩ : Algebra.adjoin K {f}) g) = _
  rw [← Polynomial.aeval_algebraMap_apply]
  rfl

@[simp]
theorem algEquivOfTranscendental_X :
    algEquivOfTranscendental f h (X : RatFunc K) = f := by
  simp [← algebraMap_X, AdjoinSimple.gen]

theorem algEquivOfTranscendental_apply (u : RatFunc K) :
    algEquivOfTranscendental f h u = aeval f u.num / aeval f u.denom := by
  change algebraMap K⟮f⟯ L (algEquivOfTranscendental f h u) = _
  conv_lhs => rw [← num_div_denom u]
  rw [map_div₀, map_div₀, algEquivOfTranscendental_algebraMap,
    algEquivOfTranscendental_algebraMap, ← Polynomial.aeval_algebraMap_apply,
    ← Polynomial.aeval_algebraMap_apply]
  rfl

end RatFunc

#print axioms RatFunc.algEquivOfTranscendental
#print axioms RatFunc.algEquivOfTranscendental_apply
