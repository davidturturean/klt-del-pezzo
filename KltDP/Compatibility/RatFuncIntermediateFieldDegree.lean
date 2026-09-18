/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu

Compatible port of the irreducibility and degree-of-extension part of
Mathlib/FieldTheory/RatFunc/IntermediateField.lean at official commit
59e84018b299993f5d4ca6d8cb4012b08bc55241, original lines 124-174.
-/
import KltDP.Compatibility.RatFuncIntermediateFieldBasic
import KltDP.Compatibility.BivariateSwap
import KltDP.Compatibility.TranscendentalAdjoinPolynomial
import KltDP.Compatibility.PrimitiveLinearPolynomial
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.Tactic.Convert

/-! The original arbitrary field, original simple adjoin, polynomial and
extension-degree conclusions are retained. Pinned normalized GCD data is
chosen from the proved UFD instance rather than introduced as a premise. -/

noncomputable section

variable {K : Type*} [Field K]

namespace RatFunc
open _root_.IntermediateField _root_.IntermediateField.algebraAdjoinAdjoin Polynomial Algebra
open scoped Polynomial
variable (f : RatFunc K)

theorem irreducible_minpolyX' (hf : ¬∃ c, f = C c) : Irreducible (f.minpolyX (Algebra.adjoin K {f})) := by
  let e := Polynomial.algEquivOfTranscendental K f (f.transcendental_of_ne_C hf)
  let φ : K[X][X] := f.num.map (algebraMap ..) -
    Polynomial.C Polynomial.X * f.denom.map (algebraMap ..)
  have φ_map : φ.mapEquiv e.toRingEquiv = (f.minpolyX (Algebra.adjoin K {f})) := by
    simp only [algebraMap_eq, map_sub, mapEquiv_apply,
      AlgEquiv.toRingEquiv_toRingHom, algEquivOfTranscendental_coe, Polynomial.map_map, map_mul,
      map_C, RingHom.coe_coe, aeval_X, e, φ]
    congr 2 <;> ext <;> simp [Polynomial.algEquivOfTranscendental]
  rw [← φ_map, MulEquiv.irreducible_iff]
  have : φ = Bivariate.swap
      (Polynomial.C f.num - Polynomial.X * Polynomial.C f.denom) := by
    change f.num.map Polynomial.C -
        Polynomial.C Polynomial.X * f.denom.map Polynomial.C = _
    rw [map_sub, map_mul, Bivariate.swap_C, Bivariate.swap_Y, Bivariate.swap_C]
  rw [this, MulEquiv.irreducible_iff]
  convert
    irreducible_C_mul_X_add_C (neg_ne_zero.mpr f.denom_ne_zero)
      ((IsCoprime.neg_right_iff _ _).mpr f.isCoprime_num_denom).symm.isRelPrime using 1
  rw [add_comm, X_mul_C, map_neg, neg_mul]
  exact sub_eq_add_neg (Polynomial.C f.num) (Polynomial.C f.denom * Polynomial.X)

theorem irreducible_minpolyX (hf : ¬∃ c, f = C c) : Irreducible (f.minpolyX K⟮f⟯) := by
  have : UniqueFactorizationMonoid (Algebra.adjoin K {f}) :=
    KltDP.Compatibility.TranscendentalAdjoinPolynomial.uniqueFactorizationMonoid_adjoin
      (f.transcendental_of_ne_C hf)
  letI : NormalizedGCDMonoid (Algebra.adjoin K {f}) := Classical.choice inferInstance
  rw [← f.minpolyX_map (Algebra.adjoin K {f}) K⟮f⟯,
    ← IsPrimitive.irreducible_iff_irreducible_map_fraction_map]
  · exact f.irreducible_minpolyX' hf
  · apply (f.irreducible_minpolyX' hf).isPrimitive
    intro H
    have := natDegree_map_le (f := algebraMap (Algebra.adjoin K {f}) K⟮f⟯) (p := f.minpolyX (Algebra.adjoin K {f}))
    rw [f.minpolyX_map (Algebra.adjoin K {f}) K⟮f⟯, H, nonpos_iff_eq_zero, f.natDegree_minpolyX,
      Nat.max_eq_zero_iff, ← f.eq_C_iff] at this
    exact hf this

theorem finrank_eq_max_natDegree :
    Module.finrank K⟮f⟯ (RatFunc K) = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    rw [adjoin_simple_eq_bot_iff.mpr (show C c ∈ ⊥ from ⟨c, rfl⟩), finrank_bot',
      Module.finrank_of_not_finite fun H ↦ Algebra.transcendental_iff_not_isAlgebraic.mp
      transcendental <| Algebra.IsAlgebraic.of_finite K (RatFunc K)]
    simp
  rw [← (IntermediateField.adjoinXEquiv K⟮f⟯).toLinearEquiv.finrank_eq,
    adjoin.finrank (f.isAlgebraic_adjoin_simple_X hf).isIntegral,
    ← minpoly.eq_of_irreducible (f.irreducible_minpolyX hf) f.minpolyX_aeval_X, mul_comm,
    natDegree_C_mul <| inv_ne_zero <| leadingCoeff_ne_zero.mpr fun H ↦
    hf ((minpolyX_eq_zero_iff f).mp H), natDegree_minpolyX]

end RatFunc

#print axioms RatFunc.irreducible_minpolyX
#print axioms RatFunc.finrank_eq_max_natDegree
