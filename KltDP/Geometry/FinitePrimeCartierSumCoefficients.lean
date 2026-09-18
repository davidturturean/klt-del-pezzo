import KltDP.Geometry.PrimeCurveCartierVanishingIdeal

/-!
# Original Weil coefficients of a finite reduced prime Cartier sum

Injectivity of the actual prime family ensures that each curve contributes
once. The original Cartier-to-Weil map then has coefficient one precisely
on that family and zero elsewhere. This verifies the multiplicities of the
actual finite Cartier sum used in the global SNC construction.
-/

noncomputable section

open AlgebraicGeometry

universe u v

namespace KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Classical.propDecidable

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  {I : Type v} [Fintype I] (C : I → X.PrimeCurve) (hinj : Function.Injective C)

include hinj in
/-- The original reduced Cartier sum has coefficient one exactly on its
actual prime family; no Weil-divisor or multiplicity premise is supplied. -/
theorem finite_primeCartier_sum_coefficient (E : X.PrimeCurve) :
    X.cartierToWeilHom (∑ i, X.primeCurveCartier hregular (C i)) E =
      if E ∈ Set.range C then 1 else 0 := by
  classical
  rw [map_sum, Finsupp.finset_sum_apply]
  simp_rw [X.cartierToWeilHom_primeCurveCartier hregular]
  by_cases hE : E ∈ Set.range C
  · obtain ⟨i, rfl⟩ := hE
    rw [if_pos (Set.mem_range_self i)]
    rw [Finset.sum_eq_single i]
    · exact Finsupp.single_eq_same
    · intro j _ hji
      exact Finsupp.single_eq_of_ne (fun h => hji (hinj h))
    · simp
  · rw [if_neg hE]
    apply Finset.sum_eq_zero
    intro i _
    exact Finsupp.single_eq_of_ne (fun h => hE ⟨i, h⟩)

include hinj in
/-- The actual prime Cartier sum has effective original Weil coefficients. -/
theorem finite_primeCartier_sum_effective :
    EffectiveDivisor (X.cartierToWeilHom (∑ i, X.primeCurveCartier hregular (C i))) := by
  intro E
  rw [finite_primeCartier_sum_coefficient X hregular C hinj E]
  split_ifs <;> norm_num

include hinj in
/-- The actual prime Cartier sum is reduced at the level of original Weil coefficients. -/
theorem finite_primeCartier_sum_coefficient_le_one (E : X.PrimeCurve) :
    X.cartierToWeilHom (∑ i, X.primeCurveCartier hregular (C i)) E ≤ 1 := by
  rw [finite_primeCartier_sum_coefficient X hregular C hinj E]
  split_ifs <;> norm_num

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.finite_primeCartier_sum_coefficient
