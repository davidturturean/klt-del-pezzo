import KltDP.Geometry.RationalHodgeIndex
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The original integral numerical divisor-class group

The group is the actual additive Picard group modulo the already defined
subgroup of classes whose degrees vanish on every original prime curve.
Its canonical map to the existing rational numerical quotient is injective.
Positive denominator clearing proves that this map is a localization at the
nonzero integers. Mathlib then supplies its canonical tensor equivalence.

No finite-generation, freeness, Hodge, or finite-dimensionality hypothesis is
needed for these object comparisons.
-/

noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The literal integral numerical group: the original Picard group modulo
its existing all-prime-curve numerical subgroup. -/
abbrev IntegralNumericalClassGroup :=
  Additive X.toScheme.Pic ⧸ X.numericallyTrivialSubgroup

/-- The original integral Picard class map. -/
def picardIntegralNumericalMap :
    Additive X.toScheme.Pic →ₗ[ℤ] X.IntegralNumericalClassGroup :=
  (QuotientAddGroup.mk' X.numericallyTrivialSubgroup).toIntLinearMap

theorem picardIntegralNumericalMap_surjective :
    Function.Surjective X.picardIntegralNumericalMap :=
  QuotientAddGroup.mk'_surjective X.numericallyTrivialSubgroup

/-- Vanishing in the integral quotient is exactly original numerical triviality. -/
theorem picardIntegralNumericalMap_eq_zero_iff (p : Additive X.toScheme.Pic) :
    X.picardIntegralNumericalMap p = 0 ↔ X.NumericallyTrivial p.toMul :=
  (QuotientAddGroup.eq_zero_iff p).trans (X.mem_numericallyTrivialSubgroup_iff p)

/-- The canonical integral quotient map has the original numerical subgroup as
its exact additive kernel. -/
theorem picardIntegralNumericalMap_ker :
    X.picardIntegralNumericalMap.toAddMonoidHom.ker = X.numericallyTrivialSubgroup := by
  ext p
  change X.picardIntegralNumericalMap p = 0 ↔ p ∈ X.numericallyTrivialSubgroup
  rw [picardIntegralNumericalMap_eq_zero_iff, mem_numericallyTrivialSubgroup_iff]

/-- The original rational numerical map descends through the integral quotient. -/
def integralNumericalRationalization :
    X.IntegralNumericalClassGroup →ₗ[ℤ] X.NumericalClassGroup :=
  (QuotientAddGroup.lift X.numericallyTrivialSubgroup
    X.picardNumericalMap.toAddMonoidHom (by
      intro p hp
      exact (X.picardNumericalMap_eq_zero_iff p).mpr
        ((X.mem_numericallyTrivialSubgroup_iff p).mp hp))).toIntLinearMap

/-- Both actual integral class maps recover the existing rational Picard map. -/
@[simp]
theorem integralNumericalRationalization_picard (p : Additive X.toScheme.Pic) :
    X.integralNumericalRationalization (X.picardIntegralNumericalMap p) =
      X.picardNumericalMap p := rfl

theorem integralNumericalRationalization_eq_zero_iff (c : X.IntegralNumericalClassGroup) :
    X.integralNumericalRationalization c = 0 ↔ c = 0 := by
  obtain ⟨p, rfl⟩ := X.picardIntegralNumericalMap_surjective c
  rw [integralNumericalRationalization_picard, picardNumericalMap_eq_zero_iff,
    picardIntegralNumericalMap_eq_zero_iff]

/-- Rationalization loses no original integral numerical class. -/
theorem integralNumericalRationalization_injective :
    Function.Injective X.integralNumericalRationalization := by
  intro c d h
  apply sub_eq_zero.mp
  apply (X.integralNumericalRationalization_eq_zero_iff (c - d)).mp
  rw [map_sub, h, sub_self]

/-- Every class in the existing rational quotient has a positive integral
multiple coming from the actual integral numerical group. -/
theorem numericalClass_exists_positive_integralNum_multiple (v : X.NumericalClassGroup) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : X.IntegralNumericalClassGroup,
      X.integralNumericalRationalization c = (n : ℚ) • v := by
  obtain ⟨n, hn, p, hp⟩ := X.numericalClass_exists_positive_integral_multiple v
  exact ⟨n, hn, X.picardIntegralNumericalMap p, hp⟩

/-- The image of the original integral numerical group spans the entire
existing rational numerical quotient. -/
theorem integralNumericalRationalization_span :
    Submodule.span ℚ (Set.range X.integralNumericalRationalization) = ⊤ := by
  apply eq_top_iff.mpr
  intro v _
  obtain ⟨n, hn, c, hc⟩ := X.numericalClass_exists_positive_integralNum_multiple v
  have hmem : X.integralNumericalRationalization c ∈
      Submodule.span ℚ (Set.range X.integralNumericalRationalization) :=
    Submodule.subset_span ⟨c, rfl⟩
  have hscaled := Submodule.smul_mem
    (Submodule.span ℚ (Set.range X.integralNumericalRationalization)) (n : ℚ)⁻¹ hmem
  rw [hc, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)),
    one_smul] at hscaled
  exact hscaled

/-- The actual integral-to-rational numerical map is localization at the
nonzero integers, by injectivity and proved positive denominator clearing. -/
instance integralNumericalRationalization_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ) X.integralNumericalRationalization where
  map_units s := by
    rw [← (Algebra.lsmul ℤ (A := ℚ) ℤ X.NumericalClassGroup).commutes]
    exact (IsLocalization.map_units ℚ s).map _
  surj' v := by
    obtain ⟨n, hn, c, hc⟩ := X.numericalClass_exists_positive_integralNum_multiple v
    let s : nonZeroDivisors ℤ :=
      ⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr
        (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn))⟩
    refine ⟨(c, s), ?_⟩
    change (n : ℤ) • v = X.integralNumericalRationalization c
    simpa only [natCast_zsmul, Nat.cast_smul_eq_nsmul ℚ] using hc.symm
  exists_of_eq {c d} h := by
    change X.integralNumericalRationalization c = X.integralNumericalRationalization d at h
    refine ⟨1, ?_⟩
    simpa only [Submonoid.coe_one, one_smul] using
      (X.integralNumericalRationalization_injective h)

/-- The canonical rationalization of the actual integral numerical quotient is
the existing rational numerical quotient, by the imported base-change theorem. -/
def integralNumericalTensorRationalEquiv :
    ℚ ⊗[ℤ] X.IntegralNumericalClassGroup ≃ₗ[ℚ] X.NumericalClassGroup :=
  (IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ
    X.integralNumericalRationalization).equiv

/-- The tensor equivalence preserves the original integral numerical inclusion. -/
theorem integralNumericalTensorRationalEquiv_one_tmul (c : X.IntegralNumericalClassGroup) :
    X.integralNumericalTensorRationalEquiv (1 ⊗ₜ[ℤ] c) =
      X.integralNumericalRationalization c :=
  (IsBaseChange.equiv_tmul
    (IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ
      X.integralNumericalRationalization) (1 : ℚ) c).trans (one_smul ℚ _)

end KltDP.Geometry.NormalProjectiveSurface
