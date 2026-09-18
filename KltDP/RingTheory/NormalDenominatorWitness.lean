import KltDP.RingTheory.NormalDenominatorAssociatedPrime
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Normality forces a denominator ideal to escape under multiplication

The original nonzero denominator ideal embeds as a finite submodule of
the original fraction field. If multiplication by the fraction preserved
that submodule, the pinned determinant trick would make the fraction
integral, hence regular by normality. No factoriality is used.
-/

noncomputable section

universe u v

namespace KltDP.RingTheory.NormalHartogs

open FactorialHartogs

variable (R : Type u) [CommRing R] [IsDomain R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The denominator ideal of an actual fraction is nonzero. -/
theorem denominatorIdeal_ne_bot (f : K) : denominatorIdeal R K f ≠ ⊥ := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) f
  have hb : (b : R) ∈ denominatorIdeal R K f :=
    ⟨a, (mul_comm _ f).trans hab⟩
  intro h
  rw [h] at hb
  exact nonZeroDivisors.ne_zero b.2 hb

/-- A nonregular fraction in a normal Noetherian domain multiplies
some denominator into an original element outside its denominator ideal. -/
theorem exists_denominator_witness [IsNoetherianRing R] [IsIntegrallyClosed R]
    (f : K) (hproper : denominatorIdeal R K f ≠ ⊤) :
    ∃ s r : R, s ∈ denominatorIdeal R K f ∧ r ∉ denominatorIdeal R K f ∧
      algebraMap R K s * f = algebraMap R K r := by
  classical
  by_contra hex
  let P := denominatorIdeal R K f
  let M := Submodule.map (Algebra.linearMap R K) P
  have hstable : ∀ y ∈ M, f * y ∈ M := by
    rintro y ⟨s, hs, rfl : algebraMap R K s = y⟩
    obtain ⟨r, hr⟩ := hs
    have hrP : r ∈ P := by
      by_contra hnot
      exact hex ⟨s, r, ⟨r, hr⟩, hnot, hr⟩
    exact ⟨r, hrP, hr.symm.trans (mul_comm _ f)⟩
  have hM : M ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp (denominatorIdeal_ne_bot R K f)
    refine (Submodule.ne_bot_iff _).mpr ⟨algebraMap R K a, ⟨a, ha, rfl⟩, ?_⟩
    exact (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr ha0
  have hfg : M.FG := Submodule.FG.map _ (IsNoetherian.noetherian P)
  have hint : IsIntegral R f := isIntegral_of_smul_mem_submodule M hM hfg f hstable
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  apply hproper
  apply (Ideal.eq_top_iff_one (denominatorIdeal R K f)).mpr
  exact ⟨a, by rw [map_one, one_mul, ha]⟩

end KltDP.RingTheory.NormalHartogs
