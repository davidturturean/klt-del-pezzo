import KltDP.RingTheory.FactorialHartogs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Prime denominator ideals above a nonregular fraction

The pinned associated-prime existence theorem applies to the original
quotient module `K / R`. Its annihilators are exactly the already defined
denominator ideals. This stage requires only a Noetherian base ring.
-/

noncomputable section

universe u v

namespace KltDP.RingTheory.NormalHartogs

open FactorialHartogs

variable (R : Type u) [CommRing R] (K : Type v) [CommRing K] [Algebra R K]

/-- The original additive image of the base ring inside its algebra. -/
def baseRange : Submodule R K := LinearMap.range (Algebra.linearMap R K)

/-- Annihilators in the original quotient `K / R` are denominator ideals. -/
theorem ker_toSpanSingleton_quotient (f : K) :
    LinearMap.ker (LinearMap.toSpanSingleton R (K ⧸ baseRange R K)
      ((baseRange R K).mkQ f)) = denominatorIdeal R K f := by
  ext r
  rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [baseRange, LinearMap.mem_range, mem_denominatorIdeal_iff, Algebra.smul_def]
  change (∃ a : R, algebraMap R K a = algebraMap R K r * f) ↔
    ∃ a : R, algebraMap R K r * f = algebraMap R K a
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

/-- A nonregular fraction has its denominator ideal contained in a
prime which is itself the denominator ideal of an actual fraction. -/
theorem exists_prime_denominator_over [IsNoetherianRing R] (f : K)
    (hf : f ∉ Set.range (algebraMap R K)) :
    ∃ g : K, (denominatorIdeal R K g).IsPrime ∧
      denominatorIdeal R K f ≤ denominatorIdeal R K g := by
  have hq : (baseRange R K).mkQ f ≠ 0 := by
    intro h
    have hmem := (Submodule.Quotient.mk_eq_zero (p := baseRange R K)).mp h
    exact hf hmem
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    ((baseRange R K).mkQ f) hq
  obtain ⟨y, hy⟩ := hP.2
  obtain ⟨g, rfl⟩ := (baseRange R K).mkQ_surjective y
  rw [ker_toSpanSingleton_quotient] at hy hle
  exact ⟨g, hy ▸ hP.1, hy ▸ hle⟩

end KltDP.RingTheory.NormalHartogs
