import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! A principal localized ideal has an original generator on an actual
basic neighborhood. Finite generation clears one denominator for all
original ideal elements; every original map inverting that denominator
then gives the same principal extended ideal. -/

noncomputable section

open scoped BigOperators

namespace KltDP.Geometry.PrincipalIdealNeighborhood

variable {R : Type*} [CommRing R] (M : Submonoid R)
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The generator and the common denominator both come from the original ring. -/
theorem exists_source_generator_denominator (I : Ideal R) (hfg : I.FG)
    [(I.map (algebraMap R S)).IsPrincipal] :
    ∃ d ∈ I, ∃ b ∈ M,
      I.map (algebraMap R S) = Ideal.span {algebraMap R S d} ∧
      ∀ r ∈ I, b * r ∈ Ideal.span {d} := by
  classical
  let J := I.map (algebraMap R S)
  obtain ⟨⟨d, s⟩, hds⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp
    (Submodule.IsPrincipal.generator_mem J)
  have hdspan : J = Ideal.span {algebraMap R S (d : R)} := by
    calc
      J = Ideal.span {Submodule.IsPrincipal.generator J} :=
        (Ideal.span_singleton_generator J).symm
      _ = Ideal.span {Submodule.IsPrincipal.generator J * algebraMap R S s} :=
        (Ideal.span_singleton_mul_right_unit (IsLocalization.map_units S s) _).symm
      _ = Ideal.span {algebraMap R S (d : R)} := by rw [hds]
  obtain ⟨t, ht⟩ := hfg
  have hden (r : {r : R // r ∈ t}) :
      ∃ m ∈ M, m * (r : R) ∈ Ideal.span {(d : R)} := by
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff M S _ _).mp
    rw [Ideal.map_span, Set.image_singleton, ← hdspan]
    apply Ideal.mem_map_of_mem
    rw [← ht]
    exact Submodule.subset_span r.2
  choose m hm hmr using hden
  let b : R := ∏ r : {r : R // r ∈ t}, m r
  have hb : b ∈ M := M.prod_mem (fun r _ => hm r)
  refine ⟨d, d.2, b, hb, hdspan, ?_⟩
  intro r hr
  rw [← ht] at hr
  induction hr using Submodule.span_induction with
  | mem r hr =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m
        (Finset.mem_univ (⟨r, hr⟩ : {r : R // r ∈ t}))
      change b * r ∈ Ideal.span {(d : R)}
      have heq : b = m ⟨r, hr⟩ * c := hc
      rw [heq, mul_right_comm]
      exact (Ideal.span {(d : R)}).mul_mem_right c (hmr ⟨r, hr⟩)
  | zero => simp only [mul_zero, Ideal.zero_mem]
  | add r s hr hs h₁ h₂ =>
      simpa only [mul_add] using (Ideal.span {(d : R)}).add_mem h₁ h₂
  | smul a r hr h =>
      simpa only [smul_eq_mul, mul_left_comm] using
        (Ideal.span {(d : R)}).mul_mem_left a h

/-- Any actual ring map inverting the proved denominator has the original
principal extended ideal. -/
theorem map_eq_span_of_unit_denominator {T : Type*} [CommRing T]
    (φ : R →+* T) (I : Ideal R) (d b : R) (hd : d ∈ I)
    (hb : IsUnit (φ b)) (hden : ∀ r ∈ I, b * r ∈ Ideal.span {d}) :
    I.map φ = Ideal.span {φ d} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change φ r ∈ Ideal.span {φ d}
    apply (Ideal.unit_mul_mem_iff_mem _ hb).mp
    have h := Ideal.mem_map_of_mem φ (hden r hr)
    simpa only [Ideal.map_span, Set.image_singleton, map_mul] using h
  · apply Ideal.span_le.mpr
    rintro _ rfl
    exact Ideal.mem_map_of_mem φ hd

#print axioms exists_source_generator_denominator
#print axioms map_eq_span_of_unit_denominator

end KltDP.Geometry.PrincipalIdealNeighborhood
