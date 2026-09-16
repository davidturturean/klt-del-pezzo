import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Equality of finitely generated ideal germs spreads to a principal open

The proof chooses actual denominators for finitely many generators and
takes their product. It constructs a principal neighborhood and proves
equality of the actual localized ideals, without assuming such a
neighborhood or replacing ideal equality by equality of supports.
-/

noncomputable section

open scoped BigOperators

namespace KltDP.Compatibility

universe u

/-- If `I ≤ J` and their germs agree at `p`, finite generation of `J`
provides a principal neighborhood of `p` on which the actual ideals agree. -/
theorem exists_away_ideal_eq_of_atPrime_eq
    {R : Type u} [CommRing R] (p I J : Ideal R) [p.IsPrime]
    (hIJ : I ≤ J) (hJ : J.FG)
    (hgerm : I.map (algebraMap R (Localization.AtPrime p)) =
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ r : R, r ∉ p ∧
      I.map (algebraMap R (Localization.Away r)) =
        J.map (algebraMap R (Localization.Away r)) := by
  classical
  obtain ⟨t, ht⟩ := hJ
  have hden (x : t) : ∃ c ∈ p.primeCompl, c * (x : R) ∈ I := by
    have hx : (x : R) ∈ J := by
      rw [← ht]
      exact Ideal.subset_span x.2
    have hl : algebraMap R (Localization.AtPrime p) (x : R) ∈
        I.map (algebraMap R (Localization.AtPrime p)) := by
      rw [hgerm]
      exact Ideal.mem_map_of_mem _ hx
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff
      p.primeCompl (Localization.AtPrime p) I (x : R)).mp hl
  choose c hc hcx using hden
  let r : R := ∏ x : t, c x
  have hr : r ∉ p := by
    change r ∈ p.primeCompl
    exact p.primeCompl.prod_mem (fun x _ ↦ hc x)
  refine ⟨r, hr, le_antisymm (Ideal.map_mono hIJ) ?_⟩
  apply Ideal.map_le_iff_le_comap.mpr
  rw [← ht, Ideal.span_le]
  intro x hx
  let xt : t := ⟨x, hx⟩
  have hdiv : c xt ∣ r := Finset.dvd_prod_of_mem c (Finset.mem_univ xt)
  obtain ⟨b, hb⟩ := hdiv
  have hmul : r * x ∈ I := by
    have hcx' : c xt * x ∈ I := hcx xt
    rw [hb]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using I.mul_mem_left b hcx'
  have himage : algebraMap R (Localization.Away r) r *
      algebraMap R (Localization.Away r) x ∈
      I.map (algebraMap R (Localization.Away r)) := by
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ hmul
  change algebraMap R (Localization.Away r) x ∈
    I.map (algebraMap R (Localization.Away r))
  exact (Ideal.unit_mul_mem_iff_mem
    (I.map (algebraMap R (Localization.Away r)))
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r)).mp himage

/-- A maximal ideal disjoint from a localization's denominators remains
maximal. The proof uses the actual prime-ideal localization correspondence. -/
theorem isMaximal_map_of_localization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    (q : Ideal R) [q.IsMaximal] (hd : Disjoint (M : Set R) (q : Set R)) :
    (q.map (algebraMap R S)).IsMaximal := by
  letI : (q.map (algebraMap R S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M S q inferInstance hd
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal (q.map (algebraMap R S))
    (Ideal.IsPrime.ne_top inferInstance)
  letI : Q.IsMaximal := hQ
  have heq : q = Q.comap (algebraMap R S) :=
    Ideal.IsMaximal.eq_of_le inferInstance
      (Ideal.IsPrime.ne_top inferInstance) (Ideal.map_le_iff_le_comap.mp hle)
  have hmap : q.map (algebraMap R S) = Q := by
    rw [heq, IsLocalization.map_comap M S Q]
  rwa [hmap]

/-- Inverting an element outside a maximal ideal preserves its actual
closed-point ideal. -/
theorem isMaximal_map_away
    {R : Type u} [CommRing R] (q : Ideal R) [q.IsMaximal]
    (r : R) (hr : r ∉ q) :
    (q.map (algebraMap R (Localization.Away r))).IsMaximal := by
  apply isMaximal_map_of_localization (Submonoid.powers r) q
  apply Set.disjoint_left.mpr
  rintro x ⟨n, rfl⟩ hx
  exact hr (Ideal.IsPrime.mem_of_pow_mem inferInstance n hx)

end KltDP.Compatibility
