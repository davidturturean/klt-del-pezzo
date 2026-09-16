import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

/-!
# Parameter existence and dimension drop for the factoriality problem

These support results concern actual maximal ideals, cotangent spaces and
localizations. They do not assert that a regular local ring is factorial.
An element of the maximal ideal outside its square is proved irreducible,
not assumed prime. Localization away from an element of the maximal ideal
is proved to have smaller dimension, not assumed to be a PID or a UFD.

The parameter-existence statement occurs as a proved helper in the UW Math AI
regular-local-factoriality source. Here its proof reuses the pinned cotangent
form of Nakayama's lemma. The dimension argument reuses pinned prime-height
transport. See `docs/REGULAR_LOCAL_FACTORIAL_SUPPORT.md` for precise provenance
and the remaining route obligations.
-/

namespace KltDP.Geometry.RegularLocalFactorialSupport

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- In a positive-dimensional Noetherian local ring, the actual maximal ideal
contains an element outside its square. -/
theorem exists_mem_maximal_not_mem_sq [IsNoetherianRing R]
    (hdim : 0 < ringKrullDim R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ (maximalIdeal R) ^ 2 := by
  classical
  by_contra h
  have hall : ∀ x : R, x ∈ maximalIdeal R → x ∈ (maximalIdeal R) ^ 2 := by
    intro x hx
    by_contra hxsq
    exact h ⟨x, hx, hxsq⟩
  have hsub : Subsingleton (CotangentSpace R) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := (maximalIdeal R).toCotangent_surjective a
    obtain ⟨b', rfl⟩ := (maximalIdeal R).toCotangent_surjective b
    have ha : (maximalIdeal R).toCotangent a' = 0 :=
      ((maximalIdeal R).toCotangent_eq_zero a').mpr (hall a' a'.property)
    have hb : (maximalIdeal R).toCotangent b' = 0 :=
      ((maximalIdeal R).toCotangent_eq_zero b').mpr (hall b' b'.property)
    exact ha.trans hb.symm
  exact hdim.ne' (ringKrullDim_eq_zero_of_isField
    (subsingleton_cotangentSpace_iff.mp hsub))

/-- An element of a local ring's maximal ideal outside its square is
irreducible. This assertion does not require a domain or Noetherianity. -/
theorem irreducible_of_mem_maximal_not_mem_sq {x : R}
    (hx : x ∈ maximalIdeal R) (hxsq : x ∉ (maximalIdeal R) ^ 2) :
    Irreducible x := by
  classical
  refine ⟨?_, ?_⟩
  · simpa only [mem_maximalIdeal, mem_nonunits_iff] using hx
  · intro a b hab
    by_cases ha : IsUnit a
    · exact Or.inl ha
    · right
      by_contra hb
      have ham : a ∈ maximalIdeal R := by
        simpa only [mem_maximalIdeal, mem_nonunits_iff] using ha
      have hbm : b ∈ maximalIdeal R := by
        simpa only [mem_maximalIdeal, mem_nonunits_iff] using hb
      apply hxsq
      rw [hab, pow_two]
      exact Ideal.mul_mem_mul ham hbm

/-- Positive-dimensional Noetherian local rings have an actual irreducible
parameter outside the square of their maximal ideal. -/
theorem exists_irreducible_parameter [IsNoetherianRing R]
    (hdim : 0 < ringKrullDim R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ (maximalIdeal R) ^ 2 ∧ Irreducible x := by
  obtain ⟨x, hx, hxsq⟩ := exists_mem_maximal_not_mem_sq hdim
  exact ⟨x, hx, hxsq, irreducible_of_mem_maximal_not_mem_sq hx hxsq⟩

section Localization

variable {T : Type*} [CommRing T] [Algebra R T]
variable {f : R} [IsLocalization.Away f T]

/-- The comap of an actual prime of the localization lies strictly below the
maximal ideal: the inverted element belongs to the latter but not the former. -/
theorem comap_prime_lt_maximal (hf : f ∈ maximalIdeal R)
    (J : Ideal T) [J.IsPrime] :
    J.comap (algebraMap R T) < maximalIdeal R := by
  have hprime : (J.comap (algebraMap R T)).IsPrime := inferInstance
  apply lt_of_le_of_ne (le_maximalIdeal hprime.ne_top)
  intro heq
  have hfJ : algebraMap R T f ∈ J := by
    change f ∈ J.comap (algebraMap R T)
    rw [heq]
    exact hf
  exact (Ideal.IsPrime.ne_top (inferInstance : J.IsPrime))
    (J.eq_top_of_isUnit_mem hfJ (IsLocalization.Away.algebraMap_isUnit f))

/-- Prime heights in the localization drop by at least one from the ambient
local-ring dimension bound. No Noetherianity or domain condition is needed. -/
theorem primeHeight_away_le (hf : f ∈ maximalIdeal R) (n : ℕ)
    (hdim : ringKrullDim R ≤ (n : WithBot ℕ∞) + 1)
    (J : Ideal T) [J.IsPrime] : J.primeHeight ≤ (n : ℕ∞) := by
  have hstep := Ideal.primeHeight_add_one_le_of_lt (comap_prime_lt_maximal hf J)
  have hm : (maximalIdeal R).primeHeight ≤ (n : ℕ∞) + 1 := by
    have hdim' : ((maximalIdeal R).primeHeight : WithBot ℕ∞) ≤
        (n : WithBot ℕ∞) + 1 := by
      simpa only [maximalIdeal_primeHeight_eq_ringKrullDim] using hdim
    exact_mod_cast hdim'
  have hcomp : (J.comap (algebraMap R T)).primeHeight ≤ (n : ℕ∞) :=
    (WithTop.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp (hstep.trans hm)
  rwa [IsLocalization.primeHeight_comap (Submonoid.powers f) J] at hcomp

/-- Inverting an element of the maximal ideal lowers a finite local dimension
bound by one. The conclusion concerns the actual localization's prime spectrum. -/
theorem ringKrullDim_away_le (hf : f ∈ maximalIdeal R) (n : ℕ)
    (hdim : ringKrullDim R ≤ (n : WithBot ℕ∞) + 1) :
    ringKrullDim T ≤ (n : WithBot ℕ∞) := by
  rw [ringKrullDim, Order.krullDim_eq_iSup_height]
  apply iSup_le
  intro p
  letI : p.asIdeal.IsPrime := p.isPrime
  have hp : p.asIdeal.primeHeight ≤ (n : ℕ∞) := primeHeight_away_le hf n hdim p.asIdeal
  change (p.asIdeal.primeHeight : WithBot ℕ∞) ≤ (n : WithBot ℕ∞)
  exact_mod_cast hp

/-- The localization relevant to a two-dimensional local surface ring has
dimension at most one. This does not imply principal ideals or factoriality. -/
theorem ringKrullDim_away_le_one (hf : f ∈ maximalIdeal R)
    (hdim : ringKrullDim R ≤ 2) : ringKrullDim T ≤ 1 := by
  simpa using ringKrullDim_away_le (T := T) hf 1 (by simpa using hdim)

end Localization

end KltDP.Geometry.RegularLocalFactorialSupport
