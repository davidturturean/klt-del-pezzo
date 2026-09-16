import KltDP.Geometry.UFDDivisorCoordinates
import Mathlib.RingTheory.Ideal.Height

/-!
# Algebraic Hartogs for factorial rings

BRIEF30, task 1 (F09 step (i), algebraic core). For a ring `R` with an `R`-algebra `K` (in practice the
fraction field), `MemLocalizationAt R K p f` says that `f ∈ K` lies in the localisation of `R` at the prime
`p`: `s · f ∈ R` for some `s ∉ p`.

* **Local–global for elements** (`mem_range_iff_forall_isMaximal`, any commutative ring): `f` lies in
  (the image of) `R` iff it lies in every localisation at a maximal ideal — the ideal of denominators
  `denominatorIdeal R K f = {s | s · f ∈ R}` is not contained in any maximal ideal.
* **Hartogs for a UFD** (`exists_eq_algebraMap_of_forall_heightOne`, `mem_range_iff_forall_heightOne`):
  for a unique factorisation domain `R` with fraction field `K`, `f ∈ K` lies in `R` iff `f` lies in the
  localisation at every height-one prime. Lowest-terms argument by well-founded induction on the
  denominator: a prime factor `π` of the denominator generates a height-one prime (the accepted
  `primeElement_span_height_eq_one`); regularity at `(π)` forces `π` to divide the numerator, and the
  fraction is cancelled. Mathlib's only intersection-of-localisations statement at the pin is the
  Dedekind-domain `iInf_localization_eq`; no Noetherian hypothesis is needed here.
* **Dimension-two local corollary** (`mem_range_iff_forall_ne_bot_ne_maximalIdeal`): for a local UFD `R`
  with `ringKrullDim R = 2`, `f ∈ R` iff `f` lies in the localisation at every prime other than `0` and the
  maximal ideal (these are exactly the height-one primes: `ne_bot_of_height_eq_one`,
  `ne_maximalIdeal_of_height_eq_one`); and such primes exist
  (`exists_isPrime_ne_bot_ne_maximalIdeal`). No Noetherian hypothesis is needed.
* `MemLocalizationAt.of_comap`: transport along a scalar tower `R → A → K` (used for the stalk of a
  point and the ring of an affine chart).
-/

noncomputable section

universe u v w

namespace KltDP.RingTheory.FactorialHartogs

section General

variable (R : Type u) [CommRing R] (K : Type v) [CommRing K] [Algebra R K]

/-- `f ∈ K` lies in the localisation of `R` at `p`: `s · f ∈ R` for some `s ∉ p`. -/
def MemLocalizationAt (p : Ideal R) (f : K) : Prop :=
  ∃ r s : R, s ∉ p ∧ algebraMap R K s * f = algebraMap R K r

theorem memLocalizationAt_of_mem_range (p : Ideal R) (hp : p ≠ ⊤) {f : K}
    (hf : f ∈ Set.range (algebraMap R K)) : MemLocalizationAt R K p f := by
  obtain ⟨r, rfl⟩ := hf
  exact ⟨r, 1, fun h => hp ((Ideal.eq_top_iff_one p).mpr h), by rw [map_one, one_mul]⟩

/-- Transport along a scalar tower `R → A → K`: regularity at `P.comap (R → A)` implies regularity
at `P`. -/
theorem MemLocalizationAt.of_comap {A : Type w} [CommRing A] [Algebra R A] [Algebra A K]
    [IsScalarTower R A K] (P : Ideal A) {f : K}
    (h : MemLocalizationAt R K (P.comap (algebraMap R A)) f) : MemLocalizationAt A K P f := by
  obtain ⟨r, s, hs, hsf⟩ := h
  refine ⟨algebraMap R A r, algebraMap R A s, fun h => hs (Ideal.mem_comap.mpr h), ?_⟩
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact hsf

/-- The ideal of denominators of `f`. -/
def denominatorIdeal (f : K) : Ideal R where
  carrier := {s | ∃ r : R, algebraMap R K s * f = algebraMap R K r}
  add_mem' := by
    rintro a b ⟨r, hr⟩ ⟨r', hr'⟩
    exact ⟨r + r', by rw [map_add, map_add, add_mul, hr, hr']⟩
  zero_mem' := ⟨0, by rw [map_zero, zero_mul]⟩
  smul_mem' := by
    rintro c a ⟨r, hr⟩
    refine ⟨c * r, ?_⟩
    show algebraMap R K (c * a) * f = algebraMap R K (c * r)
    rw [map_mul, map_mul, mul_assoc, hr]

theorem mem_denominatorIdeal_iff (f : K) (s : R) :
    s ∈ denominatorIdeal R K f ↔ ∃ r : R, algebraMap R K s * f = algebraMap R K r :=
  Iff.rfl

/-- **Local–global for elements**: `f` lies in `R` iff it lies in every localisation at a maximal
ideal. -/
theorem mem_range_iff_forall_isMaximal (f : K) :
    f ∈ Set.range (algebraMap R K) ↔
      ∀ p : Ideal R, p.IsMaximal → MemLocalizationAt R K p f := by
  constructor
  · intro hf p hp
    exact memLocalizationAt_of_mem_range R K p hp.ne_top hf
  · intro h
    by_contra hf
    have hI : denominatorIdeal R K f ≠ ⊤ := by
      intro hI
      have h1 : (1 : R) ∈ denominatorIdeal R K f := by rw [hI]; exact Submodule.mem_top
      obtain ⟨r, hr⟩ := h1
      rw [map_one, one_mul] at hr
      exact hf ⟨r, hr.symm⟩
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
    obtain ⟨r, s, hs, hsf⟩ := h m hm
    exact hs (hIm ⟨r, hsf⟩)

end General

section Factorial

variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Hartogs for a UFD**: an element of the fraction field lying in the localisation at every
height-one prime lies in `R`. -/
theorem exists_eq_algebraMap_of_forall_heightOne {f : K}
    (hf : ∀ p : Ideal R, p.IsPrime → p.height = 1 → MemLocalizationAt R K p f) :
    ∃ r : R, algebraMap R K r = f := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) f
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  revert a
  refine WellFounded.induction (wellFounded_dvdNotUnit (α := R))
    (C := fun b : R => b ≠ 0 → ∀ a : R, f * algebraMap R K b = algebraMap R K a →
      ∃ r : R, algebraMap R K r = f) (b : R) ?_ hb0
  intro b ih hb a hab
  by_cases hu : IsUnit b
  · obtain ⟨u, rfl⟩ := hu
    refine ⟨a * ↑u⁻¹, ?_⟩
    rw [map_mul, ← hab, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  · obtain ⟨π, hπ, b', rfl⟩ := WfDvdMonoid.exists_irreducible_factor hu hb
    have hπp : Prime π := UniqueFactorizationMonoid.irreducible_iff_prime.mp hπ
    haveI hp : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπp.ne_zero).mpr hπp
    obtain ⟨r, s, hs, hsf⟩ :=
      hf _ hp (KltDP.RingTheory.primeElement_span_height_eq_one R π hπp)
    have hs' : ¬ π ∣ s := fun h => hs (Ideal.mem_span_singleton.mpr h)
    have heq : s * a = r * (π * b') := by
      apply hinj
      rw [map_mul, map_mul, ← hab, ← hsf]
      ring
    have hπa : π ∣ a := by
      have hsa : π ∣ s * a := ⟨r * b', by rw [heq]; ring⟩
      exact (hπp.dvd_or_dvd hsa).resolve_left hs'
    obtain ⟨a', rfl⟩ := hπa
    have hb' : b' ≠ 0 := right_ne_zero_of_mul hb
    refine ih b' ⟨hb', π, hπ.not_isUnit, mul_comm π b'⟩ hb' a' ?_
    have hπ0 : algebraMap R K π ≠ 0 := fun h => hπp.ne_zero (hinj (by rw [h, map_zero]))
    apply mul_left_cancel₀ hπ0
    rw [map_mul, map_mul] at hab
    rw [← hab]
    ring

theorem mem_range_iff_forall_heightOne (f : K) :
    f ∈ Set.range (algebraMap R K) ↔
      ∀ p : Ideal R, p.IsPrime → p.height = 1 → MemLocalizationAt R K p f :=
  ⟨fun hf p hp _ => memLocalizationAt_of_mem_range R K p hp.ne_top hf,
    fun hf => exists_eq_algebraMap_of_forall_heightOne R K hf⟩

end Factorial

section DimensionTwo

variable (R : Type u) [CommRing R]

theorem bot_primeHeight [IsDomain R] :
    haveI : (⊥ : Ideal R).IsPrime := Ideal.bot_prime
    (⊥ : Ideal R).primeHeight = 0 :=
  Order.height_eq_zero.mpr fun b _ => (bot_le : (⊥ : Ideal R) ≤ b.asIdeal)

theorem ne_bot_of_height_eq_one [IsDomain R] {p : Ideal R} [p.IsPrime] (hp : p.height = 1) : p ≠ ⊥ := by
  rintro rfl
  rw [Ideal.height_eq_primeHeight, bot_primeHeight] at hp
  exact zero_ne_one hp

variable [IsLocalRing R]

theorem ne_maximalIdeal_of_height_eq_one (hdim : ringKrullDim R = 2) {p : Ideal R} [p.IsPrime]
    (hp : p.height = 1) : p ≠ IsLocalRing.maximalIdeal R := by
  rintro rfl
  have h := IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim (R := R)
  have h2 : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞) := hdim
  rw [← Ideal.height_eq_primeHeight, hp, h2] at h
  have h' : (1 : ℕ∞) = 2 := WithBot.coe_inj.mp h
  norm_num at h'

/-- A local ring of Krull dimension two has a prime other than `0` and the maximal ideal. -/
theorem exists_isPrime_ne_bot_ne_maximalIdeal (hdim : ringKrullDim R = 2) :
    ∃ p : Ideal R, p.IsPrime ∧ p ≠ ⊥ ∧ p ≠ IsLocalRing.maximalIdeal R := by
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum R) := by
    show ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R
    rw [hdim]
    exact le_of_eq (by norm_num)
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp h2
  have h01 : l ⟨0, by omega⟩ < l ⟨1, by omega⟩ := l.strictMono (Fin.mk_lt_mk.mpr (by omega))
  have h12 : l ⟨1, by omega⟩ < l ⟨2, by omega⟩ := l.strictMono (Fin.mk_lt_mk.mpr (by omega))
  refine ⟨(l ⟨1, by omega⟩).asIdeal, (l ⟨1, by omega⟩).isPrime, ?_, ?_⟩
  · intro hbot
    have h01' := (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr h01
    rw [hbot] at h01'
    exact not_lt_bot h01'
  · intro hmax
    have h12' := (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr h12
    rw [hmax] at h12'
    exact lt_irrefl _ (h12'.trans_le (IsLocalRing.le_maximalIdeal (l ⟨2, by omega⟩).isPrime.ne_top))

variable [IsDomain R] [UniqueFactorizationMonoid R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Hartogs in dimension two**: for a local UFD of Krull dimension two, an element of the fraction
field lying in the localisation at every prime other than `0` and the maximal ideal lies in `R`. -/
theorem exists_eq_algebraMap_of_forall_ne_bot_ne_maximalIdeal (hdim : ringKrullDim R = 2) {f : K}
    (hf : ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≠ IsLocalRing.maximalIdeal R →
      MemLocalizationAt R K p f) :
    ∃ r : R, algebraMap R K r = f :=
  exists_eq_algebraMap_of_forall_heightOne R K fun p hp h1 =>
    hf p hp (ne_bot_of_height_eq_one R h1) (ne_maximalIdeal_of_height_eq_one R hdim h1)

theorem mem_range_iff_forall_ne_bot_ne_maximalIdeal (hdim : ringKrullDim R = 2) (f : K) :
    f ∈ Set.range (algebraMap R K) ↔
      ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≠ IsLocalRing.maximalIdeal R →
        MemLocalizationAt R K p f :=
  ⟨fun hf p hp _ _ => memLocalizationAt_of_mem_range R K p hp.ne_top hf,
    fun hf => exists_eq_algebraMap_of_forall_ne_bot_ne_maximalIdeal R K hdim hf⟩

end DimensionTwo

/-- Universe check at `Type`. -/
example (R₀ : Type) [CommRing R₀] [IsDomain R₀] [UniqueFactorizationMonoid R₀] (K₀ : Type) [Field K₀]
    [Algebra R₀ K₀] [IsFractionRing R₀ K₀] (f : K₀)
    (hf : ∀ p : Ideal R₀, p.IsPrime → p.height = 1 → MemLocalizationAt R₀ K₀ p f) :
    ∃ r : R₀, algebraMap R₀ K₀ r = f :=
  exists_eq_algebraMap_of_forall_heightOne R₀ K₀ hf

end KltDP.RingTheory.FactorialHartogs
