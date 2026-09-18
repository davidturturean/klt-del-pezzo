import KltDP.RingTheory.NormalDenominatorWitness
import KltDP.RingTheory.PrimeDenominatorHeight

/-!
# Normal Noetherian domains are detected in codimension one

An actual fraction outside the ring has a prime denominator ideal above
its own. The determinant trick and the original prime-localization
height calculation make that prime height one. Regularity at this prime
contradicts the original denominator containment.
-/

noncomputable section

universe u v

namespace KltDP.RingTheory.NormalHartogs

open FactorialHartogs

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- A fraction regular at every actual height-one prime of a normal
Noetherian domain is an original ring element. -/
theorem exists_eq_algebraMap_of_forall_heightOne {f : K}
    (hf : ∀ P : Ideal R, P.IsPrime → P.height = 1 → MemLocalizationAt R K P f) :
    ∃ r : R, algebraMap R K r = f := by
  classical
  by_contra hnot
  obtain ⟨g, hP, hle⟩ := exists_prime_denominator_over R K f hnot
  letI : (denominatorIdeal R K g).IsPrime := hP
  obtain ⟨s, r, hs, hr, he⟩ := exists_denominator_witness R K g hP.ne_top
  have hheight := prime_denominator_height_eq_one_of_witness R K g s r hs hr he
  obtain ⟨a, b, hb, hab⟩ := hf (denominatorIdeal R K g) hP hheight
  exact hb (hle ⟨a, hab⟩)

/-- The converse uses the original constant denominator one. -/
theorem mem_range_iff_forall_heightOne (f : K) :
    f ∈ Set.range (algebraMap R K) ↔
      ∀ P : Ideal R, P.IsPrime → P.height = 1 → MemLocalizationAt R K P f :=
  ⟨fun hf P hP _ => memLocalizationAt_of_mem_range R K P hP.ne_top hf,
    fun hf => exists_eq_algebraMap_of_forall_heightOne R K hf⟩

/-- A fraction and its inverse regular at every height-one prime come
from an actual unit of the original normal domain. -/
theorem exists_unit_of_forall_heightOne (f : Kˣ)
    (hf : ∀ P : Ideal R, P.IsPrime → P.height = 1 →
      MemLocalizationAt R K P (f : K) ∧ MemLocalizationAt R K P (f⁻¹ : Kˣ)) :
    ∃ a : Rˣ, Units.map (algebraMap R K).toMonoidHom a = f := by
  obtain ⟨a, ha⟩ := exists_eq_algebraMap_of_forall_heightOne R K
    (fun P hP hheight => (hf P hP hheight).1)
  obtain ⟨b, hb⟩ := exists_eq_algebraMap_of_forall_heightOne R K
    (fun P hP hheight => (hf P hP hheight).2)
  have hab : a * b = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, ha, hb, Units.mul_inv, map_one]
  refine ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, ?_⟩
  exact Units.ext ha

end KltDP.RingTheory.NormalHartogs
