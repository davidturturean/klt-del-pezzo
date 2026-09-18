import Mathlib.RingTheory.Localization.AtPrime

/-!
# Original numerators for actual local parameters

Every element of the maximal ideal of the original prime localization
is a unit multiple of an element of the original prime ideal. The unit
is the image of an actual localization denominator. This supplies the
literal scalar equation needed to compare a given local parameter chart
with a chart at an original numerator.
-/

noncomputable section

namespace KltDP.Geometry.LocalizedParameterNumerator

universe u

variable {R : Type u} [CommRing R] (m : Ideal R) [m.IsPrime]

/-- An actual local parameter has an original numerator in the original
prime ideal and an actual denominator unit. -/
theorem exists_original_numerator
    (f : IsLocalRing.maximalIdeal (Localization.AtPrime m)) :
    ∃ r : m, ∃ v : (Localization.AtPrime m)ˣ,
      algebraMap R (Localization.AtPrime m) (r : R) =
        (v : Localization.AtPrime m) * (f : Localization.AtPrime m) := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj m.primeCompl
    (f : Localization.AtPrime m)
  obtain ⟨v, hv⟩ := IsLocalization.map_units (Localization.AtPrime m) s
  have hmem : algebraMap R (Localization.AtPrime m) r ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
    rw [← hrs]
    exact (IsLocalRing.maximalIdeal (Localization.AtPrime m)).mul_mem_right _ f.property
  have hr : r ∈ m :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m r).mp hmem
  refine ⟨⟨r, hr⟩, v, ?_⟩
  calc
    _ = (f : Localization.AtPrime m) * algebraMap R (Localization.AtPrime m) (s : R) :=
      hrs.symm
    _ = _ := by rw [← hv, mul_comm]

end KltDP.Geometry.LocalizedParameterNumerator
