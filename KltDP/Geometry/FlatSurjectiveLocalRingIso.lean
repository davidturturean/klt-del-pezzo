import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! A flat, surjective map of actual local rings is an isomorphism. -/

noncomputable section

namespace KltDP.Geometry.FlatSurjectiveLocalRingIso

variable {A B : Type*} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]

/-- Faithful flatness of a local flat map gives injectivity; surjectivity then
identifies the original rings without changing the map. -/
theorem bijective (φ : A →+* B) [IsLocalHom φ]
    (hflat : φ.Flat) (hsurj : Function.Surjective φ) : Function.Bijective φ := by
  letI : Algebra A B := φ.toAlgebra
  letI : Module.Flat A B := hflat
  letI : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom φ)
  letI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨?_, hsurj⟩
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
  simpa only [Ideal.map_bot] using
    (Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (⊥ : Ideal A))

end KltDP.Geometry.FlatSurjectiveLocalRingIso
