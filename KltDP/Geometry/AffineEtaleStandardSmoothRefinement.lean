import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Actual principal étale coordinate refinements

The pinned scheme-étale predicate on an original affine map supplies a
unit-ideal family of actual principal target localizations on which that same
map is standard smooth of relative dimension zero. In particular every prime
has such a principal neighborhood. No cover or formal-étaleness conclusion is
assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.AffineEtaleStandardSmoothRefinement

universe u

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
variable [hEtale : IsEtale (Spec.map (CommRingCat.ofHom φ))]

include hEtale in
/-- The original affine map has a standard-smooth-zero principal cover. -/
theorem exists_standardSmoothZero_cover :
    ∃ s : Set B, Ideal.span s = ⊤ ∧
      ∀ r ∈ s, RingHom.IsStandardSmoothOfRelativeDimension 0
        ((algebraMap B (Localization.Away r)).comp φ) := by
  obtain ⟨s, hs, h⟩ := (HasRingHomProperty.Spec_iff (P := @IsSmoothOfRelativeDimension 0)
    (φ := CommRingCat.ofHom φ)).mp hEtale
  exact ⟨s, hs, h⟩

include hEtale in
/-- The neighborhood is derived for each original target prime. -/
theorem exists_standardSmoothZero_away (p : PrimeSpectrum B) :
    ∃ r : B, r ∉ p.asIdeal ∧
      RingHom.IsStandardSmoothOfRelativeDimension 0
        ((algebraMap B (Localization.Away r)).comp φ) := by
  obtain ⟨s, hs, h⟩ := exists_standardSmoothZero_cover φ
  have hex : ∃ r ∈ s, r ∉ p.asIdeal := by
    by_contra hn
    push_neg at hn
    have hle : Ideal.span s ≤ p.asIdeal := Ideal.span_le.mpr hn
    rw [hs] at hle
    exact p.isPrime.ne_top (top_unique hle)
  obtain ⟨r, hr, hpr⟩ := hex
  exact ⟨r, hpr, h r hr⟩

end KltDP.Geometry.AffineEtaleStandardSmoothRefinement
