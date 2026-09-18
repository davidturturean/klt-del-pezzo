import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Standard smooth principal neighborhoods in the original affine ring

The pinned scheme smoothness property is the local closure of standard
smoothness. Its existing localization theorem permits every model of the
selected principal localization, including the original quotient section
ring on an ambient basic open.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.SchemeSmoothPrincipalLocalization

variable {R B : Type u} [CommRing R] [CommRing B]

/-- Every point of the original smooth affine morphism has a principal
neighborhood standard smooth in every model of that localization. -/
theorem exists_away (n : ℕ) (φ : R →+* B)
    [IsSmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom φ))]
    (x : PrimeSpectrum B) :
    ∃ t : B, t ∉ x.asIdeal ∧
      ∀ (C : Type u) [CommRing C] [Algebra B C] [IsLocalization.Away t C],
        RingHom.IsStandardSmoothOfRelativeDimension n ((algebraMap B C).comp φ) := by
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) φ :=
    (HasRingHomProperty.Spec_iff (P := @IsSmoothOfRelativeDimension n)).mp
      (inferInstance : IsSmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom φ)))
  obtain ⟨s, hs, ht⟩ :=
    (RingHom.locally_iff_isLocalization
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso φ).mp hloc
  have hex : ∃ t ∈ s, t ∉ x.asIdeal := by
    by_contra! hn
    apply x.isPrime.ne_top
    apply top_unique
    rw [← hs]
    exact Ideal.span_le.mpr hn
  obtain ⟨t, hts, htx⟩ := hex
  exact ⟨t, htx, ht t hts⟩

/-- The ring-map predicate uses the existing algebra structure unchanged. -/
theorem standardSmooth_of_algebraMap (n : ℕ) [Algebra R B]
    (h : RingHom.IsStandardSmoothOfRelativeDimension n (algebraMap R B)) :
    Algebra.IsStandardSmoothOfRelativeDimension n R B := by
  have hAlg : (algebraMap R B).toAlgebra = ‹Algebra R B› := by
    ext
    rw [Algebra.smul_def]
    rfl
  rw [RingHom.IsStandardSmoothOfRelativeDimension, hAlg] at h
  exact h

end KltDP.Geometry.SchemeSmoothPrincipalLocalization
