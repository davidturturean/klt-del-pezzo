import KltDP.Geometry.AffineEtaleStandardSmoothRefinement
import KltDP.Geometry.EtaleDifferentialBasisTransport

/-!
# Derived native differential frames on principal étale refinements

For the original étale affine map, the principal neighborhood and its native
differential basis are both derived. The source basis is transported by the
original scalar-extension differential, and coordinate differentials remain
the differentials of the actual composite ring-map images.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.EtaleDifferentialBasisRefinement

universe u v

variable (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
variable [hEtale : IsEtale (Spec.map (CommRingCat.ofHom (algebraMap A B)))]

include hEtale in
/-- Every original prime admits a principal neighborhood with a native basis
whose vectors are derived from the original source basis. -/
theorem exists_basis_away {ι : Type v} (β : Basis ι A (KaehlerDifferential k A))
    (p : PrimeSpectrum B) :
    ∃ r : B, r ∉ p.asIdeal ∧
      ∃ γ : Basis ι (Localization.Away r) (KaehlerDifferential k (Localization.Away r)),
        ∀ i, γ i = KaehlerDifferential.mapBaseChange k A (Localization.Away r)
          (1 ⊗ₜ[A] β i) := by
  obtain ⟨r, hr, hs⟩ :=
    AffineEtaleStandardSmoothRefinement.exists_standardSmoothZero_away (algebraMap A B) p
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 A (Localization.Away r) := by
    have ha : (algebraMap A (Localization.Away r)).toAlgebra =
        (inferInstance : Algebra A (Localization.Away r)) := by
      ext
      rw [Algebra.smul_def]
      rfl
    rw [← IsScalarTower.algebraMap_eq A B (Localization.Away r),
      RingHom.IsStandardSmoothOfRelativeDimension, ha] at hs
    exact hs
  refine ⟨r, hr, EtaleDifferentialBasisTransport.basis k A (Localization.Away r) β, ?_⟩
  exact EtaleDifferentialBasisTransport.basis_apply k A (Localization.Away r) β

include hEtale in
/-- If the source basis is the differentials of actual functions, so is the
derived basis on each actual principal target neighborhood. -/
theorem exists_coordinate_basis_away {ι : Type v}
    (β : Basis ι A (KaehlerDifferential k A)) (x : ι → A)
    (hx : ∀ i, β i = KaehlerDifferential.D k A (x i)) (p : PrimeSpectrum B) :
    ∃ r : B, r ∉ p.asIdeal ∧
      ∃ γ : Basis ι (Localization.Away r) (KaehlerDifferential k (Localization.Away r)),
        ∀ i, γ i = KaehlerDifferential.D k (Localization.Away r)
          (algebraMap B (Localization.Away r) (algebraMap A B (x i))) := by
  obtain ⟨r, hr, γ, hγ⟩ := exists_basis_away k A B β p
  refine ⟨r, hr, γ, fun i => ?_⟩
  rw [hγ, hx, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]
  exact congrArg (KaehlerDifferential.D k (Localization.Away r))
    (IsScalarTower.algebraMap_apply A B (Localization.Away r) (x i))

end KltDP.Geometry.EtaleDifferentialBasisRefinement
