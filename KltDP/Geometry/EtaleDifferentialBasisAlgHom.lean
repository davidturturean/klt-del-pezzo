import KltDP.Geometry.EtaleDifferentialBasisRefinement

/-! The native principal-basis refinement for an explicit original algebra homomorphism. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.EtaleDifferentialBasisRefinement

universe u v

variable (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B]

/-- All scalar structures used for the transport are induced by the supplied
original algebra homomorphism. The output retains its literal values. -/
theorem exists_coordinate_basis_away_of_algHom (φ : A →ₐ[k] B)
    [hEtale : IsEtale (Spec.map (CommRingCat.ofHom φ.toRingHom))]
    {ι : Type v} (β : Basis ι A (KaehlerDifferential k A)) (x : ι → A)
    (hx : ∀ i, β i = KaehlerDifferential.D k A (x i)) (p : PrimeSpectrum B) :
    ∃ r : B, r ∉ p.asIdeal ∧
      ∃ γ : Basis ι (Localization.Away r) (KaehlerDifferential k (Localization.Away r)),
        ∀ i, γ i = KaehlerDifferential.D k (Localization.Away r)
          (algebraMap B (Localization.Away r) (φ (x i))) := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  letI : IsEtale (Spec.map (CommRingCat.ofHom (algebraMap A B))) := hEtale
  exact exists_coordinate_basis_away k A B β x hx p

end KltDP.Geometry.EtaleDifferentialBasisRefinement
