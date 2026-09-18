import KltDP.Geometry.PushforwardBasicOpenLocalization
import KltDP.Geometry.ProperAffineSectionsFinite

/-!
# Original affine-base localization of global functions

The ring on the inverse image of the original principal open `D(r)` is
the localization of the original global ring at the exact original
`ProperAffineSections.baseScalar f r`. The algebra map is the original
structure-presheaf restriction. Quasi-compactness and quasi-separatedness
suffice; no Noetherian, field, integral, or reduced hypothesis is needed.
The finite-sections import supplies only the already defined scalar map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.ProperPushforwardLocalization

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))

/-- The original restriction of global functions to the inverse image of `D(r)`. -/
def topRestriction (r : R) :
    Γ(X, ⊤) ⟶ Γ(X, f ⁻¹ᵁ PrimeSpectrum.basicOpen r) :=
  X.presheaf.map (homOfLE le_top).op

/-- The inverse-image principal open uses exactly the original affine-base scalar. -/
theorem preimage_basicOpen (r : R) :
    f ⁻¹ᵁ PrimeSpectrum.basicOpen r =
      X.basicOpen (ProperAffineSections.baseScalar f r) := by
  rw [← basicOpen_eq_of_affine (R := CommRingCat.of R) r, Scheme.preimage_basicOpen_top]
  rfl

private theorem isLocalization_top_of_eq_basicOpen
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (r : Γ(X, ⊤)) {V : X.Opens} (e : V = X.basicOpen r) :
    @IsLocalization.Away _ _ r Γ(X, V) _
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.toAlgebra := by
  subst e
  convert isLocalization_basicOpen_of_qcqs (U := ⊤)
    CompactSpace.isCompact_univ isQuasiSeparated_univ r using 3

/-- Original global functions localize by the literal original restriction algebra. -/
theorem isLocalization_preimage_basicOpen [CompactSpace X] [QuasiSeparatedSpace X]
    (r : R) :
    letI := (topRestriction f r).hom.toAlgebra
    IsLocalization.Away (ProperAffineSections.baseScalar f r)
      Γ(X, f ⁻¹ᵁ PrimeSpectrum.basicOpen r) :=
  isLocalization_top_of_eq_basicOpen (ProperAffineSections.baseScalar f r)
    (preimage_basicOpen f r)

/-- A qcqs morphism to an arbitrary affine base has the original localization property. -/
theorem isLocalization_preimage_basicOpen_of_qcqs [QuasiCompact f] [QuasiSeparated f]
    (r : R) :
    letI := (topRestriction f r).hom.toAlgebra
    IsLocalization.Away (ProperAffineSections.baseScalar f r)
      Γ(X, f ⁻¹ᵁ PrimeSpectrum.basicOpen r) := by
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : QuasiSeparatedSpace X := (quasiSeparated_over_affine_iff f).mp inferInstance
  exact isLocalization_preimage_basicOpen f r

end KltDP.Geometry.ProperPushforwardLocalization
