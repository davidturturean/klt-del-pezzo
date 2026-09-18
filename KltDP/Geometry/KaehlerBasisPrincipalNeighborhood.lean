import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.CotangentComplex
import KltDP.Geometry.AffineTopDifferentialFrame

/-!
# Spreading the original native Kähler basis

Pinned finite-presentation spreading preserves every vector of the supplied
localized basis. The canonical Kähler localization equivalence turns the
result into a basis of the native differentials on a principal neighborhood.
The map back is the original localization map, characterized on all numerator
differentials. No smoothness or canonical-divisor assertion is an input.
-/

noncomputable section

namespace KltDP.Geometry.KaehlerBasisPrincipalNeighborhood

universe u v

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The canonical localization equivalence, with the actual localized scalars. -/
def nativeLocalizationEquiv (S : Submonoid A) :
    LocalizedModule S (KaehlerDifferential k A) ≃ₗ[Localization S]
      KaehlerDifferential k (Localization S) :=
  (IsLocalizedModule.iso S
    (KaehlerDifferential.map k k A (Localization S))).extendScalarsOfIsLocalization
      S (Localization S)

variable (S : Submonoid A) (T : Type u) [CommRing T]
    [Algebra A T] [Algebra k T] [IsScalarTower k A T] [IsLocalization S T]

/-- The original native restriction from a principal localization to T. -/
def nativeRestriction (r : A) (hr : r ∈ S) :
    KaehlerDifferential k (Localization.Away r) →ₗ[A] KaehlerDifferential k T :=
  IsLocalizedModule.liftOfLE (.powers r) S (Submonoid.powers_le.mpr hr)
    (KaehlerDifferential.map k k A (Localization.Away r))
    (KaehlerDifferential.map k k A T)

/-- The restriction uses the original algebra maps on numerator differentials. -/
theorem nativeRestriction_D (r : A) (hr : r ∈ S) (a : A) :
    nativeRestriction k A S T r hr
      (KaehlerDifferential.D k (Localization.Away r)
        (algebraMap A (Localization.Away r) a)) =
      KaehlerDifferential.D k T (algebraMap A T a) := by
  simpa only [KaehlerDifferential.map_D] using
    (IsLocalizedModule.liftOfLE_apply (.powers r) S (Submonoid.powers_le.mpr hr)
      (KaehlerDifferential.map k k A (Localization.Away r))
      (KaehlerDifferential.map k k A T) (KaehlerDifferential.D k A a))

/-- A finitely presented native Kähler module spreads the very same basis
to one principal neighborhood, with exact vectorwise germ compatibility. -/
theorem exists_native_basis [Module.FinitePresentation A (KaehlerDifferential k A)]
    {I : Type v} [Finite I] (b : Basis I T (KaehlerDifferential k T)) :
    ∃ (r : A) (hr : r ∈ S)
      (b' : Basis I (Localization.Away r) (KaehlerDifferential k (Localization.Away r))),
      ∀ i, nativeRestriction k A S T r hr (b' i) = b i := by
  obtain ⟨r, hr, b', hb'⟩ :=
    Module.FinitePresentation.exists_basis_localizedModule_powers S
      (KaehlerDifferential.map k k A T) T b
  refine ⟨r, hr, b'.map (nativeLocalizationEquiv k A (.powers r)), ?_⟩
  intro i
  change IsLocalizedModule.lift (.powers r)
    (KaehlerDifferential.map k k A (Localization.Away r))
    (KaehlerDifferential.map k k A T) _
    ((IsLocalizedModule.iso (.powers r)
      (KaehlerDifferential.map k k A (Localization.Away r))) (b' i)) = b i
  rw [IsLocalizedModule.lift_iso]
  exact hb' i

/-- The native rank-two frame is primitive on that actual principal neighborhood. -/
theorem exists_native_basis_primitive
    [Module.FinitePresentation A (KaehlerDifferential k A)]
    (b : Basis (Fin 2) T (KaehlerDifferential k T)) :
    ∃ (r : A) (hr : r ∈ S)
      (b' : Basis (Fin 2) (Localization.Away r)
        (KaehlerDifferential k (Localization.Away r))),
      (∀ i, nativeRestriction k A S T r hr (b' i) = b i) ∧
      AffineTopDifferentialFrame.determinantEquiv b'
        (exteriorPower.ιMulti (Localization.Away r) 2 b') = 1 := by
  obtain ⟨r, hr, b', hb'⟩ := exists_native_basis k A S T (I := Fin 2) b
  exact ⟨r, hr, b', hb', AffineTopDifferentialFrame.determinantEquiv_basis_wedge b'⟩

end KltDP.Geometry.KaehlerBasisPrincipalNeighborhood
