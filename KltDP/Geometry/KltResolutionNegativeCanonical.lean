import KltDP.Geometry.BirationalAnticanonicalPairingSign
import KltDP.Geometry.NegativeCanonicalSurfaceInvariants
import KltDP.Geometry.DelPezzoType

/-!
# Actual canonical negativity on resolutions of klt del Pezzo surfaces

The original del Pezzo condition supplies the ample anticanonical numerator.
Its actual pullback is nef and pairs negatively with a canonical divisor on
the original resolution. No rationality or numerical formula is assumed.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u

namespace KltDP.Geometry.IsResolution

open NormalProjectiveSurface SmoothCanonicalCartierRepresentative

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

local instance originalResolutionIntegral (T : NormalProjectiveSurface k) :
    IsIntegral T.toScheme := T.integral

/-- The original resolution has an actual canonical divisor with negative
pairing against an actual nef line, derived from the del Pezzo condition. -/
theorem exists_nef_canonical_negative_of_kltDelPezzo
    (hres : IsResolution S X π) (hDP : IsKltDelPezzo X) :
    ∃ (K : CartierDivisor S.toScheme)
      (_ : cartierDivisorModule S.toScheme K ≅
        relativeDifferentialExterior S.structureMorphism 2)
      (H : InvertibleSheaf S.toScheme),
      Positivity.IsNef S.structureMorphism H ∧
      S.picardPairing hres.regular (cartierPicardClass S.toScheme K) H.toPic < 0 := by
  letI : IsProper π := hres.isProper
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hres.regular
  have hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hres.birational
  obtain ⟨KX, hKX, n, hn, A, hA, hample⟩ := (isLogDelPezzoPair_zero_iff X).mp hDP
  have hAW : X.cartierToWeilHom A = n • (-KX) := by
    apply rationalizeWeilDivisor_injective
    simpa only [map_nsmul, map_neg] using hA
  let H := pullbackInvertibleSheaf π (cartierDivisorInvertibleSheaf X.toScheme A)
  have hnegative := BirationalAnticanonicalPairingSign.canonical_picardPairing_pullback_neg
    π hres.over_base hbir hres.regular KX hKX.1 n hn A hAW hample
  have hPicard : schemePicardPullbackHom π (cartierPicardClass X.toScheme A) = H.toPic := by
    change schemePicardPullbackHom π (cartierDivisorInvertibleSheaf X.toScheme A).toPic = H.toPic
    exact schemePicardPullbackHom_toPic π (cartierDivisorInvertibleSheaf X.toScheme A)
  rw [hPicard] at hnegative
  have hsemi : Positivity.IsSemiample H :=
    AmplePullbackNef.isSemiample_pullback_of_isAmple π
      (cartierDivisorInvertibleSheaf X.toScheme A) hample
  exact ⟨cartierRepresentative S.structureMorphism,
    SmoothCanonicalCartierExterior.representativeIsoExterior S.structureMorphism,
    H, AmpleNefUnconditional.isNef_of_isSemiample S H hsemi, hnegative⟩

/-- Both invariant formulas hold on the original resolution for any actual
canonical representative; rationality of the resolution is not an input. -/
theorem noether_euler_relations_of_kltDelPezzo
    (hres : IsResolution S X π) (hDP : IsKltDelPezzo X)
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2) :
    (S.intersectionPairing hres.regular K K + (S.picardRank : ℤ) =
      10 - 8 * (cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 : ℤ)) ∧
    (eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) =
      1 - (cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 : ℤ)) := by
  obtain ⟨K₀, eK₀, H, hH, hnegative⟩ :=
    hres.exists_nef_canonical_negative_of_kltDelPezzo hDP
  have heq := cartierPicardClass_eq_of_iso S.toScheme K₀ K (eK₀ ≪≫ eK.symm)
  rw [heq] at hnegative
  exact S.noether_euler_relations_of_negative_nef hres.regular K eK H hH hnegative

end KltDP.Geometry.IsResolution

#check @KltDP.Geometry.IsResolution.exists_nef_canonical_negative_of_kltDelPezzo
#print axioms KltDP.Geometry.IsResolution.exists_nef_canonical_negative_of_kltDelPezzo
#print axioms KltDP.Geometry.IsResolution.noether_euler_relations_of_kltDelPezzo
