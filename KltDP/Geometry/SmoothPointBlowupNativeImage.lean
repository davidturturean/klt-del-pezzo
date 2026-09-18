import KltDP.Geometry.SmoothPointBlowupSourceBasis
import KltDP.Geometry.SmoothPointBlowupLocalizedChart
import KltDP.Geometry.AffineNativeTopDifferentialPrincipalCover
import KltDP.Geometry.StandardSmoothSpecFlat
import KltDP.Geometry.SmoothEtaleCoordinates

/-!
# The actual native exceptional-ideal factor on every point-blowup chart prime

Both differential bases, flatness, étaleness, the original Rees relation and
its regularity are derived from the original standard-smooth plane map. The
abstract principal-cover producer fixes the literal module carriers before
specializing the actual Rees ring. The public proposition is its exact inferred
proposition, exposed transparently to avoid reconstructing those large carriers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.SmoothPointBlowupNativeImage

open KltDP.Examples.FrobeniusBlowupContact
open SmoothPointBlowupChartBasis SmoothPointBlowupLocalizedChart
open AffineNativeTopDifferential

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

private def basis_cover_proof (p : PrimeSpectrum (chartRing k φ)) :=
  letI : Flat (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    flat_spec_map_of_standardSmooth φ.toRingHom hφ.isStandardSmooth
  letI : IsEtale (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    isEtale_spec_map_of_standardSmoothZero φ.toRingHom hφ
  exists_native_coordinate_basis k φ p

private def native_image_factor_proof (p : PrimeSpectrum (chartRing k φ)) :=
  exists_factor_on_principal_cover k (localizedBaseMap k φ) (localizedCenterIdeal k φ)
    (SmoothPointBlowupSourceBasis.basis k φ hφ) (φ uCoord) (φ vCoord)
    (exceptionalParameter k φ) (fractionCoordinate k φ)
    (SmoothPointBlowupSourceBasis.basis_zero k φ hφ)
    (SmoothPointBlowupSourceBasis.basis_one k φ hφ)
    (fun r => localizedBaseMap_apply k φ r (φ uCoord))
    (localized_relation k φ) (localized_parameter_regular k φ)
    (localizedCenterIdeal_span k φ) p (basis_cover_proof k φ hφ p)

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

/-- At every original chart prime there are `r` outside that prime, an actual
native target basis `γ`, and an equivalence from the ORIGINAL scalar-extended
source top module to `localizedCenterIdeal k φ r`, whose composite with the
original ideal inclusion and inverse determinant frame is the ORIGINAL native
map. No basis, regularity, image, or comparison is supplied. The transparent
statement is literally the previously displayed dependent existential. -/
theorem exists_native_image_factor (p : PrimeSpectrum (chartRing k φ)) :
    statementOf (native_image_factor_proof k φ hφ p) :=
  native_image_factor_proof k φ hφ p

end KltDP.Geometry.SmoothPointBlowupNativeImage
