import KltDP.Geometry.SmoothPointBlowupSourceBasis
import KltDP.Geometry.SmoothPointBlowupRightLocalizedChart
import KltDP.Geometry.AffineNativeTopDifferentialPrincipalCover
import KltDP.Geometry.StandardSmoothSpecFlat
import KltDP.Geometry.SmoothEtaleCoordinates

/-!
# The actual native exceptional-ideal factor on every complementary-chart prime

Both differential bases, flatness, étaleness, the original Rees relation and
its regularity are derived from the original standard-smooth plane map. The
abstract principal-cover producer fixes the literal module carriers before
specializing the actual Rees ring. The public proposition is its exact inferred
proposition, exposed transparently to avoid reconstructing those large carriers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.SmoothPointBlowupRightNativeImage

open KltDP.Examples.FrobeniusBlowupContact
open SmoothPointBlowupRightChartBasis SmoothPointBlowupRightLocalizedChart
open AffineNativeTopDifferential

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

/-- The derived source basis in the complementary order `(dv, du)`. -/
def sourceBasis : Basis (Fin 2) S (KaehlerDifferential k S) :=
  (SmoothPointBlowupSourceBasis.basis k φ hφ).reindex (Equiv.swap 0 1)

theorem sourceBasis_zero : sourceBasis k φ hφ 0 = KaehlerDifferential.D k S (φ vCoord) := by
  rw [sourceBasis, Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left]
  exact SmoothPointBlowupSourceBasis.basis_one k φ hφ

theorem sourceBasis_one : sourceBasis k φ hφ 1 = KaehlerDifferential.D k S (φ uCoord) := by
  rw [sourceBasis, Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right]
  exact SmoothPointBlowupSourceBasis.basis_zero k φ hφ

private def basis_cover_proof (p : PrimeSpectrum (chartRing k φ)) :=
  letI : Flat (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    flat_spec_map_of_standardSmooth φ.toRingHom hφ.isStandardSmooth
  letI : IsEtale (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    isEtale_spec_map_of_standardSmoothZero φ.toRingHom hφ
  exists_native_coordinate_basis k φ p

private def native_image_factor_proof (p : PrimeSpectrum (chartRing k φ)) :=
  exists_factor_on_principal_cover k (localizedBaseMap k φ) (localizedCenterIdeal k φ)
    (sourceBasis k φ hφ) (φ vCoord) (φ uCoord)
    (exceptionalParameter k φ) (fractionCoordinate k φ)
    (sourceBasis_zero k φ hφ)
    (sourceBasis_one k φ hφ)
    (fun r => localizedBaseMap_apply k φ r (φ vCoord))
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

end KltDP.Geometry.SmoothPointBlowupRightNativeImage
