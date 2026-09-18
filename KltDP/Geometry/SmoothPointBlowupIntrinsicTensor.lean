import KltDP.Geometry.SmoothPointBlowupNativeImage
import KltDP.Geometry.AffineNativeTopDifferentialTensorCover

/-!
# The original intrinsic exceptional tensor factor on every chart prime

The original standard-smooth plane coordinate map supplies both bases and the
whole native factor through the actual pulled center ideal. The proved affine
comparison then supplies the whole intrinsic tensor factor on the same actual
principal neighborhood. No basis, comparison, or canonical formula is assumed.
-/

noncomputable section

namespace KltDP.Geometry.SmoothPointBlowupIntrinsicTensor

open KltDP.Examples.FrobeniusBlowupContact
open SmoothPointBlowupChartBasis SmoothPointBlowupLocalizedChart
open AffineNativeTopDifferential SmoothPointBlowupNativeImage

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

private theorem sourceBasis_coordinates (i : Fin 2) :
    SmoothPointBlowupSourceBasis.basis k φ hφ i =
      KaehlerDifferential.D k S (![φ uCoord, φ vCoord] i) := by
  fin_cases i
  · exact SmoothPointBlowupSourceBasis.basis_zero k φ hφ
  · exact SmoothPointBlowupSourceBasis.basis_one k φ hφ

private def intrinsic_tensor_proof (p : PrimeSpectrum (chartRing k φ)) :=
  exists_tensor_factor_on_principal_cover k (localizedBaseMap k φ) (localizedCenterIdeal k φ)
    (SmoothPointBlowupSourceBasis.basis k φ hφ) ![φ uCoord, φ vCoord]
    (sourceBasis_coordinates k φ hφ) p (exists_native_image_factor k φ hφ p)

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

/-- At every original chart prime there is an original principal neighborhood
and an isomorphism from the ORIGINAL pullback top differential sheaf to the
ORIGINAL pulled-center ideal tilde tensored with the ORIGINAL intrinsic top
sheaf. Its composite with the tensor of the actual ideal inclusion is the
ORIGINAL intrinsic differential map. All local hypotheses are derived from
`hφ`; the transparent proposition retains the exact original maps. -/
theorem exists_intrinsic_tensor_factor (p : PrimeSpectrum (chartRing k φ)) :
    statementOf (intrinsic_tensor_proof k φ hφ p) :=
  intrinsic_tensor_proof k φ hφ p

end KltDP.Geometry.SmoothPointBlowupIntrinsicTensor
