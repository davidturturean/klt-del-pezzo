import KltDP.Geometry.SmoothPointBlowupAffineCanonicalCharts
import KltDP.Geometry.AffineBlowupPrincipalRefinementCover
import KltDP.Geometry.SchemeModuleMonicFactorOnCharts
import KltDP.Geometry.AffinePlaneEtaleBlowupSmooth

/-!
# The original global canonical factor on a centered étale affine blowup

Both actual Rees generator charts supply their original principal refinements
and normalized local factors. The original global monic-factor construction
then gives the factor of the original blowdown differential through the
original exceptional kernel tensor. Smoothness, chart coverage, and all local
compatibilities are derived from the original standard-smooth coordinate map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor

open AffineBlowup AffineBlowupChartBaseChange AffineBlowupTopDifferential
open AffineNativeTopDifferential
open KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupSmooth

local instance affineFinalModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)

variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

include hφ in
/-- Actual smooth relative dimension two, for the same original ground-field map. -/
theorem structureMap_isSmoothTwo :
    IsSmoothOfRelativeDimension 2 (structureMap k S (extendedCenter k φ)) := by
  letI : Flat (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    flat_spec_map_of_standardSmooth φ.toRingHom hφ.isStandardSmooth
  letI : IsEtale (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    isEtale_spec_map_of_standardSmoothZero φ.toRingHom hφ
  have h := AffinePlaneEtaleBlowupSmooth.isSmoothOfRelativeDimension_two φ.toRingHom
  have hc : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ planeStructure =
      Spec.map (CommRingCat.ofHom (algebraMap k S)) :=
    AffineNativeTopDifferential.spec_comp k φ
  rw [hc] at h
  exact h

/-- The original global blowdown top sheaf factors through the actual exceptional ideal tensor. -/
def canonicalFactorIso :
    (schemeModulePullback (toSpec (extendedCenter k φ))).obj (intrinsic k S 2) ≅
      exceptionalTensor k S (extendedCenter k φ) := by
  letI := structureMap_isSmoothTwo k φ hφ
  letI := exceptionalInclusion_mono k S (extendedCenter k φ)
  exact schemeModuleMonicFactorIsoOnOpenCharts
    (principalRefinementScheme (extendedCenter k φ) (generator k φ) (refinement k φ hφ))
    (principalRefinementMap (extendedCenter k φ) (generator k φ) (refinement k φ hφ))
    (principalRefinementMap_jointly_surjective (extendedCenter k φ) (generator k φ)
      (refinement k φ hφ) (span_generator k φ) (refinement_not_mem k φ hφ))
    (exceptionalInclusion k S (extendedCenter k φ)) (blowdownMap k S (extendedCenter k φ))
    (factorIso k φ hφ) (factorIso_factor k φ hφ)

/-- The isomorphism retains the whole original exterior differential of the original blowdown. -/
theorem canonicalFactorIso_comp :
    (canonicalFactorIso k φ hφ).hom ≫ exceptionalInclusion k S (extendedCenter k φ) =
      blowdownMap k S (extendedCenter k φ) := by
  letI := structureMap_isSmoothTwo k φ hφ
  letI := exceptionalInclusion_mono k S (extendedCenter k φ)
  exact schemeModuleMonicFactorIsoOnOpenCharts_comp
    (principalRefinementScheme (extendedCenter k φ) (generator k φ) (refinement k φ hφ))
    (principalRefinementMap (extendedCenter k φ) (generator k φ) (refinement k φ hφ))
    (principalRefinementMap_jointly_surjective (extendedCenter k φ) (generator k φ)
      (refinement k φ hφ) (span_generator k φ) (refinement_not_mem k φ hφ))
    (exceptionalInclusion k S (extendedCenter k φ)) (blowdownMap k S (extendedCenter k φ))
    (factorIso k φ hφ) (factorIso_factor k φ hφ)

end KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor
