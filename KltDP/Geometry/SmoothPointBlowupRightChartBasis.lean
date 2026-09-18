import KltDP.Geometry.PlaneBlowupRightNativeDifferentialBasis
import KltDP.Geometry.AffineBlowupChartBaseChangeEtale
import KltDP.Geometry.EtaleDifferentialBasisAlgHom

/-!
# Native coordinate bases on actual étale pullbacks of point-blowup charts

The complementary chart uses the actual selected second center generator.
The input is an actual flat étale coordinate map from the original plane to
an original affine ring. Its center is the actual extended origin ideal.
At every prime of the original selected Rees chart, both a principal
neighborhood and the native parameter/fraction differential basis are derived.
There is no basis, chart isomorphism, or canonical formula premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.SmoothPointBlowupRightChartBasis

open AffineBlowup AffineBlowupChartBaseChange
open KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupSmooth
open KltDP.Examples.FrobeniusBlowupDifferentialOverlap
open KltDP.Examples.FrobeniusBlowupDifferentialRightMap

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)

abbrev chartRing := AffineBlowup.chartRing
  (Ideal.map φ.toRingHom (centerIdeal (k := k)))
  (mappedElement centerIdeal φ.toRingHom centerV)

local instance sourceAlgebra : Algebra k (rightChartRing k) :=
  (chartConstants (centerV (k := k))).toAlgebra

/-- The target chart's ground-ring map is the original composite through `S`. -/
def groundMap : k →+* chartRing k φ :=
  (AffineBlowup.chartBaseMap _ _).comp (algebraMap k S)

instance groundAlgebra : Algebra k (chartRing k φ) := (groundMap k φ).toAlgebra

/-- The actual exceptional parameter of the extended center. -/
def exceptionalParameter : chartRing k φ :=
  AffineBlowup.chartBaseMap _ _ (φ vCoord)

/-- The original first center parameter divided by the selected second parameter. -/
def fractionCoordinate : chartRing k φ :=
  chartFraction _ _ (mappedElement centerIdeal φ.toRingHom centerU)

/-- The original Rees chart map respects the original ground-field structure. -/
def chartMapAlgHom : rightChartRing k →ₐ[k] chartRing k φ where
  __ := AffineBlowupChartBaseChange.chartMap centerIdeal φ.toRingHom centerV
  commutes' r := by
    change AffineBlowupChartBaseChange.chartMap centerIdeal φ.toRingHom centerV
      (AffineBlowup.chartBaseMap centerIdeal centerV (algebraMap k (planeRing k) r)) = _
    rw [chartMap_baseMap]
    change AffineBlowup.chartBaseMap _ _ (φ (algebraMap k (planeRing k) r)) =
      AffineBlowup.chartBaseMap _ _ (algebraMap k S r)
    rw [φ.commutes]

theorem chartMapAlgHom_v : chartMapAlgHom k φ (rightV (k := k)) = exceptionalParameter k φ :=
  chartMap_baseMap centerIdeal φ.toRingHom centerV vCoord

theorem chartMapAlgHom_s : chartMapAlgHom k φ (rightS (k := k)) = fractionCoordinate k φ :=
  chartMap_fraction centerIdeal φ.toRingHom centerV centerU

variable [hFlat : Flat (Spec.map (CommRingCat.ofHom φ.toRingHom))]
variable [hEtale : IsEtale (Spec.map (CommRingCat.ofHom φ.toRingHom))]

include hFlat hEtale in
/-- The local basis is derived at every original chart prime. Its two vectors
are the native differentials of the original exceptional parameter and fraction. -/
theorem exists_native_coordinate_basis (p : PrimeSpectrum (chartRing k φ)) :
    ∃ r : chartRing k φ, r ∉ p.asIdeal ∧
      ∃ β : Basis (Fin 2) (Localization.Away r)
          (KaehlerDifferential k (Localization.Away r)),
        β 0 = KaehlerDifferential.D k (Localization.Away r)
          (algebraMap (chartRing k φ) (Localization.Away r) (exceptionalParameter k φ)) ∧
        β 1 = KaehlerDifferential.D k (Localization.Away r)
          (algebraMap (chartRing k φ) (Localization.Away r) (fractionCoordinate k φ)) := by
  letI : IsEtale (Spec.map (CommRingCat.ofHom (chartMapAlgHom k φ).toRingHom)) :=
    chartMap_isEtale centerIdeal φ.toRingHom centerV
  have hβ (i : Fin 2) : PlaneBlowupRightNativeDifferentialBasis.basis k i =
      KaehlerDifferential.D k (rightChartRing k) (![(rightV (k := k)), (rightS (k := k))] i) := by
    fin_cases i
    · exact PlaneBlowupRightNativeDifferentialBasis.basis_zero k
    · exact PlaneBlowupRightNativeDifferentialBasis.basis_one k
  obtain ⟨r, hr, β, hb⟩ :=
    EtaleDifferentialBasisRefinement.exists_coordinate_basis_away_of_algHom
      k (rightChartRing k) (chartRing k φ) (chartMapAlgHom k φ)
      (PlaneBlowupRightNativeDifferentialBasis.basis k) ![(rightV (k := k)), (rightS (k := k))] hβ p
  refine ⟨r, hr, β, ?_, ?_⟩
  · have h0 : β 0 = KaehlerDifferential.D k (Localization.Away r)
        (algebraMap (chartRing k φ) (Localization.Away r) (chartMapAlgHom k φ (rightV (k := k)))) := hb 0
    rwa [chartMapAlgHom_v] at h0
  · have h1 : β 1 = KaehlerDifferential.D k (Localization.Away r)
        (algebraMap (chartRing k φ) (Localization.Away r) (chartMapAlgHom k φ (rightS (k := k)))) := hb 1
    rwa [chartMapAlgHom_s] at h1

end KltDP.Geometry.SmoothPointBlowupRightChartBasis
