import KltDP.Geometry.PlaneBlowupNativeDifferentialBasis
import KltDP.Geometry.AffineBlowupChartBaseChangeEtale
import KltDP.Geometry.EtaleDifferentialBasisAlgHom

/-!
# Native coordinate bases on actual étale pullbacks of point-blowup charts

The input is an actual flat étale coordinate map from the original plane to
an original affine ring. Its center is the actual extended origin ideal.
At every prime of the original selected Rees chart, both a principal
neighborhood and the native parameter/fraction differential basis are derived.
There is no basis, chart isomorphism, or canonical formula premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.SmoothPointBlowupChartBasis

open AffineBlowup AffineBlowupChartBaseChange
open KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupSmooth

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)

abbrev chartRing := AffineBlowup.chartRing
  (Ideal.map φ.toRingHom (centerIdeal (k := k)))
  (mappedElement centerIdeal φ.toRingHom centerU)

local instance sourceAlgebra : Algebra k (reesChartRing k) :=
  (chartConstants (centerU (k := k))).toAlgebra

/-- The target chart's ground-ring map is the original composite through `S`. -/
def groundMap : k →+* chartRing k φ :=
  (AffineBlowup.chartBaseMap _ _).comp (algebraMap k S)

instance groundAlgebra : Algebra k (chartRing k φ) := (groundMap k φ).toAlgebra

/-- The actual exceptional parameter of the extended center. -/
def exceptionalParameter : chartRing k φ :=
  AffineBlowup.chartBaseMap _ _ (φ uCoord)

/-- The actual homogeneous fraction of the second center parameter by the first. -/
def fractionCoordinate : chartRing k φ :=
  chartFraction _ _ (mappedElement centerIdeal φ.toRingHom centerV)

/-- The original Rees chart map respects the original ground-field structure. -/
def chartMapAlgHom : reesChartRing k →ₐ[k] chartRing k φ where
  __ := AffineBlowupChartBaseChange.chartMap centerIdeal φ.toRingHom centerU
  commutes' r := by
    change AffineBlowupChartBaseChange.chartMap centerIdeal φ.toRingHom centerU
      (AffineBlowup.chartBaseMap centerIdeal centerU (algebraMap k (planeRing k) r)) = _
    rw [chartMap_baseMap]
    change AffineBlowup.chartBaseMap _ _ (φ (algebraMap k (planeRing k) r)) =
      AffineBlowup.chartBaseMap _ _ (algebraMap k S r)
    rw [φ.commutes]

theorem chartMapAlgHom_u : chartMapAlgHom k φ chartU = exceptionalParameter k φ :=
  chartMap_baseMap centerIdeal φ.toRingHom centerU uCoord

theorem chartMapAlgHom_w : chartMapAlgHom k φ chartW = fractionCoordinate k φ :=
  chartMap_fraction centerIdeal φ.toRingHom centerU centerV

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
    chartMap_isEtale centerIdeal φ.toRingHom centerU
  have hβ (i : Fin 2) : PlaneBlowupNativeDifferentialBasis.basis k i =
      KaehlerDifferential.D k (reesChartRing k) (![chartU, chartW] i) := by
    fin_cases i
    · exact PlaneBlowupNativeDifferentialBasis.basis_zero k
    · exact PlaneBlowupNativeDifferentialBasis.basis_one k
  obtain ⟨r, hr, β, hb⟩ :=
    EtaleDifferentialBasisRefinement.exists_coordinate_basis_away_of_algHom
      k (reesChartRing k) (chartRing k φ) (chartMapAlgHom k φ)
      (PlaneBlowupNativeDifferentialBasis.basis k) ![chartU, chartW] hβ p
  refine ⟨r, hr, β, ?_, ?_⟩
  · have h0 : β 0 = KaehlerDifferential.D k (Localization.Away r)
        (algebraMap (chartRing k φ) (Localization.Away r) (chartMapAlgHom k φ chartU)) := hb 0
    rwa [chartMapAlgHom_u] at h0
  · have h1 : β 1 = KaehlerDifferential.D k (Localization.Away r)
        (algebraMap (chartRing k φ) (Localization.Away r) (chartMapAlgHom k φ chartW)) := hb 1
    rwa [chartMapAlgHom_w] at h1

end KltDP.Geometry.SmoothPointBlowupChartBasis
