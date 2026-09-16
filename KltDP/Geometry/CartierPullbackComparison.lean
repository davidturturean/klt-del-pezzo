import KltDP.Geometry.CartierPullbackChartFrames
import KltDP.Geometry.SchemeModuleMonicFactorOnCover

/-!
# The Picard compatibility of the Cartier-divisor pullback, in general

Fourth and last module of the general Cartier comparison.  For a generic-point-preserving morphism
`π : X ⟶ Y` of integral schemes and an effective Cartier divisor `D` on `Y` with regular equations,
the compatible chart pairs of `CartierPullbackFrameCharts.exists_compatible_charts` cover `X`, and on
each of them the two ideal modules were identified, compatibly with their inclusions into the
structure module, in `CartierPullbackChartFrames.chartComparisonIso(_map)`.  The accepted
`schemeModuleMonicFactorIsoOnOpenCover` glues these local identifications into

  `π^* I_D ≅ I_{π^*D}`   (`pullbackKernelIso`),

and feeding that into the compiled `cartierPicardHom_pullbackDivisor_eq_picardPullback` closes the
gap that lanes A1 and A2 need:

  `cartierPicardHom X (pullbackDivisor π D hD) = schemePicardPullbackHom π (cartierPicardHom Y D)`
                                               (`cartierPicardHom_pullbackDivisor_eq`).

This is the first case of the identity for a morphism which is neither an open immersion nor an
isomorphism over an open containing the divisor: no flatness, openness or isomorphism hypothesis is
used, only that `π` preserves the generic point and that `D` has regular equations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierPullbackComparison

open KltDP.Geometry KltDP.Geometry.CartierPullbackFrameCharts
  KltDP.Geometry.CartierPullbackChartFrames KltDP.Geometry.CartierDivisorPullbackIdeal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y)
  [GenericPointPreserving π] (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)

/-! ### A chosen compatible chart pair around every point -/

/-- A compatible pair of affine charts around a point of `X`: a regular chart of `D`, an affine open
of `Y` inside it, and an affine open of `X` inside the preimage containing the point. -/
structure ChartPair (x : X) where
  /-- The regular equation chart of `D`. -/
  eqChart : RegularCartierEquationChart Y D
  /-- The affine open of `Y` inside that chart. -/
  baseOpen : Y.affineOpens
  /-- The affine open of `X` inside its preimage. -/
  srcOpen : X.affineOpens
  /-- The affine open of `Y` lies in the chart. -/
  baseOpen_le : baseOpen.1 ≤ eqChart.chart.openSet
  /-- The point lies in the affine open of `X`. -/
  mem_srcOpen : x ∈ srcOpen.1
  /-- The affine open of `X` lies in the preimage. -/
  srcOpen_le : srcOpen.1 ≤ π ⁻¹ᵁ baseOpen.1

/-- A chosen compatible chart pair around each point, from the compiled
`exists_compatible_charts`. -/
def chartPair (x : X) : ChartPair π D x :=
  Classical.choice (by
    obtain ⟨c, V, W, hV, hx, hW⟩ := exists_compatible_charts π D hD x
    exact ⟨⟨c, V, W, hV, hx, hW⟩⟩)

instance chartPair_nonempty_src (x : X) : Nonempty (chartPair π D hD x).srcOpen.1 :=
  ⟨⟨x, (chartPair π D hD x).mem_srcOpen⟩⟩

instance chartPair_nonempty_base (x : X) : Nonempty (chartPair π D hD x).baseOpen.1 :=
  ⟨⟨π.base x, (chartPair π D hD x).srcOpen_le (chartPair π D hD x).mem_srcOpen⟩⟩

/-- The chosen affine open of `X` lies in the preimage of the chosen regular chart. -/
theorem chartPair_le_chart (x : X) :
    (chartPair π D hD x).srcOpen.1 ≤ π ⁻¹ᵁ (chartPair π D hD x).eqChart.chart.openSet := by
  intro z hz
  exact (chartPair π D hD x).baseOpen_le ((chartPair π D hD x).srcOpen_le hz)

/-! ### The cover and the global comparison -/

/-- The affine cover of `X` by the chosen charts. -/
def comparisonCover (x : X) : X.Opens := (chartPair π D hD x).srcOpen.1

theorem comparisonCover_covers (x : X) : ∃ y : X, x ∈ comparisonCover π D hD y :=
  ⟨x, (chartPair π D hD x).mem_srcOpen⟩

local instance pullbackKernelι_mono :
    Mono (schemeKernelIdealι (pullbackIdealData π D hD).gluedTo) := by
  unfold schemeKernelIdealι
  infer_instance

set_option maxHeartbeats 4000000 in
/-- **The ideal sheaf of the pulled-back divisor is the inverse image of the ideal sheaf of `D`.** -/
def pullbackKernelIso :
    (schemeModulePullback π).obj
        (schemeKernelIdeal (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo) ≅
      schemeKernelIdeal (pullbackIdealData π D hD).gluedTo :=
  schemeModuleMonicFactorIsoOnOpenCover (comparisonCover π D hD)
    (comparisonCover_covers π D hD)
    (schemeKernelIdealι (pullbackIdealData π D hD).gluedTo)
    (pulledKernelInclusion
      (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo π)
    (fun x => chartComparisonIso π D hD (chartPair π D hD x).eqChart
      (chartPair π D hD x).baseOpen (chartPair π D hD x).baseOpen_le
      (chartPair π D hD x).srcOpen (chartPair π D hD x).srcOpen_le
      (chartPair_le_chart π D hD x))
    (fun x => chartComparisonIso_map π D hD (chartPair π D hD x).eqChart
      (chartPair π D hD x).baseOpen (chartPair π D hD x).baseOpen_le
      (chartPair π D hD x).srcOpen (chartPair π D hD x).srcOpen_le
      (chartPair_le_chart π D hD x))

set_option maxHeartbeats 4000000 in
/-- **The Picard class of a pulled-back Cartier divisor is the Picard pullback of its class.** -/
theorem cartierPicardHom_pullbackDivisor_eq :
    cartierPicardHom X (pullbackDivisor π D hD) =
      (schemePicardPullbackHom π).toAdditive (cartierPicardHom Y D) :=
  cartierPicardHom_pullbackDivisor_eq_picardPullback π D hD (pullbackKernelIso π D hD)

end KltDP.Geometry.CartierPullbackComparison
