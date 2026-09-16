import KltDP.Examples.FrobeniusStageOneEmbedding

/-!
# The five chart maps of stage `1` are closed immersions into their `P⁷` charts

A tuple `r : Fin 8 → k[u][v]` normalised at `m` whose entries include the two coordinates `u`, `v`
has a surjective chart ring map `tupleChartHom 7 planeConstants r m : A_{(z_m)} →+* k[u][v]`
(explicit right inverse `planeToChartOf`, `u ↦ z_{iu}/z_m`, `v ↦ z_{iv}/z_m`), so the map
`tupleSpec` into the chart `D(z_m)` is a closed immersion (pinned `IsClosedImmersion.spec_of_surjective`).
For each of the five charts of stage `1` the coordinates are entries of its monomial tuple
(`stageOneData_tuple_u`, `stageOneData_tuple_v`), hence `chartTupleSpec c` is a closed immersion
(`chartTupleSpec_isClosedImmersion`) and `chartTupleMorphism c = chartTupleSpec c ≫ chart (ni c)`
(`chartTupleMorphism_eq`).

These are the closed-immersion halves of the five chart squares of `stageOneEmbedding` over the
charts `D(z_{ni c})` of `P⁷`; the range identities and the three remaining charts of `P⁷` are not
treated here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStageOneClosed

open KltDP.Geometry KltDP.Geometry.ProjectiveChart
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
open FrobeniusStageOneCharts FrobeniusStageOneTuples FrobeniusStageOneTuples.ChartTuple

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

section Generic

variable (r : Fin 8 → planeRing k) (m : Fin 8) (hm : r m = 1) (iu iv : Fin 8)

/-- The right inverse `u ↦ z_{iu}/z_m`, `v ↦ z_{iv}/z_m`, constants to constants. -/
def planeToChartOf : planeRing k →+* coordinateChartRing k 7 m :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (coordinateChartConstants k 7 m) (chartFraction k 7 m iu))
    (chartFraction k 7 m iv)

variable (hu : r iu = uCoord) (hv : r iv = vCoord)

include hu hv in
theorem tupleChartHom_comp_planeToChartOf :
    (tupleChartHom 7 planeConstants r m hm).comp (planeToChartOf (k := k) m iu iv) =
      RingHom.id (planeRing k) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro a
      simp [planeToChartOf, planeConstants]
    · simp [planeToChartOf, uCoord, hu]
  · simp [planeToChartOf, vCoord, hv]

include hu hv in
/-- A tuple containing both coordinates has a surjective chart ring map. -/
theorem tupleChartHom_surjective_of :
    Function.Surjective (tupleChartHom 7 planeConstants r m hm) := fun x =>
  ⟨planeToChartOf (k := k) m iu iv x,
    RingHom.congr_fun (tupleChartHom_comp_planeToChartOf r m hm iu iv hu hv) x⟩

end Generic

/-! ## The five charts -/

/-- The index of the entry `u` of each chart's tuple. -/
def uIndex : Fin 5 → Fin 8 := ![3, 5, 1, 6, 6]

/-- The index of the entry `v` of each chart's tuple. -/
def vIndex : Fin 5 → Fin 8 := ![0, 1, 4, 0, 4]

theorem stageOneData_tuple_u (c : Fin 5) :
    (stageOneData (k := k) c).tuple (uIndex c) = uCoord := by
  fin_cases c <;>
    simp [stageOneData, dataU, dataV, data10, data01, data11, uIndex, ChartTuple.tuple,
      ChartTuple.xF, ChartTuple.yF, monoX, monoY, monoT]

theorem stageOneData_tuple_v (c : Fin 5) :
    (stageOneData (k := k) c).tuple (vIndex c) = vCoord := by
  fin_cases c <;>
    simp [stageOneData, dataU, dataV, data10, data01, data11, vIndex, ChartTuple.tuple,
      ChartTuple.xF, ChartTuple.yF, monoX, monoY, monoT]

/-- The chart ring map of the `c`-th chart is surjective. -/
theorem chartTupleHom_surjective (c : Fin 5) :
    Function.Surjective (tupleChartHom 7 planeConstants (stageOneData (k := k) c).tuple
      (stageOneData c).ni (stageOneData c).tuple_ni) :=
  tupleChartHom_surjective_of _ _ _ (uIndex c) (vIndex c) (stageOneData_tuple_u c)
    (stageOneData_tuple_v c)

/-- The map of the `c`-th chart into the chart `D(z_{ni c})` of `P⁷`. -/
abbrev chartTupleSpec (c : Fin 5) :
    plane k ⟶ Spec (CommRingCat.of (coordinateChartRing k 7 (stageOneData (k := k) c).ni)) :=
  tupleSpec 7 planeConstants (stageOneData (k := k) c).tuple (stageOneData c).ni
    (stageOneData c).tuple_ni

/-- **Each chart map is a closed immersion into its `P⁷` chart.** -/
instance chartTupleSpec_isClosedImmersion (c : Fin 5) :
    IsClosedImmersion (chartTupleSpec (k := k) c) :=
  tupleSpec_isClosedImmersion _ _ _ _ _ (chartTupleHom_surjective c)

theorem chartTupleMorphism_eq (c : Fin 5) :
    chartTupleMorphism (k := k) c =
      chartTupleSpec c ≫ coordinateChartMorphism k 7 (stageOneData (k := k) c).ni := rfl

end KltDP.Examples.FrobeniusStageOneClosed
