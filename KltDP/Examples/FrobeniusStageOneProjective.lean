import KltDP.Examples.FrobeniusStageOneLocalCharts
import KltDP.Examples.FrobeniusStageExceptionalSelfIntersectionValue

/-!
# Stage `1` of the contact tower is projective over `k`

The morphism `stageOneEmbedding : projectiveContactStage 1 ⟶ P⁷` of the eight `(2,2)`-monomials
vanishing at the origin is a closed immersion (`stageOneEmbedding_isClosedImmersion`), by the
chart-squares criterion over the eight coordinate charts `D(z_m)` of `P⁷`: over `D(z_m)` the piece of
stage `1` is the localised chart `localChart (hostChart m) m` (the chart itself for the five
monomials `m = ni c`; the basic opens `D(u'v') ⊂ (1,1)`, `D(v) ⊂ (1,0)`, `D(u) ⊂ (0,1)` for
`m = 2, 4, 6`), a closed immersion into `D(z_m)` (`localTupleSpec_isClosedImmersion'`: `u`, `v` and
`1/f` are localised entries) with range exactly `Φ⁻¹(D(z_m))` (`range_localChart`, from the five
chart range identities and the divisibility `tuple_{c'}(ni (host m)) ∣ tuple_{c'}(m)^N`,
`hdiv`).

Consequences, all **without the hypothesis `hproj`**:

* `stage_one_projective : IsProjectiveOverField ((projectiveProductInitial).stage 1).structureMap`;
* `stageOneSurface : NormalProjectiveSurface k` (= `stageSurface 1 _`), `stageOneExceptionalCurve`
  (= `exceptionalPrimeCurve 0 _`), and the F09 exports at stage `1`:
  `f09_exceptional_self_intersection_stage_one : E·E = −1` and
  `f09_exceptional_pullback_degree_zero_stage_one : E·π^*L = 0`.

Route for the iterated stages (not formalised): with stage `n ⊂ P^N` and centre `p` a `k`-point, the
`N` linear forms vanishing at `p` generate the ideal sheaf of `p` twisted by `O(1)`, so
`Bl_p (stage n) ⊂ stage n × P^{N-1} ⊂ P^N × P^{N-1} ⊂ P^{N(N+1)-1}` (Segre); equivalently the
`(2,2)`-construction here is the case `N = 3` with `stage 0 ⊂ P³` by the Segre embedding of BRIEF10.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStageOneProjective

open KltDP.Geometry KltDP.Geometry.ProjectiveChart
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
open FrobeniusGlobalBlowupStages FrobeniusStageSurface
open FrobeniusStageOneCharts FrobeniusStageOneTuples FrobeniusStageOneTuples.ChartTuple
open FrobeniusStageOneEmbedding FrobeniusStageOneClosed FrobeniusStageOneRanges
open FrobeniusStageOneReesRanges FrobeniusStageOneLocal

variable {k : Type u} [Field k]

/-- The chart of stage `1` hosting the piece over the coordinate chart `D(z_m)` of `P⁷`. -/
def hostChart : Fin 8 → Fin 5 := ![1, 0, 4, 2, 2, 3, 3, 4]

/-! ## The five chart range identities -/

theorem range_stageOneChart (c : Fin 5) :
    Set.range (stageOneChart (k := k) c).base =
      (stageOneEmbedding (k := k)).base ⁻¹'
        Set.range (coordinateChartMorphism k 7 (stageOneData (k := k) c).ni).base := by
  fin_cases c
  · exact range_stageOneChart_zero
  · exact range_stageOneChart_one
  · exact range_stageOneChart_two
  · exact range_stageOneChart_three
  · exact range_stageOneChart_four

/-! ## Divisibility of the transition entries -/

theorem hdiv_self (c' : Fin 5) (m : Fin 8) (h : (stageOneData (k := k) (hostChart m)).ni = m) :
    ∃ N : ℕ, 0 < N ∧
      (stageOneData (k := k) c').tuple (stageOneData (k := k) (hostChart m)).ni ∣
        (stageOneData (k := k) c').tuple m ^ N :=
  ⟨1, one_pos, Dvd.intro 1 (by rw [h, pow_one, mul_one])⟩

theorem hdiv (m : Fin 8) (c' : Fin 5) :
    ∃ N : ℕ, 0 < N ∧
      (stageOneData (k := k) c').tuple (stageOneData (k := k) (hostChart m)).ni ∣
        (stageOneData (k := k) c').tuple m ^ N := by
  fin_cases m <;> fin_cases c'
  -- m = 0
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  -- m = 1
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  -- m = 2 (torus), host `(1,1)`, `ni = 7`
  · exact ⟨3, by norm_num, Dvd.intro vCoord (by
      show uCoord * (uCoord * vCoord) * (uCoord * vCoord) * vCoord = (1 * 1 * (uCoord * vCoord)) ^ 3
      ring)⟩
  · exact ⟨3, by norm_num, Dvd.intro vCoord (by
      show uCoord * vCoord * uCoord * (uCoord * vCoord) * vCoord = (1 * 1 * (uCoord * vCoord)) ^ 3
      ring)⟩
  · exact ⟨2, by norm_num, Dvd.intro (uCoord * uCoord) (by
      show 1 * vCoord * vCoord * (uCoord * uCoord) = (uCoord * 1 * vCoord) ^ 2
      ring)⟩
  · exact ⟨2, by norm_num, Dvd.intro (vCoord * vCoord) (by
      show uCoord * 1 * uCoord * (vCoord * vCoord) = (1 * vCoord * uCoord) ^ 2
      ring)⟩
  · exact ⟨1, by norm_num, Dvd.intro (uCoord * vCoord * 1) (by
      show 1 * 1 * 1 * (uCoord * vCoord * 1) = (uCoord * vCoord * 1) ^ 1
      ring)⟩
  -- m = 3
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  -- m = 4, host `(1,0)`, `ni = 3`
  · exact ⟨1, by norm_num, Dvd.intro (uCoord * vCoord) (by
      show uCoord * 1 * 1 * (uCoord * vCoord) = (uCoord * 1 * (uCoord * vCoord)) ^ 1
      ring)⟩
  · exact ⟨1, by norm_num, Dvd.intro uCoord (by
      show uCoord * vCoord * 1 * vCoord * uCoord = (uCoord * vCoord * 1 * (uCoord * vCoord)) ^ 1
      ring)⟩
  · exact ⟨1, by norm_num, Dvd.intro (1 * 1 * vCoord) (by
      show 1 * 1 * 1 * (1 * 1 * vCoord) = (1 * 1 * vCoord) ^ 1
      ring)⟩
  · exact ⟨2, by norm_num, Dvd.intro (uCoord * uCoord) (by
      show uCoord * vCoord * (uCoord * vCoord) * (uCoord * uCoord) = (uCoord * vCoord * uCoord) ^ 2
      ring)⟩
  · exact ⟨2, by norm_num, Dvd.intro 1 (by
      show 1 * vCoord * vCoord * 1 = (1 * vCoord * 1) ^ 2
      ring)⟩
  -- m = 5
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  -- m = 6, host `(0,1)`, `ni = 5`
  · exact ⟨1, by norm_num, Dvd.intro uCoord (by
      show 1 * (uCoord * vCoord) * vCoord * uCoord = (1 * (uCoord * vCoord) * (uCoord * vCoord)) ^ 1
      ring)⟩
  · exact ⟨1, by norm_num, Dvd.intro (uCoord * vCoord) (by
      show 1 * uCoord * 1 * (uCoord * vCoord) = (1 * uCoord * (uCoord * vCoord)) ^ 1
      ring)⟩
  · exact ⟨2, by norm_num, Dvd.intro (vCoord * vCoord) (by
      show uCoord * vCoord * (uCoord * vCoord) * (vCoord * vCoord) = (uCoord * vCoord * vCoord) ^ 2
      ring)⟩
  · exact ⟨1, by norm_num, Dvd.intro (1 * 1 * uCoord) (by
      show 1 * 1 * 1 * (1 * 1 * uCoord) = (1 * 1 * uCoord) ^ 1
      ring)⟩
  · exact ⟨2, by norm_num, Dvd.intro 1 (by
      show uCoord * 1 * uCoord * 1 = (uCoord * 1 * 1) ^ 2
      ring)⟩
  -- m = 7
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl
  · exact hdiv_self _ _ rfl

/-! ## The closed immersions into the eight charts -/

theorem hu_main (c : Fin 5) :
    (stageOneData (k := k) c).tuple (uIndex c) =
      uCoord * (stageOneData (k := k) c).tuple (stageOneData (k := k) c).ni := by
  rw [stageOneData_tuple_u, tuple_ni, mul_one]

theorem hv_main (c : Fin 5) :
    (stageOneData (k := k) c).tuple (vIndex c) =
      vCoord * (stageOneData (k := k) c).tuple (stageOneData (k := k) c).ni := by
  rw [stageOneData_tuple_v, tuple_ni, mul_one]

/-- **Each piece is a closed immersion into its coordinate chart of `P⁷`.** -/
theorem localTupleSpec_isClosedImmersion' (m : Fin 8) :
    IsClosedImmersion (localTupleSpec (k := k) (hostChart m) m) := by
  fin_cases m
  · exact localTupleSpec_isClosedImmersion _ _ _ _
      (localTuple_eq_of _ _ _ _ (hu_main 1)) (localTuple_eq_of _ _ _ _ (hv_main 1))
  · exact localTupleSpec_isClosedImmersion _ _ _ _
      (localTuple_eq_of _ _ _ _ (hu_main 0)) (localTuple_eq_of _ _ _ _ (hv_main 0))
  · exact localTupleSpec_isClosedImmersion _ _ 0 1
      (localTuple_eq_of _ _ 0 uCoord (by
        show uCoord * vCoord * uCoord = uCoord * (uCoord * vCoord * 1)
        ring))
      (localTuple_eq_of _ _ 1 vCoord (by
        show uCoord * vCoord * vCoord = vCoord * (uCoord * vCoord * 1)
        ring))
  · exact localTupleSpec_isClosedImmersion _ _ _ _
      (localTuple_eq_of _ _ _ _ (hu_main 2)) (localTuple_eq_of _ _ _ _ (hv_main 2))
  · exact localTupleSpec_isClosedImmersion _ _ 2 7
      (localTuple_eq_of _ _ 2 uCoord (by
        show uCoord * 1 * vCoord = uCoord * (1 * 1 * vCoord)
        ring))
      (localTuple_eq_of _ _ 7 vCoord (by
        show 1 * vCoord * vCoord = vCoord * (1 * 1 * vCoord)
        ring))
  · exact localTupleSpec_isClosedImmersion _ _ _ _
      (localTuple_eq_of _ _ _ _ (hu_main 3)) (localTuple_eq_of _ _ _ _ (hv_main 3))
  · exact localTupleSpec_isClosedImmersion _ _ 7 2
      (localTuple_eq_of _ _ 7 uCoord (by
        show uCoord * 1 * uCoord = uCoord * (1 * 1 * uCoord)
        ring))
      (localTuple_eq_of _ _ 2 vCoord (by
        show 1 * vCoord * uCoord = vCoord * (1 * 1 * uCoord)
        ring))
  · exact localTupleSpec_isClosedImmersion _ _ _ _
      (localTuple_eq_of _ _ _ _ (hu_main 4)) (localTuple_eq_of _ _ _ _ (hv_main 4))

/-! ## The closed immersion and projectivity -/

/-- **`stageOneEmbedding : stage 1 ⟶ P⁷` is a closed immersion.** -/
theorem stageOneEmbedding_isClosedImmersion : IsClosedImmersion (stageOneEmbedding (k := k)) := by
  haveI : ∀ i : ULift.{u} (Fin 8),
      IsClosedImmersion (localTupleSpec (k := k) (hostChart i.down) i.down) :=
    fun i => localTupleSpec_isClosedImmersion' i.down
  exact isClosedImmersion_of_chartSquares (stageOneEmbedding (k := k)) (coordinateChartCover k 7)
    (fun i => Spec (CommRingCat.of (LocRing (k := k) (hostChart i.down) i.down)))
    (fun i => localChart (hostChart i.down) i.down)
    (fun i => localTupleSpec (hostChart i.down) i.down)
    (fun i => localChart_embedding (hostChart i.down) i.down)
    (fun i => range_localChart (hostChart i.down) i.down (range_stageOneChart _) (hdiv i.down))

/-- **Stage `1` of the contact tower is projective over `k`.** -/
theorem stage_one_projective :
    IsProjectiveOverField ((projectiveProductInitial (k := k)).stage 1).structureMap :=
  ⟨7, stageOneEmbedding, stageOneEmbedding_isClosedImmersion, stageOneEmbedding_structure⟩

/-- **Stage `1` as a normal projective surface**, with no projectivity hypothesis. -/
def stageOneSurface [IsAlgClosed k] : NormalProjectiveSurface k :=
  stageSurface 1 (stage_one_projective (k := k))

@[simp] theorem stageOneSurface_toScheme [IsAlgClosed k] :
    (stageOneSurface (k := k)).toScheme = projectiveContactStage (k := k) 1 := rfl

/-- **The exceptional curve of the first blowup as a prime curve**, with no projectivity
hypothesis. -/
def stageOneExceptionalCurve [IsAlgClosed k] : (stageOneSurface (k := k)).PrimeCurve :=
  exceptionalPrimeCurve 0 (stage_one_projective (k := k))

end KltDP.Examples.FrobeniusStageOneProjective

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusStageOneProjective
open FrobeniusStageExceptionalPullback FrobeniusStageExceptionalSelfIntersection

/-- **F09 at stage `1` without `hproj`: `E·E = −1`.** -/
theorem f09_exceptional_self_intersection_stage_one (k : Type u) [Field k] [IsAlgClosed k] :
    (exceptionalPrimeCurve 0 (stage_one_projective (k := k))).selfIntersectionNumber
      (stageRegular 0 (stage_one_projective (k := k))) = -1 :=
  f09_exceptional_self_intersection k 0 (stage_one_projective (k := k))

/-- **F09 at stage `1` without `hproj`: `E·π^*L = 0` and `E·E = −deg_E(conormal)`.** -/
theorem f09_exceptional_pullback_degree_zero_stage_one (k : Type u) [Field k] [IsAlgClosed k] :
    (∀ L : InvertibleSheaf (projectiveContactStage (k := k) 0),
      (exceptionalPrimeCurve 0 (stage_one_projective (k := k))).restrictionDegree
        (pullbackInvertibleSheaf ((projectiveProductInitial (k := k)).stepProjection 0) L) = 0) ∧
    (exceptionalPrimeCurve 0 (stage_one_projective (k := k))).selfIntersectionNumber
        (stageRegular 0 (stage_one_projective (k := k))) =
      -(exceptionalPrimeCurve 0 (stage_one_projective (k := k))).lineDegree
        (exceptionalConormalLine 0 (stage_one_projective (k := k))) :=
  f09_exceptional_pullback_degree_zero k 0 (stage_one_projective (k := k))

/-- The statements have exactly one universe parameter. -/
theorem f09_stage_one_universe_check (k : Type u) [Field k] [IsAlgClosed k] : True := by
  have _ := f09_exceptional_self_intersection_stage_one.{u} k
  have _ := f09_exceptional_pullback_degree_zero_stage_one.{u} k
  trivial

end KltDP.Examples
