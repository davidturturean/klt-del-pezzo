import KltDP.Examples.FrobeniusTowerChartCover
import KltDP.Examples.FrobeniusGraphPicardClassIntegral
import KltDP.Geometry.ProjectiveSegreRange

/-!
# The five affine charts of the first blowup stage

Stage `1` of the contact tower (`projectiveContactStage 1`, the point blowup of `P¹ ×_k P¹` at the
origin of the chart `(0,0)`) is covered by five open immersions of the polynomial plane
`Spec k[u][v]`:

* the two Rees charts of the affine blowup: the accepted selected chart `reesUChart = (stage 1).chart`
  (blowdown `chartSubstitution : u ↦ u, v ↦ u·v`) and the accepted second chart
  `reesVChart = secondChart projectiveProductInitial 0` (blowdown `secondSubstitution : u ↦ u·v, v ↦ u`);
* the three product charts `(1,0)`, `(0,1)`, `(1,1)` of `P¹ ×_k P¹`, which avoid the origin
  (`origin_not_mem_range`) and hence lift into the puncture and then into stage `1`
  (`punctureChart i j h`, projecting to `productChart i j`).

`stageOneChart : Fin 5 → (plane k ⟶ stageOne)` collects them, `stageOneChart_projection` gives the
uniform projection formula `chart ≫ π = Spec.map (blowdown) ≫ productChart (index)`, and
`stageOneCover : OpenCover.{u} stageOne` is the cover (accepted `stage_succ_cover` for the two Rees
charts and the puncture; a point of the puncture over the chart `(0,0)` lies in the chart `(1,0)` or
`(0,1)` because it differs from the origin, `planeChart_mem_range_of_ne`).

Nothing about morphisms out of stage `1` is constructed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStageOneCharts

open KltDP.Geometry KltDP.Geometry.ProjectiveChart KltDP.Geometry.ProjectiveSegreCover
open KltDP.Geometry.ProjectiveLineComparison
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
open FrobeniusProjectivePoints FrobeniusProductPlaneChart FrobeniusGraphPicardClassCharts
open FrobeniusGlobalBlowupStages FrobeniusStageComplement FrobeniusStageComplement.PlaneChartedScheme
open FrobeniusTowerSecondChart FrobeniusTowerSecondChart.PlaneChartedScheme
open FrobeniusTowerChartCover.PlaneChartedScheme

variable {k : Type u} [Field k]

/-- The selected origin has the accepted maximal centre ideal. -/
local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The initial product is integral (accepted), in the form seen by the accepted second chart. -/
local instance initial_isIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- Stage one of the contact tower. -/
abbrev stageOne : Scheme.{u} := projectiveContactStage (k := k) 1

/-- The step projection `stage 1 ⟶ P¹ ×_k P¹`. -/
abbrev stageOneProjection : stageOne (k := k) ⟶ projectiveProduct k :=
  (projectiveProductInitial (k := k)).stepProjection 0

/-! ## The two Rees charts -/

/-- The selected Rees chart `Spec k[u][w] ⟶ stage 1` (`v = u·w`). -/
abbrev reesUChart : plane k ⟶ stageOne (k := k) :=
  ((projectiveProductInitial (k := k)).stage 1).chart

theorem reesUChart_projection :
    reesUChart (k := k) ≫ stageOneProjection =
      Spec.map (CommRingCat.ofHom chartSubstitution) ≫ planeChart :=
  selectedChart_projection (projectiveProductInitial (k := k)) 0

/-- The second Rees chart `Spec k[v][w'] ⟶ stage 1` (`u = w'·v`, polynomial model). -/
abbrev reesVChart : plane k ⟶ stageOne (k := k) :=
  secondChart (projectiveProductInitial (k := k)) 0

instance reesVChart_isOpenImmersion : IsOpenImmersion (reesVChart (k := k)) := by
  unfold reesVChart secondChart
  infer_instance

theorem reesVChart_projection :
    reesVChart (k := k) ≫ stageOneProjection =
      Spec.map (CommRingCat.ofHom secondSubstitution) ≫ planeChart :=
  secondChart_projection (projectiveProductInitial (k := k)) 0

/-! ## The three punctured product charts -/

/-- The puncture `P¹ ×_k P¹ ∖ {origin}`. -/
abbrev puncture : (projectiveProduct k).Opens := initialPuncture (projectiveProductInitial (k := k))

theorem fin_two_zero_or_one : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide

/-- The first coordinate of a point of the chart `(0,0)`. -/
theorem planeChart_fst (q : plane k) :
    (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base (planeChart.base q) =
      (polynomialChartMap k 0).base
        ((Spec.map (CommRingCat.ofHom firstCoordinateMap)).base q) := by
  rw [← Scheme.comp_base_apply, ← productChart_zero_zero, productChart_fst, Scheme.comp_base_apply]

/-- The second coordinate of a point of the chart `(0,0)`. -/
theorem planeChart_snd (q : plane k) :
    (pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base (planeChart.base q) =
      (polynomialChartMap k 0).base
        ((Spec.map (CommRingCat.ofHom secondCoordinateMap)).base q) := by
  rw [← Scheme.comp_base_apply, ← productChart_zero_zero, productChart_snd, Scheme.comp_base_apply]

/-- The first coordinate of the origin is not in the second chart of `P¹`. -/
theorem origin_fst_not_mem :
    (Spec.map (CommRingCat.ofHom firstCoordinateMap)).base (originPoint (k := k)) ∉
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) := by
  rw [specMap_base_mem_basicOpen_iff, firstCoordinateMap_X, PrimeSpectrum.mem_basicOpen]
  exact fun hx => hx (centerU (k := k)).2

/-- The second coordinate of the origin is not in the second chart of `P¹`. -/
theorem origin_snd_not_mem :
    (Spec.map (CommRingCat.ofHom secondCoordinateMap)).base (originPoint (k := k)) ∉
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) := by
  rw [specMap_base_mem_basicOpen_iff, secondCoordinateMap_X, PrimeSpectrum.mem_basicOpen]
  exact fun hx => hx (centerV (k := k)).2

/-- The origin lies in no product chart other than `(0,0)`. -/
theorem origin_not_mem_range (i j : Fin 2) (h : (i, j) ≠ (0, 0)) :
    planeChart.base (originPoint (k := k)) ∉ Set.range (productChart (k := k) i j).base := by
  intro hmem
  rw [mem_range_productChart_iff, planeChart_fst, planeChart_snd] at hmem
  rcases fin_two_zero_or_one i with rfl | rfl <;> rcases fin_two_zero_or_one j with rfl | rfl
  · exact h rfl
  · exact origin_snd_not_mem
      ((polynomialChartMap_mem_range_iff k 0 1 (by decide) _).mp hmem.2)
  · exact origin_fst_not_mem
      ((polynomialChartMap_mem_range_iff k 0 1 (by decide) _).mp hmem.1)
  · exact origin_fst_not_mem
      ((polynomialChartMap_mem_range_iff k 0 1 (by decide) _).mp hmem.1)

theorem range_productChart_subset_puncture (i j : Fin 2) (h : (i, j) ≠ (0, 0)) :
    Set.range (productChart (k := k) i j).base ⊆ Set.range (puncture (k := k)).ι.base := by
  rintro x ⟨y, rfl⟩
  refine ⟨⟨(productChart i j).base y, ?_⟩, rfl⟩
  change (productChart (k := k) i j).base y ∉
    ({planeChart.base (originPoint (k := k))} : Set (projectiveProduct k))
  intro heq
  exact origin_not_mem_range i j h ⟨y, Set.mem_singleton_iff.mp heq⟩

/-- The product chart `(i, j) ≠ (0, 0)`, lifted into the puncture. -/
def puncturedChart (i j : Fin 2) (h : (i, j) ≠ (0, 0)) : plane k ⟶ (puncture (k := k)).toScheme :=
  IsOpenImmersion.lift (puncture (k := k)).ι (productChart i j)
    (range_productChart_subset_puncture i j h)

@[simp] theorem puncturedChart_ι (i j : Fin 2) (h : (i, j) ≠ (0, 0)) :
    puncturedChart i j h ≫ (puncture (k := k)).ι = productChart i j :=
  IsOpenImmersion.lift_fac _ _ _

instance puncturedChart_isOpenImmersion (i j : Fin 2) (h : (i, j) ≠ (0, 0)) :
    IsOpenImmersion (puncturedChart (k := k) i j h) := by
  haveI : IsOpenImmersion (puncturedChart (k := k) i j h ≫ (puncture (k := k)).ι) := by
    rw [puncturedChart_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (puncture (k := k)).ι

/-- The inclusion of the (unchanged) puncture into stage `1`. -/
abbrev punctureInclusion : (puncture (k := k)).toScheme ⟶ stageOne (k := k) :=
  PointBlowupGluing.complementι planeChart originPoint
    (projectiveProductInitial (k := k)).center_closed

theorem punctureInclusion_projection :
    punctureInclusion (k := k) ≫ stageOneProjection = (puncture (k := k)).ι :=
  PointBlowupGluing.complementι_projection _ _ _

/-- The product chart `(i, j) ≠ (0, 0)` as a chart of stage `1`. -/
def punctureChart (i j : Fin 2) (h : (i, j) ≠ (0, 0)) : plane k ⟶ stageOne (k := k) :=
  puncturedChart i j h ≫ punctureInclusion

instance punctureChart_isOpenImmersion (i j : Fin 2) (h : (i, j) ≠ (0, 0)) :
    IsOpenImmersion (punctureChart (k := k) i j h) := by
  unfold punctureChart
  infer_instance

theorem punctureChart_projection (i j : Fin 2) (h : (i, j) ≠ (0, 0)) :
    punctureChart i j h ≫ stageOneProjection = productChart (k := k) i j := by
  rw [punctureChart, Category.assoc, punctureInclusion_projection, puncturedChart_ι]

/-- A point of stage `1` over the puncture and over the product chart `(i, j) ≠ (0,0)` lies in the
corresponding chart of stage `1`. -/
theorem mem_range_punctureChart_of (i j : Fin 2) (h : (i, j) ≠ (0, 0)) (x : stageOne (k := k))
    (hx : stageOneProjection.base x ∈ puncture (k := k))
    (hmem : stageOneProjection.base x ∈ Set.range (productChart (k := k) i j).base) :
    x ∈ Set.range (punctureChart i j h).base := by
  have hx' : x ∈ Set.range (punctureInclusion (k := k)).base := by
    show x ∈ Set.range (PointBlowupGluing.complementι planeChart originPoint
      (projectiveProductInitial (k := k)).center_closed).base
    rw [PointBlowupGluing.range_complementι planeChart originPoint
      (projectiveProductInitial (k := k)).center_closed]
    exact hx
  obtain ⟨b, rfl⟩ := hx'
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_⟩
  rw [punctureChart, Scheme.comp_base_apply]
  congr 1
  apply (puncture (k := k)).ι.isOpenEmbedding.injective
  change (puncturedChart i j h ≫ (puncture (k := k)).ι).base y = _
  rw [puncturedChart_ι, hy]
  change (punctureInclusion ≫ stageOneProjection).base b = _
  rw [punctureInclusion_projection]

/-! ## Points of the chart `(0,0)` away from the origin -/

/-- A point of the plane containing both coordinates in its ideal is the origin. -/
theorem eq_origin_of_mem (q : plane k) (hu : uCoord (k := k) ∈ q.asIdeal)
    (hv : vCoord (k := k) ∈ q.asIdeal) : q = originPoint := by
  apply PrimeSpectrum.ext
  symm
  apply Ideal.IsMaximal.eq_of_le centerIdeal_isMaximal q.isPrime.ne_top
  show centerIdeal ≤ q.asIdeal
  rw [centerIdeal, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hu, hv⟩

/-- A point of the chart `(0,0)` other than the origin lies in the chart `(1,0)` or `(0,1)`. -/
theorem planeChart_mem_range_of_ne (q : plane k) (hq : q ≠ originPoint) :
    planeChart.base q ∈ Set.range (productChart (k := k) 1 0).base ∨
      planeChart.base q ∈ Set.range (productChart (k := k) 0 1).base := by
  have hfst0 : (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base
      (planeChart.base q) ∈ Set.range (polynomialChartMap k 0).base :=
    ⟨_, (planeChart_fst q).symm⟩
  have hsnd0 : (pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base
      (planeChart.base q) ∈ Set.range (polynomialChartMap k 0).base :=
    ⟨_, (planeChart_snd q).symm⟩
  by_cases hu : uCoord (k := k) ∈ q.asIdeal
  · have hv : vCoord (k := k) ∉ q.asIdeal := fun hv => hq (eq_origin_of_mem q hu hv)
    right
    rw [mem_range_productChart_iff]
    refine ⟨hfst0, ?_⟩
    rw [planeChart_snd, polynomialChartMap_mem_range_iff k 0 1 (by decide),
      specMap_base_mem_basicOpen_iff, secondCoordinateMap_X, PrimeSpectrum.mem_basicOpen]
    exact hv
  · left
    rw [mem_range_productChart_iff]
    refine ⟨?_, hsnd0⟩
    rw [planeChart_fst, polynomialChartMap_mem_range_iff k 0 1 (by decide),
      specMap_base_mem_basicOpen_iff, firstCoordinateMap_X, PrimeSpectrum.mem_basicOpen]
    exact hu

/-! ## The five charts and the cover -/

theorem ne_zero_zero_10 : ((1 : Fin 2), (0 : Fin 2)) ≠ (0, 0) := by decide
theorem ne_zero_zero_01 : ((0 : Fin 2), (1 : Fin 2)) ≠ (0, 0) := by decide
theorem ne_zero_zero_11 : ((1 : Fin 2), (1 : Fin 2)) ≠ (0, 0) := by decide

/-- The five affine charts of stage `1`: the two Rees charts and the product charts `(1,0)`,
`(0,1)`, `(1,1)`. -/
def stageOneChart : Fin 5 → (plane k ⟶ stageOne (k := k)) :=
  ![reesUChart, reesVChart, punctureChart 1 0 ne_zero_zero_10, punctureChart 0 1 ne_zero_zero_01,
    punctureChart 1 1 ne_zero_zero_11]

@[simp] theorem stageOneChart_zero : stageOneChart (k := k) 0 = reesUChart := rfl
@[simp] theorem stageOneChart_one : stageOneChart (k := k) 1 = reesVChart := rfl
@[simp] theorem stageOneChart_two :
    stageOneChart (k := k) 2 = punctureChart 1 0 ne_zero_zero_10 := rfl
@[simp] theorem stageOneChart_three :
    stageOneChart (k := k) 3 = punctureChart 0 1 ne_zero_zero_01 := rfl
@[simp] theorem stageOneChart_four :
    stageOneChart (k := k) 4 = punctureChart 1 1 ne_zero_zero_11 := rfl

instance stageOneChart_isOpenImmersion (i : Fin 5) : IsOpenImmersion (stageOneChart (k := k) i) := by
  fin_cases i
  · exact (inferInstance : IsOpenImmersion (reesUChart (k := k)))
  · exact (inferInstance : IsOpenImmersion (reesVChart (k := k)))
  · exact (inferInstance : IsOpenImmersion (punctureChart (k := k) 1 0 ne_zero_zero_10))
  · exact (inferInstance : IsOpenImmersion (punctureChart (k := k) 0 1 ne_zero_zero_01))
  · exact (inferInstance : IsOpenImmersion (punctureChart (k := k) 1 1 ne_zero_zero_11))

/-- The blowdown ring map of each chart to the product chart it lies over. -/
def chartBlowdown : Fin 5 → (planeRing k →+* planeRing k) :=
  ![chartSubstitution, secondSubstitution, RingHom.id _, RingHom.id _, RingHom.id _]

/-- The product chart over which each chart of stage `1` lies. -/
def chartIndex : Fin 5 → Fin 2 × Fin 2 := ![(0, 0), (0, 0), (1, 0), (0, 1), (1, 1)]

/-- The uniform projection formula for the five charts. -/
theorem stageOneChart_projection (i : Fin 5) :
    stageOneChart (k := k) i ≫ stageOneProjection =
      Spec.map (CommRingCat.ofHom (chartBlowdown (k := k) i)) ≫
        productChart (chartIndex i).1 (chartIndex i).2 := by
  fin_cases i
  · show reesUChart (k := k) ≫ stageOneProjection =
      Spec.map (CommRingCat.ofHom chartSubstitution) ≫ productChart 0 0
    rw [productChart_zero_zero]
    exact reesUChart_projection
  · show reesVChart (k := k) ≫ stageOneProjection =
      Spec.map (CommRingCat.ofHom secondSubstitution) ≫ productChart 0 0
    rw [productChart_zero_zero]
    exact reesVChart_projection
  · show punctureChart (k := k) 1 0 ne_zero_zero_10 ≫ stageOneProjection =
      Spec.map (CommRingCat.ofHom (RingHom.id (planeRing k))) ≫ productChart 1 0
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    exact punctureChart_projection 1 0 ne_zero_zero_10
  · show punctureChart (k := k) 0 1 ne_zero_zero_01 ≫ stageOneProjection =
      Spec.map (CommRingCat.ofHom (RingHom.id (planeRing k))) ≫ productChart 0 1
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    exact punctureChart_projection 0 1 ne_zero_zero_01
  · show punctureChart (k := k) 1 1 ne_zero_zero_11 ≫ stageOneProjection =
      Spec.map (CommRingCat.ofHom (RingHom.id (planeRing k))) ≫ productChart 1 1
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    exact punctureChart_projection 1 1 ne_zero_zero_11

/-- Every point of stage `1` lies in one of the five charts. -/
theorem exists_chart (x : stageOne (k := k)) :
    ∃ i : Fin 5, x ∈ Set.range (stageOneChart (k := k) i).base := by
  rcases stage_succ_cover (projectiveProductInitial (k := k)) 0 x with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · have hx : stageOneProjection.base x ∈ puncture (k := k) := h
    have hx' : stageOneProjection.base x ∉
        ({planeChart.base (originPoint (k := k))} : Set (projectiveProduct k)) := hx
    obtain ⟨i, j, hmem⟩ := productCharts_cover ((stageOneProjection (k := k)).base x)
    by_cases h00 : (i, j) = (0, 0)
    · obtain ⟨y, hy⟩ := hmem
      rw [Prod.mk.injEq] at h00
      obtain ⟨rfl, rfl⟩ := h00
      rw [productChart_zero_zero] at hy
      have hq : y ≠ originPoint := by
        rintro rfl
        exact hx' (Set.mem_singleton_iff.mpr hy.symm)
      rcases planeChart_mem_range_of_ne y hq with h10 | h01
      · rw [hy] at h10
        exact ⟨2, mem_range_punctureChart_of 1 0 ne_zero_zero_10 x hx h10⟩
      · rw [hy] at h01
        exact ⟨3, mem_range_punctureChart_of 0 1 ne_zero_zero_01 x hx h01⟩
    · rcases fin_two_zero_or_one i with rfl | rfl <;> rcases fin_two_zero_or_one j with rfl | rfl
      · exact absurd rfl h00
      · exact ⟨3, mem_range_punctureChart_of 0 1 ne_zero_zero_01 x hx hmem⟩
      · exact ⟨2, mem_range_punctureChart_of 1 0 ne_zero_zero_10 x hx hmem⟩
      · exact ⟨4, mem_range_punctureChart_of 1 1 ne_zero_zero_11 x hx hmem⟩

/-- The five-chart open cover of stage `1` (universe-lifted index, as the pinned gluing API
requires). -/
def stageOneCover : Scheme.OpenCover.{u} (stageOne (k := k)) where
  J := ULift.{u} (Fin 5)
  obj _ := plane k
  map i := stageOneChart i.down
  f x := ⟨(exists_chart x).choose⟩
  covers x := (exists_chart x).choose_spec

@[simp] theorem stageOneCover_map (i : ULift.{u} (Fin 5)) :
    (stageOneCover (k := k)).map i = stageOneChart i.down := rfl

end KltDP.Examples.FrobeniusStageOneCharts
