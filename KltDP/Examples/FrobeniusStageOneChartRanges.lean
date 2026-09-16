import KltDP.Examples.FrobeniusStageOneChartClosed

/-!
# Range identities for the chart squares of `stage 1 ⟶ P⁷`: the three product charts

For the chart-squares criterion (`isClosedImmersion_of_chartSquares`) each coordinate chart `D(z_m)` of
`P⁷` needs an open piece of stage `1` whose range is exactly `Φ⁻¹(D(z_m))`. This module proves the
identity for the three product charts `(1,0)`, `(0,1)`, `(1,1)` of stage `1` (`m = 3, 5, 7`):

* `embedding_mem_range_iff`: `Φ (chart c q) ∈ D(z_m) ↔ tuple_c(m) ∉ q` (generic tuple-morphism range lemma);
* `productChart_mem_range_iff`: a point `productChart i j p` lies in `productChart i' j'` iff the
  coordinates that change are invertible at `p` (accepted `P¹` chart transition);
* `mem_range_punctureChart_iff`: `x` lies in the chart `(i,j) ≠ (0,0)` of stage `1` iff `π x` lies in
  `productChart i j`;
* `origU_dvd_tuple`, `origV_dvd_tuple`: on a chart `D`, the entry `tuple_D (ni D')` is divisible by the
  pulled-back product coordinate that changes between `D` and `D'`;
* `range_stageOneChart_eq_preimage_of_puncture`: **`range (stageOneChart c) = Φ⁻¹(D(z_{ni c}))`** for the
  three product charts `c = 2, 3, 4`.

The identities for the two Rees charts (`m = 1, 0`) need the description of the affine blowup over
`D(u)`, `D(v)` (points over `D(u)` lie in the `u`-Rees chart) and are not proved here; neither are the
three charts `m = 2, 4, 6` of `P⁷` whose preimages are localisations of the charts.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStageOneRanges

open KltDP.Geometry KltDP.Geometry.ProjectiveChart KltDP.Geometry.ProjectiveLineComparison
open KltDP.Geometry.ProjectiveSegreCover
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
open FrobeniusProjectivePoints FrobeniusProductPlaneChart FrobeniusGraphPicardClassCharts
open FrobeniusGlobalBlowupStages
open FrobeniusStageOneCharts FrobeniusStageOneTuples FrobeniusStageOneTuples.ChartTuple
open FrobeniusStageOneEmbedding FrobeniusStageOneClosed

variable {k : Type u} [Field k]

/-! ## Points of `P¹ ×_k P¹` and the product charts -/

theorem productChart_fst_apply (i j : Fin 2) (p : plane k) :
    (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base
        ((productChart (k := k) i j).base p) =
      (polynomialChartMap k i).base ((Spec.map (CommRingCat.ofHom firstCoordinateMap)).base p) := by
  rw [← Scheme.comp_base_apply, productChart_fst, Scheme.comp_base_apply]

theorem productChart_snd_apply (i j : Fin 2) (p : plane k) :
    (pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base
        ((productChart (k := k) i j).base p) =
      (polynomialChartMap k j).base ((Spec.map (CommRingCat.ofHom secondCoordinateMap)).base p) := by
  rw [← Scheme.comp_base_apply, productChart_snd, Scheme.comp_base_apply]

/-- A point of the chart `i` of `P¹` lies in the chart `i'` iff, when `i ≠ i'`, its coordinate is
invertible. -/
theorem polynomialChartMap_mem_range_iff' (i i' : Fin 2) (y : Spec (CommRingCat.of (Polynomial k))) :
    (polynomialChartMap k i).base y ∈ Set.range (polynomialChartMap k i').base ↔
      (i ≠ i' → y ∈ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k)) := by
  by_cases h : i = i'
  · subst h
    exact ⟨fun _ h' => absurd rfl h', fun _ => ⟨y, rfl⟩⟩
  · rw [polynomialChartMap_mem_range_iff k i i' h]
    exact ⟨fun h' _ => h', fun h' => h' h⟩

/-- **Chart transition on `P¹ ×_k P¹`**: `productChart i j p` lies in `productChart i' j'` iff the
coordinates that change are invertible at `p`. -/
theorem productChart_mem_range_iff (i j i' j' : Fin 2) (p : plane k) :
    (productChart (k := k) i j).base p ∈ Set.range (productChart (k := k) i' j').base ↔
      (i ≠ i' → p ∈ PrimeSpectrum.basicOpen (uCoord (k := k))) ∧
        (j ≠ j' → p ∈ PrimeSpectrum.basicOpen (vCoord (k := k))) := by
  rw [mem_range_productChart_iff, productChart_fst_apply, productChart_snd_apply,
    polynomialChartMap_mem_range_iff', polynomialChartMap_mem_range_iff',
    specMap_base_mem_basicOpen_iff, specMap_base_mem_basicOpen_iff, firstCoordinateMap_X,
    secondCoordinateMap_X]

/-- A point of stage `1` lies in the chart `(i, j) ≠ (0,0)` iff its projection lies in the product
chart `(i, j)`. -/
theorem mem_range_punctureChart_iff (i j : Fin 2) (h : (i, j) ≠ (0, 0)) (x : stageOne (k := k)) :
    x ∈ Set.range (punctureChart i j h).base ↔
      stageOneProjection.base x ∈ Set.range (productChart (k := k) i j).base := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [← Scheme.comp_base_apply, punctureChart_projection]
  · intro hmem
    refine mem_range_punctureChart_of i j h x ?_ hmem
    obtain ⟨y, hy⟩ := hmem
    change stageOneProjection.base x ∉
      ({planeChart.base (originPoint (k := k))} : Set (projectiveProduct k))
    intro heq
    rw [Set.mem_singleton_iff] at heq
    exact origin_not_mem_range i j h ⟨y, hy.trans heq⟩

/-- The projection of a point of the `c`-th chart of stage `1`. -/
theorem stageOneProjection_chart_apply (c : Fin 5) (q : plane k) :
    stageOneProjection.base ((stageOneChart (k := k) c).base q) =
      (productChart (chartIndex c).1 (chartIndex c).2).base
        ((Spec.map (CommRingCat.ofHom (chartBlowdown (k := k) c))).base q) := by
  rw [← Scheme.comp_base_apply, stageOneChart_projection, Scheme.comp_base_apply]

/-! ## The embedding on a chart -/

/-- `Φ (chart c q) ∈ D(z_m) ↔ tuple_c(m) ∉ q`. -/
theorem embedding_mem_range_iff (c : Fin 5) (q : plane k) (m : Fin 8) :
    (stageOneEmbedding (k := k)).base ((stageOneChart c).base q) ∈
        Set.range (coordinateChartMorphism k 7 m).base ↔
      q ∈ PrimeSpectrum.basicOpen ((stageOneData (k := k) c).tuple m) := by
  rw [← Scheme.comp_base_apply, stageOneChart_embedding]
  exact tupleMorphism_base_mem_range_iff 7 planeConstants _ _ _ q m

/-- Every chart lands in its own `P⁷` chart. -/
theorem range_stageOneChart_subset (c : Fin 5) :
    Set.range (stageOneChart (k := k) c).base ⊆
      (stageOneEmbedding (k := k)).base ⁻¹'
        Set.range (coordinateChartMorphism k 7 (stageOneData (k := k) c).ni).base := by
  rintro x ⟨q, rfl⟩
  rw [Set.mem_preimage, embedding_mem_range_iff, tuple_ni, PrimeSpectrum.mem_basicOpen]
  exact fun h => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

/-! ## Divisibility of the transition entries -/

theorem origU_dvd_tuple (D D' : ChartTuple k) (h : D.xi ≠ D'.xi) : D.origU ∣ D.tuple D'.ni := by
  rw [tuple, D'.monoX_ni, xF, if_neg (Ne.symm h)]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

theorem origV_dvd_tuple (D D' : ChartTuple k) (h : D.yi ≠ D'.yi) : D.origV ∣ D.tuple D'.ni := by
  rw [tuple, D'.monoY_ni, yF, if_neg (Ne.symm h)]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

theorem mem_basicOpen_of_dvd {R : Type u} [CommRing R] {a b : R} (h : a ∣ b) (q : PrimeSpectrum R)
    (hb : q ∈ PrimeSpectrum.basicOpen b) : q ∈ PrimeSpectrum.basicOpen a := by
  rw [PrimeSpectrum.mem_basicOpen] at hb ⊢
  obtain ⟨c, rfl⟩ := h
  exact fun ha => hb (Ideal.mul_mem_right c _ ha)

/-! ## The range identity for the product charts -/

/-- A point of stage `1` whose image lies in the `P⁷` chart of the chart `c` projects into the
product chart of `c`. -/
theorem projection_mem_range_of_embedding (c : Fin 5) (x : stageOne (k := k))
    (hx : (stageOneEmbedding (k := k)).base x ∈
      Set.range (coordinateChartMorphism k 7 (stageOneData (k := k) c).ni).base) :
    stageOneProjection.base x ∈
      Set.range (productChart (k := k) (chartIndex c).1 (chartIndex c).2).base := by
  obtain ⟨c', q, rfl⟩ : ∃ c' q, (stageOneChart (k := k) c').base q = x := by
    obtain ⟨c', q, hq⟩ := exists_chart x
    exact ⟨c', q, hq⟩
  rw [embedding_mem_range_iff] at hx
  rw [stageOneProjection_chart_apply, productChart_mem_range_iff, specMap_base_mem_basicOpen_iff,
    specMap_base_mem_basicOpen_iff]
  constructor
  · intro hne
    rw [← stageOneData_xi (k := k) c', ← stageOneData_xi (k := k) c] at hne
    rw [← stageOneData_origU]
    exact mem_basicOpen_of_dvd (origU_dvd_tuple _ _ hne) q hx
  · intro hne
    rw [← stageOneData_yi (k := k) c', ← stageOneData_yi (k := k) c] at hne
    rw [← stageOneData_origV]
    exact mem_basicOpen_of_dvd (origV_dvd_tuple _ _ hne) q hx

/-- **The range identity for a product chart of stage `1`**: for `c` a chart lying over a product
chart `(i, j) ≠ (0, 0)`. -/
theorem range_stageOneChart_eq_preimage_of_puncture (c : Fin 5) (i j : Fin 2) (h : (i, j) ≠ (0, 0))
    (hc : stageOneChart (k := k) c = punctureChart i j h) (hij : chartIndex c = (i, j)) :
    Set.range (stageOneChart (k := k) c).base =
      (stageOneEmbedding (k := k)).base ⁻¹'
        Set.range (coordinateChartMorphism k 7 (stageOneData (k := k) c).ni).base := by
  apply Set.Subset.antisymm (range_stageOneChart_subset c)
  intro x hx
  have hπ := projection_mem_range_of_embedding c x hx
  rw [hij] at hπ
  rw [hc, mem_range_punctureChart_iff]
  exact hπ

theorem range_stageOneChart_two :
    Set.range (stageOneChart (k := k) 2).base =
      (stageOneEmbedding (k := k)).base ⁻¹'
        Set.range (coordinateChartMorphism k 7 (stageOneData (k := k) 2).ni).base :=
  range_stageOneChart_eq_preimage_of_puncture 2 1 0 ne_zero_zero_10 rfl rfl

theorem range_stageOneChart_three :
    Set.range (stageOneChart (k := k) 3).base =
      (stageOneEmbedding (k := k)).base ⁻¹'
        Set.range (coordinateChartMorphism k 7 (stageOneData (k := k) 3).ni).base :=
  range_stageOneChart_eq_preimage_of_puncture 3 0 1 ne_zero_zero_01 rfl rfl

theorem range_stageOneChart_four :
    Set.range (stageOneChart (k := k) 4).base =
      (stageOneEmbedding (k := k)).base ⁻¹'
        Set.range (coordinateChartMorphism k 7 (stageOneData (k := k) 4).ni).base :=
  range_stageOneChart_eq_preimage_of_puncture 4 1 1 ne_zero_zero_11 rfl rfl

end KltDP.Examples.FrobeniusStageOneRanges
