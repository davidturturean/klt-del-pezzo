import KltDP.Examples.FrobeniusStageOneTuples
import KltDP.Geometry.AffineBlowupExceptionalOverlap
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The morphism `stage 1 ⟶ P⁷` of the `(2,2)`-monomials vanishing at the origin

The five chart maps `chartTupleMorphism c : Spec k[u][v] ⟶ P⁷` (`FrobeniusStageOneTuples`) are glued
over the five-chart cover `stageOneCover` of stage `1` (`FrobeniusStageOneCharts`) with the pinned
`Scheme.Cover.glueMorphisms`:

* on an overlap `W = pullback (stageOneChart a) (stageOneChart b)` the pulled-back product coordinates
  satisfy the accepted `P¹` chart relations (equal on a common product chart, mutually inverse
  otherwise: `overlap_u`, `overlap_v`, through the projection to `P¹ ×_k P¹` and the BRIEF10
  `chart_function_relation`), constants agree (`overlap_constants`), and on the overlap of the two Rees
  charts the two chart coordinates `w`, `w'` are mutually inverse (`rees_relation`, the accepted
  `conormalOverlap_chartFractions_mul` of the Rees `Proj` transported through the polynomial models);
* these relations feed the scaling algebra of `ChartTuple` (`tuple_scale_of_relations`, or
  `tuple_scale` with the explicit `T`-relation for the Rees pair), and `tupleMorphism_eq_of_scale`
  gives the compatibility of every pair of chart maps (`glue_compatible`);
* `stageOneEmbedding : projectiveContactStage 1 ⟶ projectiveSpace k 7`, with
  `stageOneChart c ≫ stageOneEmbedding = chartTupleMorphism c` and `stageOneEmbedding_structure`
  (the morphism is over `k`).

The closed-immersion property of `stageOneEmbedding` (chart squares over the eight coordinate charts of
`P⁷`, three of which pull back to localisations of the five charts) is **not** proved here; see the F09
record for the remaining route.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStageOneEmbedding

open KltDP.Geometry KltDP.Geometry.ProjectiveChart KltDP.Geometry.ProjectiveLineComparison
open KltDP.Geometry.ProjectiveSegreCover KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
open FrobeniusProjectivePoints FrobeniusProductPlaneChart FrobeniusGraphPicardClassCharts
open FrobeniusGlobalBlowupStages FrobeniusTowerSecondChart FrobeniusTowerSecondChart.PlaneChartedScheme
open FrobeniusStageOneCharts FrobeniusStageOneTuples FrobeniusStageOneTuples.ChartTuple
open FrobeniusExceptionalCharts

variable {k : Type u} [Field k]

/-! ## Relations between the pulled-back product coordinates -/

section ProductRelations

variable {W : Scheme.{u}} (g₀ g₁ : W ⟶ plane k) (i j i' j' : Fin 2)
  (h : g₀ ≫ productChart (k := k) i j = g₁ ≫ productChart (k := k) i' j')

include h in
/-- The first product coordinates of two maps into product charts: equal on a common chart,
mutually inverse otherwise. -/
theorem product_u_relation :
    (i = i' → (specHomRingHom g₀).hom uCoord = (specHomRingHom g₁).hom uCoord) ∧
      (i ≠ i' → (specHomRingHom g₀).hom uCoord * (specHomRingHom g₁).hom uCoord = 1) := by
  have h1 : (g₀ ≫ Spec.map (CommRingCat.ofHom firstCoordinateMap)) ≫ polynomialChartMap k i =
      (g₁ ≫ Spec.map (CommRingCat.ofHom firstCoordinateMap)) ≫ polynomialChartMap k i' := by
    rw [Category.assoc, Category.assoc, ← productChart_fst i j, ← productChart_fst i' j',
      ← Category.assoc, ← Category.assoc, h]
  have h2 := chart_function_relation k _ _ i i' h1
  rw [specHomRingHom_comp_specMap, specHomRingHom_comp_specMap] at h2
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    firstCoordinateMap_X] using h2

include h in
/-- The second product coordinates of two maps into product charts. -/
theorem product_v_relation :
    (j = j' → (specHomRingHom g₀).hom vCoord = (specHomRingHom g₁).hom vCoord) ∧
      (j ≠ j' → (specHomRingHom g₀).hom vCoord * (specHomRingHom g₁).hom vCoord = 1) := by
  have h1 : (g₀ ≫ Spec.map (CommRingCat.ofHom secondCoordinateMap)) ≫ polynomialChartMap k j =
      (g₁ ≫ Spec.map (CommRingCat.ofHom secondCoordinateMap)) ≫ polynomialChartMap k j' := by
    rw [Category.assoc, Category.assoc, ← productChart_snd i j, ← productChart_snd i' j',
      ← Category.assoc, ← Category.assoc, h]
  have h2 := chart_function_relation k _ _ j j' h1
  rw [specHomRingHom_comp_specMap, specHomRingHom_comp_specMap] at h2
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    secondCoordinateMap_X] using h2

include h in
/-- Constants agree for two maps into product charts. -/
theorem product_constants :
    (specHomRingHom g₀).hom.comp planeConstants = (specHomRingHom g₁).hom.comp planeConstants := by
  have hc : g₀ ≫ Spec.map (CommRingCat.ofHom planeConstants) =
      g₁ ≫ Spec.map (CommRingCat.ofHom planeConstants) := by
    calc g₀ ≫ Spec.map (CommRingCat.ofHom planeConstants)
        = g₀ ≫ (productChart (k := k) i j ≫ projectiveProductToSpec) := by
          rw [productChart_toSpec]
      _ = g₁ ≫ (productChart (k := k) i' j' ≫ projectiveProductToSpec) := by
          rw [← Category.assoc, ← Category.assoc, h]
      _ = _ := by rw [productChart_toSpec]
  have h2 := congrArg CommRingCat.Hom.hom (specHomRingHom_congr hc)
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using h2

end ProductRelations

/-! ## The blowdown ring maps fix constants -/

theorem secondSubstitution_constants (r : k) :
    secondSubstitution (planeConstants r) = planeConstants r := by
  change vChartPolynomialEquiv (chartBaseMap centerIdeal centerV (planeConstants r)) = planeConstants r
  exact vChartPolynomialEquiv_constants r

theorem chartBlowdown_constants (c : Fin 5) :
    (chartBlowdown (k := k) c).comp planeConstants = planeConstants := by
  fin_cases c
  · exact RingHom.ext fun r => chartSubstitution_C (Polynomial.C r)
  · exact RingHom.ext fun r => secondSubstitution_constants r
  · exact RingHom.id_comp _
  · exact RingHom.id_comp _
  · exact RingHom.id_comp _

/-! ## The overlaps of the five charts of stage `1` -/

section Overlap

variable (a b : Fin 5)

theorem overlap_projection :
    (pullback.fst (stageOneChart (k := k) a) (stageOneChart b) ≫
        Spec.map (CommRingCat.ofHom (chartBlowdown (k := k) a))) ≫
        productChart (chartIndex a).1 (chartIndex a).2 =
      (pullback.snd (stageOneChart (k := k) a) (stageOneChart b) ≫
        Spec.map (CommRingCat.ofHom (chartBlowdown (k := k) b))) ≫
        productChart (chartIndex b).1 (chartIndex b).2 := by
  rw [Category.assoc, Category.assoc, ← stageOneChart_projection a, ← stageOneChart_projection b,
    ← Category.assoc, ← Category.assoc, pullback.condition]

/-- The pulled-back first product coordinates on the overlap of two charts. -/
theorem overlap_u :
    ((chartIndex a).1 = (chartIndex b).1 →
        (specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom
            (chartBlowdown a uCoord) =
          (specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom
            (chartBlowdown b uCoord)) ∧
      ((chartIndex a).1 ≠ (chartIndex b).1 →
        (specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom
            (chartBlowdown a uCoord) *
          (specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom
            (chartBlowdown b uCoord) = 1) := by
  have h := product_u_relation _ _ _ _ _ _ (overlap_projection (k := k) a b)
  rw [specHomRingHom_comp_specMap, specHomRingHom_comp_specMap] at h
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using h

/-- The pulled-back second product coordinates on the overlap of two charts. -/
theorem overlap_v :
    ((chartIndex a).2 = (chartIndex b).2 →
        (specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom
            (chartBlowdown a vCoord) =
          (specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom
            (chartBlowdown b vCoord)) ∧
      ((chartIndex a).2 ≠ (chartIndex b).2 →
        (specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom
            (chartBlowdown a vCoord) *
          (specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom
            (chartBlowdown b vCoord) = 1) := by
  have h := product_v_relation _ _ _ _ _ _ (overlap_projection (k := k) a b)
  rw [specHomRingHom_comp_specMap, specHomRingHom_comp_specMap] at h
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using h

/-- Constants agree on the overlap of two charts. -/
theorem overlap_constants :
    (specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom.comp
        planeConstants =
      (specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom.comp
        planeConstants := by
  have h := product_constants _ _ _ _ _ _ (overlap_projection (k := k) a b)
  rw [specHomRingHom_comp_specMap, specHomRingHom_comp_specMap] at h
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc,
    chartBlowdown_constants] using h

theorem data_xi_eq (h : (stageOneData (k := k) a).xi = (stageOneData (k := k) b).xi) :
    (specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom
        (stageOneData (k := k) a).origU =
      (specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom
        (stageOneData (k := k) b).origU := by
  rw [stageOneData_origU, stageOneData_origU]
  rw [stageOneData_xi, stageOneData_xi] at h
  exact (overlap_u a b).1 h

theorem data_xi_ne (h : (stageOneData (k := k) a).xi ≠ (stageOneData (k := k) b).xi) :
    (specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom
        (stageOneData (k := k) a).origU *
      (specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom
        (stageOneData (k := k) b).origU = 1 := by
  rw [stageOneData_origU, stageOneData_origU]
  rw [stageOneData_xi, stageOneData_xi] at h
  exact (overlap_u a b).2 h

theorem data_yi_eq (h : (stageOneData (k := k) a).yi = (stageOneData (k := k) b).yi) :
    (specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom
        (stageOneData (k := k) a).origV =
      (specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom
        (stageOneData (k := k) b).origV := by
  rw [stageOneData_origV, stageOneData_origV]
  rw [stageOneData_yi, stageOneData_yi] at h
  exact (overlap_v a b).1 h

theorem data_yi_ne (h : (stageOneData (k := k) a).yi ≠ (stageOneData (k := k) b).yi) :
    (specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom
        (stageOneData (k := k) a).origV *
      (specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom
        (stageOneData (k := k) b).origV = 1 := by
  rw [stageOneData_origV, stageOneData_origV]
  rw [stageOneData_yi, stageOneData_yi] at h
  exact (overlap_v a b).2 h

/-- Compatibility of two chart maps from the scaling identity of their tuples on the overlap. -/
theorem chart_compatible_of_scale
    (hscale : ∀ i, (specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom
        ((stageOneData (k := k) a).tuple i) =
      (specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom
          ((stageOneData (k := k) a).tuple (stageOneData (k := k) b).ni) *
        (specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom
          ((stageOneData (k := k) b).tuple i)) :
    pullback.fst (stageOneChart (k := k) a) (stageOneChart b) ≫ chartTupleMorphism a =
      pullback.snd (stageOneChart (k := k) a) (stageOneChart b) ≫ chartTupleMorphism b := by
  have h1 := comp_tupleMorphism 7 planeConstants (stageOneData (k := k) a).tuple
    (stageOneData (k := k) a).ni (stageOneData (k := k) a).tuple_ni
    (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))
  have h2 := comp_tupleMorphism 7 planeConstants (stageOneData (k := k) b).tuple
    (stageOneData (k := k) b).ni (stageOneData (k := k) b).tuple_ni
    (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))
  have h3 := tupleMorphism_eq_of_scale
    ((specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom.comp
      planeConstants)
    ((specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom ∘
      (stageOneData (k := k) a).tuple)
    ((specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom ∘
      (stageOneData (k := k) b).tuple)
    (stageOneData (k := k) a).ni (stageOneData (k := k) b).ni
    (by simp only [Function.comp_apply, tuple_ni, map_one])
    (by simp only [Function.comp_apply, tuple_ni, map_one]) hscale
  have h4 : tupleMorphism 7
      ((specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom.comp
        planeConstants)
      ((specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom ∘
        (stageOneData (k := k) b).tuple)
      (stageOneData (k := k) b).ni (by simp only [Function.comp_apply, tuple_ni, map_one]) =
    tupleMorphism 7
      ((specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom.comp
        planeConstants)
      ((specHomRingHom (pullback.snd (stageOneChart (k := k) a) (stageOneChart b))).hom ∘
        (stageOneData (k := k) b).tuple)
      (stageOneData (k := k) b).ni (by simp only [Function.comp_apply, tuple_ni, map_one]) := by
    rw [overlap_constants a b]
  change pullback.fst _ _ ≫ tupleMorphism 7 planeConstants _ _ _ =
    pullback.snd _ _ ≫ tupleMorphism 7 planeConstants _ _ _
  rw [h1, h2, h3, h4]

/-- Compatibility when the normaliser of the first chart is a unit on the overlap. -/
theorem chart_compatible_of_isUnit
    (he : IsUnit ((specHomRingHom (pullback.fst (stageOneChart (k := k) a) (stageOneChart b))).hom
      (stageOneData (k := k) a).e)) :
    pullback.fst (stageOneChart (k := k) a) (stageOneChart b) ≫ chartTupleMorphism a =
      pullback.snd (stageOneChart (k := k) a) (stageOneChart b) ≫ chartTupleMorphism b :=
  chart_compatible_of_scale a b
    (tuple_scale_of_relations _ _ _ _ (data_xi_eq a b) (data_xi_ne a b) (data_yi_eq a b)
      (data_yi_ne a b) he)

/-- Compatibility of two charts lying over different product charts. -/
theorem chart_compatible_of_ne
    (hab : (chartIndex a).1 ≠ (chartIndex b).1 ∨ (chartIndex a).2 ≠ (chartIndex b).2) :
    pullback.fst (stageOneChart (k := k) a) (stageOneChart b) ≫ chartTupleMorphism a =
      pullback.snd (stageOneChart (k := k) a) (stageOneChart b) ≫ chartTupleMorphism b := by
  rcases hab with h | h
  · rw [← stageOneData_xi (k := k) a, ← stageOneData_xi (k := k) b] at h
    exact chart_compatible_of_isUnit a b (isUnit_e_of_xi_ne _ _ _ _ h (data_xi_ne a b))
  · rw [← stageOneData_yi (k := k) a, ← stageOneData_yi (k := k) b] at h
    exact chart_compatible_of_isUnit a b (isUnit_e_of_yi_ne _ _ _ _ h (data_yi_ne a b))

/-- Compatibility of a chart with itself. -/
theorem chart_compatible_diag :
    pullback.fst (stageOneChart (k := k) a) (stageOneChart a) ≫ chartTupleMorphism a =
      pullback.snd (stageOneChart (k := k) a) (stageOneChart a) ≫ chartTupleMorphism a := by
  rw [(cancel_mono (stageOneChart (k := k) a)).mp pullback.condition]

end Overlap

/-! ## The overlap of the two Rees charts: `w · w' = 1` -/

section Rees

variable {W : Scheme.{u}} (g₀ g₁ : W ⟶ plane k)
  (hc : (g₀ ≫ Spec.map (CommRingCat.ofHom (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toRingHom)) ≫
      chartι (centerIdeal (k := k)) centerU =
    (g₁ ≫ Spec.map (CommRingCat.ofHom (vChartPolynomialEquiv (k := k)).toRingHom)) ≫
      chartι centerIdeal centerV)

/-- The map of an overlap of the two Rees charts to the accepted product chart of the Rees `Proj`. -/
def reesOverlapMap :
    W ⟶ Spec (CommRingCat.of (conormalOverlapRing (centerIdeal (k := k)) centerU centerV)) :=
  pullback.lift _ _ hc ≫ (conormalOverlapIso centerIdeal centerU centerV).hom

theorem reesOverlapMap_left :
    reesOverlapMap g₀ g₁ hc ≫
        Spec.map (CommRingCat.ofHom (conormalOverlapLeft (centerIdeal (k := k)) centerU centerV)) =
      g₀ ≫ Spec.map (CommRingCat.ofHom (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toRingHom) := by
  rw [reesOverlapMap, Category.assoc, conormalOverlapIso_hom_left, pullback.lift_fst]

theorem reesOverlapMap_right :
    reesOverlapMap g₀ g₁ hc ≫
        Spec.map (CommRingCat.ofHom (conormalOverlapRight (centerIdeal (k := k)) centerU centerV)) =
      g₁ ≫ Spec.map (CommRingCat.ofHom (vChartPolynomialEquiv (k := k)).toRingHom) := by
  rw [reesOverlapMap, Category.assoc, conormalOverlapIso_hom_right, pullback.lift_snd]

theorem rees_w_left :
    (specHomRingHom g₀).hom vCoord =
      (specHomRingHom (reesOverlapMap g₀ g₁ hc)).hom
        (conormalOverlapLeft centerIdeal centerU centerV (chartW (k := k))) := by
  have h := specHomRingHom_congr (reesOverlapMap_left g₀ g₁ hc).symm
  have h2 := congrArg (fun φ : CommRingCat.of (reesChartRing k) ⟶ Γ(W, ⊤) => φ.hom chartW) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, chartPolynomialEquiv_w] at h2
  exact h2

theorem rees_w_right :
    (specHomRingHom g₁).hom vCoord =
      (specHomRingHom (reesOverlapMap g₀ g₁ hc)).hom
        (conormalOverlapRight centerIdeal centerU centerV
          (chartFraction (centerIdeal (k := k)) centerV centerU)) := by
  have h := specHomRingHom_congr (reesOverlapMap_right g₀ g₁ hc).symm
  have h2 := congrArg (fun φ : CommRingCat.of (reesVChartRing k) ⟶ Γ(W, ⊤) =>
    φ.hom (chartFraction centerIdeal centerV centerU)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, vChartPolynomialEquiv_coordinate] at h2
  exact h2

include hc in
theorem rees_relation_of :
    (specHomRingHom g₀).hom vCoord * (specHomRingHom g₁).hom vCoord = 1 := by
  rw [rees_w_left g₀ g₁ hc, rees_w_right g₀ g₁ hc, ← map_mul, chartW,
    conormalOverlap_chartFractions_mul, map_one]

/-- The selected Rees chart, unfolded to the Rees `Proj` chart of `u`. -/
theorem reesUChart_eq :
    reesUChart (k := k) =
      (Spec.map (CommRingCat.ofHom (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toRingHom) ≫
        chartι centerIdeal centerU) ≫ (projectiveProductInitial (k := k)).nextAffineBlowup := by
  show (projectiveProductInitial (k := k)).nextChart = _
  rw [PlaneChartedScheme.nextChart, coordinateChart]
  rfl

/-- The second Rees chart, unfolded to the Rees `Proj` chart of `v`. -/
theorem reesVChart_eq :
    reesVChart (k := k) =
      (Spec.map (CommRingCat.ofHom (vChartPolynomialEquiv (k := k)).toRingHom) ≫
        chartι centerIdeal centerV) ≫ (projectiveProductInitial (k := k)).nextAffineBlowup := by
  show secondChart (projectiveProductInitial (k := k)) 0 = _
  rw [secondChart, ← Category.assoc]
  rfl

/-- **On an overlap of the two Rees charts the coordinates `w` and `w'` are mutually inverse.** -/
theorem rees_relation (h : g₀ ≫ reesUChart = g₁ ≫ reesVChart) :
    (specHomRingHom g₀).hom vCoord * (specHomRingHom g₁).hom vCoord = 1 := by
  rw [reesUChart_eq, reesVChart_eq] at h
  simp only [← Category.assoc] at h
  exact rees_relation_of g₀ g₁
    ((cancel_mono (projectiveProductInitial (k := k)).nextAffineBlowup).mp h)

end Rees

/-! ## The two Rees charts are compatible -/

theorem rees_compatible_UV :
    pullback.fst (stageOneChart (k := k) 0) (stageOneChart 1) ≫ chartTupleMorphism 0 =
      pullback.snd (stageOneChart (k := k) 0) (stageOneChart 1) ≫ chartTupleMorphism 1 := by
  apply chart_compatible_of_scale 0 1
  set ρ₀ := (specHomRingHom (pullback.fst (stageOneChart (k := k) 0) (stageOneChart 1))).hom
    with hρ₀
  set ρ₁ := (specHomRingHom (pullback.snd (stageOneChart (k := k) 0) (stageOneChart 1))).hom
    with hρ₁
  have hx : ρ₀ uCoord = ρ₁ (uCoord * vCoord) := data_xi_eq 0 1 rfl
  have hw : ρ₀ vCoord * ρ₁ vCoord = 1 :=
    rees_relation (pullback.fst (stageOneChart (k := k) 0) (stageOneChart 1))
      (pullback.snd (stageOneChart (k := k) 0) (stageOneChart 1)) pullback.condition
  have ht : ∀ τ, ρ₀ ((stageOneData (k := k) 0).tf τ) =
      ρ₀ ((stageOneData (k := k) 0).tf (stageOneData (k := k) 1).ti) *
        ρ₁ ((stageOneData (k := k) 1).tf τ) := by
    intro τ
    fin_cases τ
    · show ρ₀ vCoord = ρ₀ vCoord * ρ₁ 1
      rw [map_one, mul_one]
    · show ρ₀ 1 = ρ₀ vCoord * ρ₁ vCoord
      rw [map_one, hw]
    · show ρ₀ (uCoord * vCoord) = ρ₀ vCoord * ρ₁ (uCoord * vCoord)
      rw [← hx, map_mul, mul_comm]
  exact tuple_scale (stageOneData (k := k) 0) (stageOneData (k := k) 1) ρ₀ ρ₁
    (xF_scale _ _ _ _ (data_xi_eq 0 1) (data_xi_ne 0 1))
    (yF_scale _ _ _ _ (data_yi_eq 0 1) (data_yi_ne 0 1)) ht

theorem rees_compatible_VU :
    pullback.fst (stageOneChart (k := k) 1) (stageOneChart 0) ≫ chartTupleMorphism 1 =
      pullback.snd (stageOneChart (k := k) 1) (stageOneChart 0) ≫ chartTupleMorphism 0 := by
  apply chart_compatible_of_scale 1 0
  set ρ₀ := (specHomRingHom (pullback.fst (stageOneChart (k := k) 1) (stageOneChart 0))).hom
    with hρ₀
  set ρ₁ := (specHomRingHom (pullback.snd (stageOneChart (k := k) 1) (stageOneChart 0))).hom
    with hρ₁
  have hy : ρ₀ uCoord = ρ₁ (uCoord * vCoord) := data_yi_eq 1 0 rfl
  have hw : ρ₁ vCoord * ρ₀ vCoord = 1 :=
    rees_relation (pullback.snd (stageOneChart (k := k) 1) (stageOneChart 0))
      (pullback.fst (stageOneChart (k := k) 1) (stageOneChart 0)) pullback.condition.symm
  have ht : ∀ τ, ρ₀ ((stageOneData (k := k) 1).tf τ) =
      ρ₀ ((stageOneData (k := k) 1).tf (stageOneData (k := k) 0).ti) *
        ρ₁ ((stageOneData (k := k) 0).tf τ) := by
    intro τ
    fin_cases τ
    · show ρ₀ 1 = ρ₀ vCoord * ρ₁ vCoord
      rw [map_one, mul_comm, hw]
    · show ρ₀ vCoord = ρ₀ vCoord * ρ₁ 1
      rw [map_one, mul_one]
    · show ρ₀ (uCoord * vCoord) = ρ₀ vCoord * ρ₁ (uCoord * vCoord)
      rw [← hy, map_mul, mul_comm]
  exact tuple_scale (stageOneData (k := k) 1) (stageOneData (k := k) 0) ρ₀ ρ₁
    (xF_scale _ _ _ _ (data_xi_eq 1 0) (data_xi_ne 1 0))
    (yF_scale _ _ _ _ (data_yi_eq 1 0) (data_yi_ne 1 0)) ht

/-! ## Gluing -/

/-- **Every pair of chart maps is compatible on the overlap.** -/
theorem glue_compatible (a b : Fin 5) :
    pullback.fst (stageOneChart (k := k) a) (stageOneChart b) ≫ chartTupleMorphism a =
      pullback.snd (stageOneChart (k := k) a) (stageOneChart b) ≫ chartTupleMorphism b := by
  fin_cases a <;> fin_cases b
  · exact chart_compatible_diag _
  · exact rees_compatible_UV
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact rees_compatible_VU
  · exact chart_compatible_diag _
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_diag _
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_diag _
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_of_ne _ _ (by decide)
  · exact chart_compatible_diag _

/-- **The morphism `stage 1 ⟶ P⁷`** of the `(2,2)`-monomials vanishing at the origin. -/
def stageOneEmbedding : stageOne (k := k) ⟶ projectiveSpace k 7 :=
  (stageOneCover (k := k)).glueMorphisms (fun i => chartTupleMorphism i.down)
    (fun i j => glue_compatible i.down j.down)

/-- On each chart the morphism is the chart's tuple morphism. -/
theorem stageOneChart_embedding (c : Fin 5) :
    stageOneChart (k := k) c ≫ stageOneEmbedding = chartTupleMorphism c :=
  (stageOneCover (k := k)).ι_glueMorphisms _ _ ⟨c⟩

/-- Every chart of stage `1` is over `k`. -/
theorem stageOneChart_structure (c : Fin 5) :
    stageOneChart (k := k) c ≫ ((projectiveProductInitial (k := k)).stage 1).structureMap =
      planeStructure := by
  change stageOneChart (k := k) c ≫ stageOneProjection ≫ projectiveProductToSpec = planeStructure
  rw [← Category.assoc, stageOneChart_projection, Category.assoc, productChart_toSpec,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, chartBlowdown_constants]
  rfl

/-- **The morphism is over `k`.** -/
theorem stageOneEmbedding_structure :
    stageOneEmbedding (k := k) ≫ projectiveSpaceToSpec k 7 =
      ((projectiveProductInitial (k := k)).stage 1).structureMap := by
  apply (stageOneCover (k := k)).hom_ext
  intro i
  rw [stageOneCover_map, ← Category.assoc, stageOneChart_embedding, stageOneChart_structure]
  exact morphism_structure _

end KltDP.Examples.FrobeniusStageOneEmbedding
