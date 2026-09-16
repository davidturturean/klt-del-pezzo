import KltDP.Examples.FrobeniusStageOneChartRanges
import KltDP.Geometry.PointBlowupLocalUniqueness

/-!
# Range identities for the chart squares of `stage 1 ⟶ P⁷`: the two Rees charts

For the two Rees charts (`m = 1`: `x_0 x_1 y_0²`, the selected chart `(u, w)`; `m = 0`: `x_0² y_0 y_1`, the
second chart `(v, w')`) the reverse inclusion `Φ⁻¹(D(z_m)) ⊆ range (chart)` needs two facts about the
affine Rees blowup:

* `reesVChart_mem_range_reesUChart` / `reesUChart_mem_range_reesVChart`: a point of one Rees chart at
  which the chart coordinate `w'` (resp. `w`) is invertible lies in the other (the accepted Rees overlap
  `conormalOverlapIso` with `conormalOverlapRight/Left_isLocalization`, and the pinned
  `Scheme.Pullback.range_snd/range_fst`);
* `mem_range_reesUChart_of'` / `mem_range_reesVChart_of'`: a point of stage `1` over the chart `(0,0)`
  at which `u` (resp. `v`) is invertible lies in the `u`- (resp. `v`-) Rees chart (accepted
  `range_affineBlowupι`: points over the chart `(0,0)` are in the affine blowup; accepted
  `affineBlowup_cover`; `chartBaseMap_mul_chartFraction`: `u = v · (u/v)` on the `v`-chart).

With `embedding_mem_range_iff` and the divisibility of the transition entries this gives
`range_stageOneChart_zero`, `range_stageOneChart_one`: **`range (stageOneChart c) = Φ⁻¹(D(z_{ni c}))`**
for `c = 0, 1`. Together with `FrobeniusStageOneChartRanges` all five chart squares of
`stageOneEmbedding` over the charts `D(z_{ni c})` have their range identity; the three charts
`m = 2, 4, 6` of `P⁷` remain.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStageOneReesRanges

open KltDP.Geometry KltDP.Geometry.ProjectiveChart KltDP.Geometry.ProjectiveLineComparison
open KltDP.Geometry.ProjectiveSegreCover KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
open FrobeniusExceptionalCharts
open FrobeniusProjectivePoints FrobeniusProductPlaneChart FrobeniusGraphPicardClassCharts
open FrobeniusGlobalBlowupStages FrobeniusTowerSecondChart FrobeniusTowerSecondChart.PlaneChartedScheme
open FrobeniusTowerChartCover
open FrobeniusStageOneCharts FrobeniusStageOneTuples FrobeniusStageOneTuples.ChartTuple
open FrobeniusStageOneEmbedding FrobeniusStageOneClosed FrobeniusStageOneRanges

variable {k : Type u} [Field k]

/-- The selected origin has the accepted maximal centre ideal. -/
local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The inclusion of the affine Rees blowup into stage `1`. -/
abbrev blowupInclusion : AffineBlowup.scheme (centerIdeal (k := k)) ⟶ stageOne (k := k) :=
  (projectiveProductInitial (k := k)).nextAffineBlowup

/-! ## The overlap of the two Rees charts of the affine blowup -/

theorem range_reesOverlap_snd :
    Set.range (pullback.snd (chartι (centerIdeal (k := k)) centerU) (chartι centerIdeal centerV)).base =
      (PrimeSpectrum.basicOpen (chartFraction (centerIdeal (k := k)) centerV centerU) :
        Set (PrimeSpectrum (reesVChartRing k))) := by
  rw [← conormalOverlapIso_hom_right, range_comp_base_of_isIso]
  exact range_specMap_of_isLocalization_away _ _ (conormalOverlapRight_isLocalization _ _ _)

theorem range_reesOverlap_fst :
    Set.range (pullback.fst (chartι (centerIdeal (k := k)) centerU) (chartι centerIdeal centerV)).base =
      (PrimeSpectrum.basicOpen (chartFraction (centerIdeal (k := k)) centerU centerV) :
        Set (PrimeSpectrum (reesChartRing k))) := by
  rw [← conormalOverlapIso_hom_left, range_comp_base_of_isIso]
  exact range_specMap_of_isLocalization_away _ _ (conormalOverlapLeft_isLocalization _ _ _)

/-- A point of the Rees chart of `v` at which `u/v` is invertible lies in the Rees chart of `u`. -/
theorem chartιV_mem_range_chartιU (q : Spec (CommRingCat.of (reesVChartRing k)))
    (hq : q ∈ PrimeSpectrum.basicOpen (chartFraction (centerIdeal (k := k)) centerV centerU)) :
    (chartι centerIdeal centerV).base q ∈ Set.range (chartι (centerIdeal (k := k)) centerU).base := by
  have h := Scheme.Pullback.range_snd (chartι (centerIdeal (k := k)) centerU) (chartι centerIdeal centerV)
  rw [range_reesOverlap_snd] at h
  exact (Set.ext_iff.mp h q).mp hq

/-- A point of the Rees chart of `u` at which `v/u` is invertible lies in the Rees chart of `v`. -/
theorem chartιU_mem_range_chartιV (q : Spec (CommRingCat.of (reesChartRing k)))
    (hq : q ∈ PrimeSpectrum.basicOpen (chartFraction (centerIdeal (k := k)) centerU centerV)) :
    (chartι centerIdeal centerU).base q ∈ Set.range (chartι (centerIdeal (k := k)) centerV).base := by
  have h := Scheme.Pullback.range_fst (chartι (centerIdeal (k := k)) centerU) (chartι centerIdeal centerV)
  rw [range_reesOverlap_fst] at h
  exact (Set.ext_iff.mp h q).mp hq

/-! ## Transport to the polynomial models -/

theorem reesUChart_eq' :
    reesUChart (k := k) = (coordinateChartIso.hom ≫ chartι centerIdeal centerU) ≫ blowupInclusion := rfl

theorem reesVChart_eq' :
    reesVChart (k := k) = vChartIso.hom ≫ chartι centerIdeal centerV ≫ blowupInclusion := rfl

theorem range_reesUChart :
    Set.range (reesUChart (k := k)).base =
      Set.range (chartι (centerIdeal (k := k)) centerU ≫ blowupInclusion).base := by
  rw [reesUChart_eq', Category.assoc]
  exact range_comp_base_of_isIso _ _

theorem range_reesVChart :
    Set.range (reesVChart (k := k)).base =
      Set.range (chartι (centerIdeal (k := k)) centerV ≫ blowupInclusion).base := by
  rw [reesVChart_eq']
  exact range_comp_base_of_isIso _ _

theorem reesUChart_apply (q : plane k) :
    (reesUChart (k := k)).base q =
      blowupInclusion.base ((chartι centerIdeal centerU).base
        ((Spec.map (CommRingCat.ofHom
          (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toRingHom)).base q)) := by
  rw [reesUChart_eq', Scheme.comp_base_apply, Scheme.comp_base_apply]
  rfl

theorem reesVChart_apply (q : plane k) :
    (reesVChart (k := k)).base q =
      blowupInclusion.base ((chartι centerIdeal centerV).base
        ((Spec.map (CommRingCat.ofHom (vChartPolynomialEquiv (k := k)).toRingHom)).base q)) := by
  rw [reesVChart_eq', Scheme.comp_base_apply, Scheme.comp_base_apply]
  rfl

/-- A point of the second Rees chart at which `w'` is invertible lies in the selected Rees chart. -/
theorem reesVChart_mem_range_reesUChart (q : plane k)
    (hq : q ∈ PrimeSpectrum.basicOpen (vCoord (k := k))) :
    (reesVChart (k := k)).base q ∈ Set.range (reesUChart (k := k)).base := by
  rw [range_reesUChart, reesVChart_apply]
  have hq' : (Spec.map (CommRingCat.ofHom (vChartPolynomialEquiv (k := k)).toRingHom)).base q ∈
      PrimeSpectrum.basicOpen (chartFraction (centerIdeal (k := k)) centerV centerU) := by
    rw [specMap_base_mem_basicOpen_iff]
    have h : (vChartPolynomialEquiv (k := k)).toRingHom
        (chartFraction centerIdeal centerV centerU) = vCoord := vChartPolynomialEquiv_coordinate
    rw [h]
    exact hq
  obtain ⟨q₂, hq₂⟩ := chartιV_mem_range_chartιU _ hq'
  exact ⟨q₂, by rw [Scheme.comp_base_apply, hq₂]⟩

/-- A point of the selected Rees chart at which `w` is invertible lies in the second Rees chart. -/
theorem reesUChart_mem_range_reesVChart (q : plane k)
    (hq : q ∈ PrimeSpectrum.basicOpen (vCoord (k := k))) :
    (reesUChart (k := k)).base q ∈ Set.range (reesVChart (k := k)).base := by
  rw [range_reesVChart, reesUChart_apply]
  have hq' : (Spec.map (CommRingCat.ofHom
      (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toRingHom)).base q ∈
      PrimeSpectrum.basicOpen (chartFraction (centerIdeal (k := k)) centerU centerV) := by
    rw [specMap_base_mem_basicOpen_iff]
    have h : (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toRingHom
        (chartFraction centerIdeal centerU centerV) = vCoord := chartPolynomialEquiv_w
    rw [h]
    exact hq
  obtain ⟨q₂, hq₂⟩ := chartιU_mem_range_chartιV _ hq'
  exact ⟨q₂, by rw [Scheme.comp_base_apply, hq₂]⟩

/-! ## Points over the chart `(0,0)` -/

/-- A point of stage `1` over the chart `(0,0)` lies in the affine blowup, over the same point. -/
theorem exists_blowup_point (x : stageOne (k := k)) (q₀ : plane k)
    (hx : stageOneProjection.base x = planeChart.base q₀) :
    ∃ a : AffineBlowup.scheme (centerIdeal (k := k)),
      blowupInclusion.base a = x ∧ (toSpec centerIdeal).base a = q₀ := by
  have hmem : x ∈ Set.range (PointBlowupGluing.affineBlowupι planeChart originPoint
      (projectiveProductInitial (k := k)).center_closed).base := by
    rw [PointBlowupGluing.range_affineBlowupι]
    exact ⟨q₀, hx.symm⟩
  obtain ⟨a, rfl⟩ := hmem
  refine ⟨a, rfl, ?_⟩
  apply planeChart.isOpenEmbedding.injective
  rw [← hx]
  change _ = ((projectiveProductInitial (k := k)).nextAffineBlowup ≫
    (projectiveProductInitial (k := k)).nextProjection).base a
  rw [(projectiveProductInitial (k := k)).nextAffineBlowup_projection, Scheme.comp_base_apply]
  rfl

/-- **A point of stage `1` over the chart `(0,0)` with `u` invertible lies in the selected Rees
chart.** -/
theorem mem_range_reesUChart_of (x : stageOne (k := k)) (q₀ : plane k)
    (hx : stageOneProjection.base x = planeChart.base q₀)
    (hu : q₀ ∈ PrimeSpectrum.basicOpen (uCoord (k := k))) :
    x ∈ Set.range (reesUChart (k := k)).base := by
  obtain ⟨a, rfl, ha⟩ := exists_blowup_point x q₀ hx
  rw [range_reesUChart]
  rcases affineBlowup_cover a with h | h
  · obtain ⟨q₂, rfl⟩ : ∃ y, (chartι (centerIdeal (k := k)) centerU).base y = a := h
    exact ⟨q₂, by rw [Scheme.comp_base_apply]⟩
  · obtain ⟨q₁, rfl⟩ : ∃ y, (chartι (centerIdeal (k := k)) centerV).base y = a := h
    have hq₀ : (Spec.map (CommRingCat.ofHom (chartBaseMap (centerIdeal (k := k)) centerV))).base q₁ =
        q₀ := by
      rw [← ha, ← Scheme.comp_base_apply, chartι_toSpec]
      rfl
    have h1 : q₁ ∈ PrimeSpectrum.basicOpen (chartBaseMap centerIdeal centerV (uCoord (k := k))) := by
      rw [← specMap_base_mem_basicOpen_iff, hq₀]
      exact hu
    have h2 := chartBaseMap_mul_chartFraction (centerIdeal (k := k)) centerV centerU
    change chartBaseMap centerIdeal centerV vCoord * chartFraction centerIdeal centerV centerU =
      chartBaseMap centerIdeal centerV uCoord at h2
    rw [← h2] at h1
    obtain ⟨q₂, hq₂⟩ := chartιV_mem_range_chartιU q₁ (mem_basicOpen_of_dvd (dvd_mul_left _ _) q₁ h1)
    exact ⟨q₂, by rw [Scheme.comp_base_apply, hq₂]⟩

/-- **A point of stage `1` over the chart `(0,0)` with `v` invertible lies in the second Rees
chart.** -/
theorem mem_range_reesVChart_of (x : stageOne (k := k)) (q₀ : plane k)
    (hx : stageOneProjection.base x = planeChart.base q₀)
    (hv : q₀ ∈ PrimeSpectrum.basicOpen (vCoord (k := k))) :
    x ∈ Set.range (reesVChart (k := k)).base := by
  obtain ⟨a, rfl, ha⟩ := exists_blowup_point x q₀ hx
  rw [range_reesVChart]
  rcases affineBlowup_cover a with h | h
  · obtain ⟨q₂, rfl⟩ : ∃ y, (chartι (centerIdeal (k := k)) centerU).base y = a := h
    have hq₀ : (Spec.map (CommRingCat.ofHom (chartBaseMap (centerIdeal (k := k)) centerU))).base q₂ =
        q₀ := by
      rw [← ha, ← Scheme.comp_base_apply, chartι_toSpec]
      rfl
    have h1 : q₂ ∈ PrimeSpectrum.basicOpen (chartBaseMap centerIdeal centerU (vCoord (k := k))) := by
      rw [← specMap_base_mem_basicOpen_iff, hq₀]
      exact hv
    have h2 := chartBaseMap_mul_chartFraction (centerIdeal (k := k)) centerU centerV
    change chartBaseMap centerIdeal centerU uCoord * chartFraction centerIdeal centerU centerV =
      chartBaseMap centerIdeal centerU vCoord at h2
    rw [← h2] at h1
    obtain ⟨q₁, hq₁⟩ := chartιU_mem_range_chartιV q₂ (mem_basicOpen_of_dvd (dvd_mul_left _ _) q₂ h1)
    exact ⟨q₁, by rw [Scheme.comp_base_apply, hq₁]⟩
  · obtain ⟨q₁, rfl⟩ : ∃ y, (chartι (centerIdeal (k := k)) centerV).base y = a := h
    exact ⟨q₁, by rw [Scheme.comp_base_apply]⟩

/-- Points over the chart `(0,0)` that lie in the chart `(1,0)` are in the selected Rees chart. -/
theorem mem_range_reesUChart_of' (x : stageOne (k := k))
    (h0 : stageOneProjection.base x ∈ Set.range planeChart.base)
    (h1 : stageOneProjection.base x ∈ Set.range (productChart (k := k) 1 0).base) :
    x ∈ Set.range (reesUChart (k := k)).base := by
  obtain ⟨q₀, hq₀⟩ := h0
  have hu : q₀ ∈ PrimeSpectrum.basicOpen (uCoord (k := k)) := by
    rw [← hq₀, ← productChart_zero_zero, productChart_mem_range_iff] at h1
    exact h1.1 (by decide)
  exact mem_range_reesUChart_of x q₀ hq₀.symm hu

/-- Points over the chart `(0,0)` that lie in the chart `(0,1)` are in the second Rees chart. -/
theorem mem_range_reesVChart_of' (x : stageOne (k := k))
    (h0 : stageOneProjection.base x ∈ Set.range planeChart.base)
    (h1 : stageOneProjection.base x ∈ Set.range (productChart (k := k) 0 1).base) :
    x ∈ Set.range (reesVChart (k := k)).base := by
  obtain ⟨q₀, hq₀⟩ := h0
  have hv : q₀ ∈ PrimeSpectrum.basicOpen (vCoord (k := k)) := by
    rw [← hq₀, ← productChart_zero_zero, productChart_mem_range_iff] at h1
    exact h1.2 (by decide)
  exact mem_range_reesVChart_of x q₀ hq₀.symm hv

theorem punctureChart_projection_apply (i j : Fin 2) (h : (i, j) ≠ (0, 0)) (q : plane k) :
    stageOneProjection.base ((punctureChart i j h).base q) = (productChart (k := k) i j).base q := by
  rw [← Scheme.comp_base_apply, punctureChart_projection]

/-! ## The range identities for the Rees charts -/

/-- **The range identity for the selected Rees chart** (`m = 1`, `x_0 x_1 y_0²`). -/
theorem range_stageOneChart_zero :
    Set.range (stageOneChart (k := k) 0).base =
      (stageOneEmbedding (k := k)).base ⁻¹'
        Set.range (coordinateChartMorphism k 7 (stageOneData (k := k) 0).ni).base := by
  apply Set.Subset.antisymm (range_stageOneChart_subset 0)
  intro x hx
  obtain ⟨c', hc'⟩ := exists_chart x
  obtain ⟨q, rfl⟩ := hc'
  rw [Set.mem_preimage, embedding_mem_range_iff] at hx
  fin_cases c'
  · exact ⟨q, rfl⟩
  · have hv : q ∈ PrimeSpectrum.basicOpen (vCoord (k := k)) :=
      mem_basicOpen_of_dvd (Dvd.intro (1 * 1) (by show vCoord * (1 * 1) = 1 * 1 * vCoord; ring)) q hx
    exact reesVChart_mem_range_reesUChart q hv
  · have hu : q ∈ PrimeSpectrum.basicOpen (uCoord (k := k)) :=
      mem_basicOpen_of_dvd (Dvd.intro (1 * 1) (by show uCoord * (1 * 1) = uCoord * 1 * 1; ring)) q hx
    apply mem_range_reesUChart_of'
    · show stageOneProjection.base ((punctureChart 1 0 ne_zero_zero_10).base q) ∈ _
      rw [punctureChart_projection_apply, ← productChart_zero_zero, productChart_mem_range_iff]
      exact ⟨fun _ => hu, fun h => absurd rfl h⟩
    · show stageOneProjection.base ((punctureChart 1 0 ne_zero_zero_10).base q) ∈ _
      rw [punctureChart_projection_apply]
      exact ⟨q, rfl⟩
  · have hu : q ∈ PrimeSpectrum.basicOpen (uCoord (k := k)) :=
      mem_basicOpen_of_dvd (Dvd.intro (vCoord * vCoord)
        (by show uCoord * (vCoord * vCoord) = 1 * vCoord * (uCoord * vCoord); ring)) q hx
    have hv : q ∈ PrimeSpectrum.basicOpen (vCoord (k := k)) :=
      mem_basicOpen_of_dvd (Dvd.intro (uCoord * vCoord)
        (by show vCoord * (uCoord * vCoord) = 1 * vCoord * (uCoord * vCoord); ring)) q hx
    apply mem_range_reesUChart_of'
    · show stageOneProjection.base ((punctureChart 0 1 ne_zero_zero_01).base q) ∈ _
      rw [punctureChart_projection_apply, ← productChart_zero_zero, productChart_mem_range_iff]
      exact ⟨fun h => absurd rfl h, fun _ => hv⟩
    · show stageOneProjection.base ((punctureChart 0 1 ne_zero_zero_01).base q) ∈ _
      rw [punctureChart_projection_apply, productChart_mem_range_iff]
      exact ⟨fun _ => hu, fun _ => hv⟩
  · have hu : q ∈ PrimeSpectrum.basicOpen (uCoord (k := k)) :=
      mem_basicOpen_of_dvd (Dvd.intro (vCoord * vCoord)
        (by show uCoord * (vCoord * vCoord) = uCoord * vCoord * vCoord; ring)) q hx
    have hv : q ∈ PrimeSpectrum.basicOpen (vCoord (k := k)) :=
      mem_basicOpen_of_dvd (Dvd.intro (uCoord * vCoord)
        (by show vCoord * (uCoord * vCoord) = uCoord * vCoord * vCoord; ring)) q hx
    apply mem_range_reesUChart_of'
    · show stageOneProjection.base ((punctureChart 1 1 ne_zero_zero_11).base q) ∈ _
      rw [punctureChart_projection_apply, ← productChart_zero_zero, productChart_mem_range_iff]
      exact ⟨fun _ => hu, fun _ => hv⟩
    · show stageOneProjection.base ((punctureChart 1 1 ne_zero_zero_11).base q) ∈ _
      rw [punctureChart_projection_apply, productChart_mem_range_iff]
      exact ⟨fun h => absurd rfl h, fun _ => hv⟩

/-- **The range identity for the second Rees chart** (`m = 0`, `x_0² y_0 y_1`). -/
theorem range_stageOneChart_one :
    Set.range (stageOneChart (k := k) 1).base =
      (stageOneEmbedding (k := k)).base ⁻¹'
        Set.range (coordinateChartMorphism k 7 (stageOneData (k := k) 1).ni).base := by
  apply Set.Subset.antisymm (range_stageOneChart_subset 1)
  intro x hx
  obtain ⟨c', hc'⟩ := exists_chart x
  obtain ⟨q, rfl⟩ := hc'
  rw [Set.mem_preimage, embedding_mem_range_iff] at hx
  fin_cases c'
  · have hv : q ∈ PrimeSpectrum.basicOpen (vCoord (k := k)) :=
      mem_basicOpen_of_dvd (Dvd.intro (1 * 1) (by show vCoord * (1 * 1) = 1 * 1 * vCoord; ring)) q hx
    exact reesUChart_mem_range_reesVChart q hv
  · exact ⟨q, rfl⟩
  · have hu : q ∈ PrimeSpectrum.basicOpen (uCoord (k := k)) :=
      mem_basicOpen_of_dvd (Dvd.intro (uCoord * vCoord)
        (by show uCoord * (uCoord * vCoord) = uCoord * 1 * (uCoord * vCoord); ring)) q hx
    have hv : q ∈ PrimeSpectrum.basicOpen (vCoord (k := k)) :=
      mem_basicOpen_of_dvd (Dvd.intro (uCoord * uCoord)
        (by show vCoord * (uCoord * uCoord) = uCoord * 1 * (uCoord * vCoord); ring)) q hx
    apply mem_range_reesVChart_of'
    · show stageOneProjection.base ((punctureChart 1 0 ne_zero_zero_10).base q) ∈ _
      rw [punctureChart_projection_apply, ← productChart_zero_zero, productChart_mem_range_iff]
      exact ⟨fun _ => hu, fun h => absurd rfl h⟩
    · show stageOneProjection.base ((punctureChart 1 0 ne_zero_zero_10).base q) ∈ _
      rw [punctureChart_projection_apply, productChart_mem_range_iff]
      exact ⟨fun _ => hu, fun _ => hv⟩
  · have hv : q ∈ PrimeSpectrum.basicOpen (vCoord (k := k)) :=
      mem_basicOpen_of_dvd (Dvd.intro (1 * 1) (by show vCoord * (1 * 1) = 1 * vCoord * 1; ring)) q hx
    apply mem_range_reesVChart_of'
    · show stageOneProjection.base ((punctureChart 0 1 ne_zero_zero_01).base q) ∈ _
      rw [punctureChart_projection_apply, ← productChart_zero_zero, productChart_mem_range_iff]
      exact ⟨fun h => absurd rfl h, fun _ => hv⟩
    · show stageOneProjection.base ((punctureChart 0 1 ne_zero_zero_01).base q) ∈ _
      rw [punctureChart_projection_apply]
      exact ⟨q, rfl⟩
  · have hu : q ∈ PrimeSpectrum.basicOpen (uCoord (k := k)) :=
      mem_basicOpen_of_dvd (Dvd.intro (vCoord * uCoord)
        (by show uCoord * (vCoord * uCoord) = uCoord * vCoord * uCoord; ring)) q hx
    have hv : q ∈ PrimeSpectrum.basicOpen (vCoord (k := k)) :=
      mem_basicOpen_of_dvd (Dvd.intro (uCoord * uCoord)
        (by show vCoord * (uCoord * uCoord) = uCoord * vCoord * uCoord; ring)) q hx
    apply mem_range_reesVChart_of'
    · show stageOneProjection.base ((punctureChart 1 1 ne_zero_zero_11).base q) ∈ _
      rw [punctureChart_projection_apply, ← productChart_zero_zero, productChart_mem_range_iff]
      exact ⟨fun _ => hu, fun _ => hv⟩
    · show stageOneProjection.base ((punctureChart 1 1 ne_zero_zero_11).base q) ∈ _
      rw [punctureChart_projection_apply, productChart_mem_range_iff]
      exact ⟨fun _ => hu, fun h => absurd rfl h⟩

end KltDP.Examples.FrobeniusStageOneReesRanges
