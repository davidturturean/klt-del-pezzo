import KltDP.Examples.FrobeniusStageOneReesRanges

/-!
# Localised chart squares of `stage 1 ⟶ P⁷`

For a chart `c` of stage `1` and a coordinate `m` of `P⁷`, the open piece
`localChart c m : Spec (k[u][v][1/f]) ⟶ stage 1`, `f = tuple_c(m)`, is the basic open `D(f)` of the chart
`c` (pinned open immersion `Spec.map (algebraMap R (Localization.Away f))`), and the localised tuple
`localTuple c m i = tuple_c(i) / f` (normalised at `m`) gives its map `localMorphism c m` to `P⁷` with
`localChart c m ≫ stageOneEmbedding = localMorphism c m` (`localChart_embedding`, by
`tupleMorphism_eq_of_scale`). Generic criteria:

* `localTupleChartHom_surjective`: the chart ring map onto `k[u][v][1/f]` is surjective as soon as
  `u`, `v` are localised entries (`localTuple_eq_of`: `tuple_c(i) = a · f` gives `localTuple c m i = a`),
  since `1/f = localTuple c m (ni c)`; hence `localTupleSpec c m` is a closed immersion into `D(z_m)`;
* `embedding_mem_of_dvd`: if every chart's entry `tuple_{c'}(ni c)` divides a power of `tuple_{c'}(m)`,
  points of the image in `D(z_m)` lie in `D(z_{ni c})`;
* `range_localChart`: **`range (localChart c m) = Φ⁻¹(D(z_m))`**, given the range identity of the host
  chart `c` and the divisibility hypothesis.

The eight coordinate charts of `P⁷` are treated uniformly with these pieces (for the five charts
`m = ni c` the localising element is `1`) in `FrobeniusStageOneProjective`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStageOneLocal

open KltDP.Geometry KltDP.Geometry.ProjectiveChart
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
open FrobeniusStageOneCharts FrobeniusStageOneTuples FrobeniusStageOneTuples.ChartTuple
open FrobeniusStageOneEmbedding FrobeniusStageOneClosed FrobeniusStageOneRanges

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] (c : Fin 5) (m : Fin 8)

/-- The localising element `tuple_c(m)`. -/
abbrev locElem : planeRing k := (stageOneData (k := k) c).tuple m

/-- The coordinate ring `k[u][v][1/tuple_c(m)]` of the localised piece. -/
abbrev LocRing : Type u := Localization.Away (locElem (k := k) c m)

/-- The localised piece of the chart `c`, as an open of stage `1`. -/
abbrev localChart : Spec (CommRingCat.of (LocRing (k := k) c m)) ⟶ stageOne (k := k) :=
  Spec.map (CommRingCat.ofHom (algebraMap (planeRing k) (LocRing (k := k) c m))) ≫ stageOneChart c

instance localChart_isOpenImmersion : IsOpenImmersion (localChart (k := k) c m) := by
  unfold localChart
  infer_instance

/-- The localised tuple `tuple_c(i) / tuple_c(m)`. -/
def localTuple (i : Fin 8) : LocRing (k := k) c m :=
  algebraMap (planeRing k) (LocRing (k := k) c m) ((stageOneData (k := k) c).tuple i) *
    IsLocalization.Away.invSelf (locElem (k := k) c m)

theorem localTuple_self : localTuple (k := k) c m m = 1 :=
  IsLocalization.Away.mul_invSelf (locElem (k := k) c m)

/-- `tuple_c(i) = a · tuple_c(m)` gives `localTuple c m i = a`. -/
theorem localTuple_eq_of (i : Fin 8) (a : planeRing k)
    (h : (stageOneData (k := k) c).tuple i = a * locElem (k := k) c m) :
    localTuple (k := k) c m i = algebraMap (planeRing k) (LocRing (k := k) c m) a := by
  rw [localTuple, h, map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]

theorem localTuple_ni :
    localTuple (k := k) c m (stageOneData (k := k) c).ni =
      IsLocalization.Away.invSelf (locElem (k := k) c m) := by
  rw [localTuple, tuple_ni, map_one, one_mul]

/-- The constants of the localised piece. -/
abbrev localConstants : k →+* LocRing (k := k) c m :=
  (algebraMap (planeRing k) (LocRing (k := k) c m)).comp planeConstants

/-- The map of the localised piece into the chart `D(z_m)` of `P⁷`. -/
abbrev localTupleSpec :
    Spec (CommRingCat.of (LocRing (k := k) c m)) ⟶
      Spec (CommRingCat.of (coordinateChartRing k 7 m)) :=
  tupleSpec 7 (localConstants c m) (localTuple c m) m (localTuple_self c m)

/-- The morphism of the localised piece to `P⁷`. -/
abbrev localMorphism : Spec (CommRingCat.of (LocRing (k := k) c m)) ⟶ projectiveSpace k 7 :=
  tupleMorphism 7 (localConstants c m) (localTuple c m) m (localTuple_self c m)

theorem localMorphism_eq :
    localMorphism (k := k) c m = localTupleSpec c m ≫ coordinateChartMorphism k 7 m := rfl

/-- **The localised piece is compatible with the embedding.** -/
theorem localChart_embedding : localChart (k := k) c m ≫ stageOneEmbedding = localMorphism c m := by
  rw [localChart, Category.assoc, stageOneChart_embedding]
  change Spec.map _ ≫ tupleMorphism 7 planeConstants _ _ _ = _
  rw [specMap_tupleMorphism]
  apply tupleMorphism_eq_of_scale
  intro i
  show algebraMap (planeRing k) (LocRing (k := k) c m) ((stageOneData (k := k) c).tuple i) =
    algebraMap (planeRing k) (LocRing (k := k) c m) ((stageOneData (k := k) c).tuple m) *
      (algebraMap (planeRing k) (LocRing (k := k) c m) ((stageOneData (k := k) c).tuple i) *
        IsLocalization.Away.invSelf (locElem (k := k) c m))
  rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]

/-! ## Surjectivity of the localised chart ring map -/

section Surjective

variable (iu iv : Fin 8)
  (hu : localTuple (k := k) c m iu = algebraMap (planeRing k) (LocRing (k := k) c m) uCoord)
  (hv : localTuple (k := k) c m iv = algebraMap (planeRing k) (LocRing (k := k) c m) vCoord)

include hu hv in
theorem localTupleChartHom_comp_planeToChartOf :
    (tupleChartHom 7 (localConstants c m) (localTuple c m) m (localTuple_self c m)).comp
        (planeToChartOf (k := k) m iu iv) =
      algebraMap (planeRing k) (LocRing (k := k) c m) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro a
      simp [planeToChartOf, planeConstants]
    · simp [planeToChartOf, uCoord, hu]
  · simp [planeToChartOf, vCoord, hv]

include hu hv in
/-- **The localised chart ring map is surjective** when `u`, `v` are localised entries. -/
theorem localTupleChartHom_surjective :
    Function.Surjective
      (tupleChartHom 7 (localConstants (k := k) c m) (localTuple (k := k) c m) m
        (localTuple_self c m)) := by
  intro z
  obtain ⟨p, hz⟩ := IsLocalization.surj (Submonoid.powers (locElem (k := k) c m)) z
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp p.2.2
  have hfin : algebraMap (planeRing k) (LocRing (k := k) c m) (locElem (k := k) c m ^ n) *
      IsLocalization.Away.invSelf (locElem (k := k) c m) ^ n = 1 := by
    rw [map_pow, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
  have hcomp := RingHom.congr_fun (localTupleChartHom_comp_planeToChartOf c m iu iv hu hv) p.1
  rw [RingHom.comp_apply] at hcomp
  refine ⟨planeToChartOf (k := k) m iu iv p.1 *
    chartFraction k 7 m (stageOneData (k := k) c).ni ^ n, ?_⟩
  rw [map_mul, map_pow, tupleChartHom_chartFraction, localTuple_ni, hcomp]
  calc algebraMap (planeRing k) (LocRing (k := k) c m) p.1 *
        IsLocalization.Away.invSelf (locElem (k := k) c m) ^ n
      = (z * algebraMap (planeRing k) (LocRing (k := k) c m) (p.2 : planeRing k)) *
          IsLocalization.Away.invSelf (locElem (k := k) c m) ^ n := by rw [hz]
    _ = z * (algebraMap (planeRing k) (LocRing (k := k) c m) (locElem (k := k) c m ^ n) *
          IsLocalization.Away.invSelf (locElem (k := k) c m) ^ n) := by rw [hn, mul_assoc]
    _ = z := by rw [hfin, mul_one]

include hu hv in
theorem localTupleSpec_isClosedImmersion : IsClosedImmersion (localTupleSpec (k := k) c m) :=
  tupleSpec_isClosedImmersion _ _ _ _ _ (localTupleChartHom_surjective c m iu iv hu hv)

end Surjective

/-! ## The range identity of the localised piece -/

/-- If every chart's entry at `ni c` divides a power of its entry at `m`, the image points in
`D(z_m)` lie in `D(z_{ni c})`. -/
theorem embedding_mem_of_dvd
    (hdiv : ∀ c' : Fin 5, ∃ N : ℕ, 0 < N ∧
      (stageOneData (k := k) c').tuple (stageOneData (k := k) c).ni ∣
        (stageOneData (k := k) c').tuple m ^ N)
    (x : stageOne (k := k))
    (hx : (stageOneEmbedding (k := k)).base x ∈ Set.range (coordinateChartMorphism k 7 m).base) :
    (stageOneEmbedding (k := k)).base x ∈
      Set.range (coordinateChartMorphism k 7 (stageOneData (k := k) c).ni).base := by
  obtain ⟨c', hc'⟩ := exists_chart x
  obtain ⟨q, rfl⟩ := hc'
  rw [embedding_mem_range_iff] at hx ⊢
  obtain ⟨N, hN, hd⟩ := hdiv c'
  refine mem_basicOpen_of_dvd hd q ?_
  rw [PrimeSpectrum.basicOpen_pow _ _ hN]
  exact hx

/-- **The range identity of the localised piece.** -/
theorem range_localChart
    (hrange : Set.range (stageOneChart (k := k) c).base =
      (stageOneEmbedding (k := k)).base ⁻¹'
        Set.range (coordinateChartMorphism k 7 (stageOneData (k := k) c).ni).base)
    (hdiv : ∀ c' : Fin 5, ∃ N : ℕ, 0 < N ∧
      (stageOneData (k := k) c').tuple (stageOneData (k := k) c).ni ∣
        (stageOneData (k := k) c').tuple m ^ N) :
    Set.range (localChart (k := k) c m).base =
      (stageOneEmbedding (k := k)).base ⁻¹' Set.range (coordinateChartMorphism k 7 m).base := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, rfl⟩
    rw [Set.mem_preimage, ← Scheme.comp_base_apply, localChart_embedding,
      tupleMorphism_base_mem_range_iff, localTuple_self, PrimeSpectrum.mem_basicOpen]
    exact fun h => y.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  · intro x hx
    have hx' : x ∈ Set.range (stageOneChart (k := k) c).base := by
      rw [hrange]
      exact embedding_mem_of_dvd c m hdiv x hx
    obtain ⟨y, rfl⟩ := hx'
    rw [Set.mem_preimage, embedding_mem_range_iff] at hx
    have hy : y ∈ Set.range (Spec.map (CommRingCat.ofHom
        (algebraMap (planeRing k) (LocRing (k := k) c m)))).base := by
      have e : Set.range (Spec.map (CommRingCat.ofHom
          (algebraMap (planeRing k) (LocRing (k := k) c m)))).base =
          Set.range (PrimeSpectrum.comap (algebraMap (planeRing k) (LocRing (k := k) c m))) := rfl
      rw [e, PrimeSpectrum.localization_away_comap_range (LocRing (k := k) c m) (locElem c m)]
      exact hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨y', by rw [localChart, Scheme.comp_base_apply]⟩

end KltDP.Examples.FrobeniusStageOneLocal
