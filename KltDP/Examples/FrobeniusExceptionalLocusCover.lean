import KltDP.Examples.FrobeniusSpecialFiberSPn

/-!
# The exceptional locus is covered by the final exceptional components

On any charted plane tower, every point of stage `q+1` lying over the centre lies on one of the
final exceptional components `C_j` (`finalOldMap`) or `P` (`previousFiberι`) —
`exceptionalLocus_covered`. Induction on the stage: a point over the current centre lies on the
newest fibre (`range_globalCenterFiberι`); otherwise its image at the previous stage lies on a component
by induction, and it lifts into the corresponding component of the new stage — through
`mem_finalOldMap_iff` for the older curves, and through the accepted whole-fibre lift
`wholePreviousLift` (whose kernel defines the strict transform of the previous newest fibre) together
with the injectivity of the one-step projection off the centre.

Consequences: the exceptional locus of the translated tower is exactly `⋃_j C_j ∪ P`, so the support of
the complete scheme-theoretic fibre is exactly `F̃ ∪ ⋃_j C_j ∪ P` (`specialFiberSupport_eq_components`);
on `S_{p,n}` the exceptional locus of the `i`-th cluster is `⋃ E_{i,idx}` and the special fibre over
`(a i)^p` has support `F_i ∪ ⋃_idx E_{i,idx}` (`specialFiberSSupport_eq_components`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusExceptionalLocusCover

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
  FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusContactTowerSelectedPoint
  FrobeniusGlobalExceptionalSuccessor FrobeniusExceptionalFinalConfiguration
  FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber
  FrobeniusFiberClosure FrobeniusSpecialFiberTower FrobeniusSpecialFiberSPn

variable {k : Type u} [Field k]

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

section Tower

variable (A : PlaneChartedScheme k)

/-! ## The one-step projection is injective off the centre -/

/-- The one-step projection restricted to the complement of the centre. -/
def stepPunctureMap (n : ℕ) :
    (A.stepProjection n ⁻¹ᵁ initialPuncture (A.stage n)).toScheme ⟶ (A.stage n).carrier :=
  (A.stepProjection n ∣_ initialPuncture (A.stage n)) ≫ (initialPuncture (A.stage n)).ι

instance stepPunctureMap_isOpenImmersion (n : ℕ) : IsOpenImmersion (stepPunctureMap A n) := by
  letI : IsIso (A.stepProjection n ∣_ initialPuncture (A.stage n)) :=
    nextProjection_restrict_isIso (A.stage n)
  unfold stepPunctureMap
  infer_instance

theorem stepPunctureMap_base (n : ℕ)
    (y : (A.stepProjection n ⁻¹ᵁ initialPuncture (A.stage n)).toScheme) :
    (stepPunctureMap A n).base y =
      (A.stepProjection n).base ((A.stepProjection n ⁻¹ᵁ initialPuncture (A.stage n)).ι.base y) := by
  rw [stepPunctureMap, morphismRestrict_ι, Scheme.comp_base_apply]

theorem stepProjection_injective (n : ℕ) {x y : (A.stage (n + 1)).carrier}
    (hx : (A.stepProjection n).base x ≠ (A.stage n).chart.base (originPoint (k := k)))
    (hy : (A.stepProjection n).base y ≠ (A.stage n).chart.base (originPoint (k := k)))
    (h : (A.stepProjection n).base x = (A.stepProjection n).base y) : x = y := by
  have hx' : x ∈ A.stepProjection n ⁻¹ᵁ initialPuncture (A.stage n) := hx
  have hy' : y ∈ A.stepProjection n ⁻¹ᵁ initialPuncture (A.stage n) := hy
  have h' : (⟨x, hx'⟩ : (A.stepProjection n ⁻¹ᵁ initialPuncture (A.stage n)).toScheme) =
      ⟨y, hy'⟩ := by
    apply (stepPunctureMap A n).isOpenEmbedding.injective
    rw [stepPunctureMap_base, stepPunctureMap_base]
    exact h
  exact congrArg Subtype.val h'

/-! ## The two kinds of components -/

/-- A point of the next stage lies on the newest fibre iff it lies over the centre. -/
theorem mem_previousFiber_iff (n : ℕ) (x : (A.stage (n + 1)).carrier) :
    x ∈ Set.range (previousFiberι (A.stage n)).base ↔
      (A.stepProjection n).base x = (A.stage n).chart.base (originPoint (k := k)) := by
  change x ∈ Set.range (PointBlowupGluing.globalCenterFiberι (A.stage n).chart
    (originPoint (k := k)) (A.stage n).center_closed).base ↔ _
  rw [PointBlowupGluing.range_globalCenterFiberι]
  exact Iff.rfl

theorem previousFiber_noetherianSpace (B : PlaneChartedScheme k) :
    TopologicalSpace.NoetherianSpace (previousFiber B) := by
  letI := projectiveSpace_noetherianSpace k 1
  exact (previousFiberIso B).hom.isOpenEmbedding.isInducing.noetherianSpace

/-- The strict transform of the previous newest fibre is the closure of its whole punctured lift. -/
theorem range_previousStrictι_eq_closure_lift (B : PlaneChartedScheme k) :
    Set.range (previousStrictι B).base = closure (Set.range (wholePreviousLift B).base) := by
  letI := previousFiber_noetherianSpace B
  letI : TopologicalSpace.NoetherianSpace (previousPuncture B).toScheme :=
    (previousPuncture B).ι.isOpenEmbedding.isInducing.noetherianSpace
  rw [Scheme.IdealSheafData.range_gluedTo]
  exact Scheme.Hom.support_ker (wholePreviousLift B)

/-! ## The covering lemma -/

/-- Every point of stage `q + 1` over the centre lies on a final exceptional component. -/
theorem exceptionalLocus_covered : ∀ (q : ℕ) (x : (A.stage (q + 1)).carrier),
    (A.toInitial (q + 1)).base x = A.chart.base (originPoint (k := k)) →
      ∃ idx : FinalIndex.{0} q, x ∈ finalSupport A q idx
  | 0, x, hx => by
    refine ⟨Sum.inr PUnit.unit, ?_⟩
    change x ∈ Set.range (previousFiberι (A.stage 0)).base
    rw [mem_previousFiber_iff]
    exact hx
  | q + 1, x, hx => by
    by_cases hc : (A.stepProjection (q + 1)).base x =
        (A.stage (q + 1)).chart.base (originPoint (k := k))
    · exact ⟨Sum.inr PUnit.unit, (mem_previousFiber_iff A (q + 1) x).mpr hc⟩
    · have hy : (A.toInitial (q + 1)).base ((A.stepProjection (q + 1)).base x) =
          A.chart.base (originPoint (k := k)) := by
        rw [← Scheme.comp_base_apply]
        exact hx
      obtain ⟨idx, hidx⟩ := exceptionalLocus_covered q _ hy
      cases idx with
      | inl j =>
        refine ⟨Sum.inl (Fin.castSucc j), ?_⟩
        change x ∈ Set.range (finalOldMap A (q + 1 + 1) j.val (by omega)).base
        exact (mem_finalOldMap_iff (A := A) (M := q + 1) (j := j.val) (by omega) (by omega) x).mpr
          (by rw [between_step]; exact hidx)
      | inr _ =>
        refine ⟨Sum.inl (Fin.last q), ?_⟩
        change x ∈ Set.range (finalOldMap A (q + 1 + 1) q (by omega)).base
        rw [range_finalOldMap, Set.mem_preimage]
        have hb : between A (show q + 2 ≤ q + 1 + 1 by omega) = 𝟙 _ := between_refl A (q + 2)
        rw [hb]
        change x ∈ Set.range (previousStrictι (A.stage q)).base
        rw [range_previousStrictι_eq_closure_lift]
        apply subset_closure
        obtain ⟨y', hy'⟩ := hidx
        have hy'' : (previousFiberι (A.stage q)).base y' = (A.stepProjection (q + 1)).base x := hy'
        have hyp' : (previousFiberι (A.stage q)).base y' ≠
            (A.stage (q + 1)).chart.base (originPoint (k := k)) := by
          rw [hy'']
          exact hc
        have hyp : y' ∈ previousPuncture (A.stage q) := hyp'
        have hw := congrArg (fun f => f.base (⟨y', hyp⟩ : (previousPuncture (A.stage q)).toScheme))
          (wholePreviousLift_projection (A.stage q))
        dsimp only at hw
        rw [Scheme.comp_base_apply, Scheme.comp_base_apply, Scheme.Opens.ι_base_apply] at hw
        have hw' : (A.stepProjection (q + 1)).base ((wholePreviousLift (A.stage q)).base ⟨y', hyp⟩) =
            (previousFiberι (A.stage q)).base y' := hw
        refine ⟨⟨y', hyp⟩, ?_⟩
        apply stepProjection_injective A (q + 1)
        · rw [hw']
          exact hyp'
        · exact hc
        · rw [hw']
          exact hy''

end Tower

/-! ## Consequences for the special fibres -/

section Translated

variable (p : ℕ) (a : k) (q : ℕ)

/-- The exceptional locus of the translated tower is the union of the final components. -/
theorem exceptionalLocus_eq_iUnion :
    exceptionalLocus p a (q + 1) =
      ⋃ idx : FinalIndex.{0} q, finalSupport (translatedInitial p a) q idx := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : ((translatedInitial p a).toInitial (q + 1)).base x =
        (translatedInitial p a).chart.base (originPoint (k := k)) := by
      have h : (selectedProjection p a (q + 1)).base x = graphPoint p a := hx
      rw [← selected_center] at h
      exact h
    obtain ⟨idx, hidx⟩ := exceptionalLocus_covered (translatedInitial p a) q x hx'
    exact Set.mem_iUnion.mpr ⟨idx, hidx⟩
  · intro x hx
    obtain ⟨idx, hidx⟩ := Set.mem_iUnion.mp hx
    exact finalSupport_subset_exceptionalLocus p a q idx hidx

/-- The support of the complete scheme-theoretic fibre is exactly `F̃ ∪ ⋃_j C_j ∪ P`. -/
theorem specialFiberSupport_eq_components :
    specialFiberSupport p a (q + 1) =
      Set.range (fiberClosureInclusion (translatedInitial p a) (q + 1)).base ∪
        ⋃ idx : FinalIndex.{0} q, finalSupport (translatedInitial p a) q idx := by
  rw [specialFiberSupport_eq_union, exceptionalLocus_eq_iUnion]

end Translated

section Multi

variable (q n : ℕ) (a : Fin n → k)

/-- The exceptional locus of the `i`-th cluster of `S_{p,n}` is the union of its exceptional curves. -/
theorem clusterLocus_eq_iUnion (i : Fin n) :
    clusterLocus q n a i = ⋃ idx : FinalIndex.{0} q, exceptionalSupport q n a i idx := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : (selectedProjection (q + 1) (a i) (q + 1)).base
        ((towerProjection (q + 1) n a i).base x) = graphPoint (q + 1) (a i) := by
      rw [← Scheme.comp_base_apply, towerProjection_projection]
      exact hx
    have hloc : (towerProjection (q + 1) n a i).base x ∈ exceptionalLocus (q + 1) (a i) (q + 1) := hx'
    rw [exceptionalLocus_eq_iUnion] at hloc
    obtain ⟨idx, hidx⟩ := Set.mem_iUnion.mp hloc
    refine Set.mem_iUnion.mpr ⟨idx, ?_⟩
    rw [exceptionalSupport_eq]
    exact hidx
  · intro x hx
    obtain ⟨idx, hidx⟩ := Set.mem_iUnion.mp hx
    exact exceptionalSupport_subset_clusterLocus q n a i idx hidx

variable [IsAlgClosed k] [Fact (q + 1).Prime] [CharP k (q + 1)] (ha : Function.Injective a)
include ha

/-- The support of the special fibre of `S_{p,n}` over `(a i)^p` is exactly `F_i ∪ ⋃_idx E_{i,idx}`. -/
theorem specialFiberSSupport_eq_components (i : Fin n) :
    specialFiberSSupport q n a i =
      Set.range (fiberStrictι (q + 1) n a i).base ∪
        ⋃ idx : FinalIndex.{0} q, exceptionalSupport q n a i idx := by
  rw [specialFiberSSupport_eq_union q n a ha i, clusterLocus_eq_iUnion]

end Multi

end KltDP.Examples.FrobeniusExceptionalLocusCover

namespace KltDP.Examples

open KltDP.Geometry FrobeniusTranslatedCharts FrobeniusExceptionalFinalConfiguration
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber FrobeniusFiberClosure
  FrobeniusSpecialFiberTower FrobeniusSpecialFiberSPn FrobeniusExceptionalLocusCover

/-- Bundle: the exact component lists of the complete scheme-theoretic fibres. -/
theorem f29_special_fiber_components (k : Type u) [Field k] (p : ℕ) (a : k) (q : ℕ) :
    (exceptionalLocus p a (q + 1) =
      ⋃ idx : FinalIndex.{0} q, finalSupport (translatedInitial p a) q idx) ∧
    (specialFiberSupport p a (q + 1) =
      Set.range (fiberClosureInclusion (translatedInitial p a) (q + 1)).base ∪
        ⋃ idx : FinalIndex.{0} q, finalSupport (translatedInitial p a) q idx) :=
  ⟨exceptionalLocus_eq_iUnion p a q, specialFiberSupport_eq_components p a q⟩

/-- Bundle: the exact component lists on `S_{p,n}`. -/
theorem f29_special_fiber_components_sPn (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) :
    (∀ i : Fin n, clusterLocus q n a i = ⋃ idx : FinalIndex.{0} q, exceptionalSupport q n a i idx) ∧
    (∀ i : Fin n, specialFiberSSupport q n a i =
      Set.range (fiberStrictι (q + 1) n a i).base ∪
        ⋃ idx : FinalIndex.{0} q, exceptionalSupport q n a i idx) :=
  ⟨fun i => clusterLocus_eq_iUnion q n a i, fun i => specialFiberSSupport_eq_components q n a ha i⟩

/-- The bundles have exactly one universe parameter. -/
theorem f29_special_fiber_components_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) (b : k) (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k)
    (ha : Function.Injective a) : True := by
  have _ := f29_special_fiber_components.{u} k p b q
  have _ := f29_special_fiber_components_sPn.{u} k q n a ha
  trivial

end KltDP.Examples
