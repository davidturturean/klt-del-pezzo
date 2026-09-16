import KltDP.Examples.FrobeniusClosureNewestUnique
import KltDP.Examples.FrobeniusMultiCentreFiberContacts

/-!
# Single-point contacts on `S_{p,n}`

The strict graph `B` and the strict fibre `F_i` of `S_{p,n}` meet the newest exceptional curve `P_i`
of the `i`-th tower in exactly one point each. Existence is `graphStrict_meets_newest`,
`fiberStrict_meets_newest` (BRIEF6). Uniqueness: `P_i` lies in the isomorphism open of the `i`-th tower
(`newest_mem_isoPreimage`), where the tower projection `τ_i` is injective (`towerProjection_injOn`),
and `τ_i` maps `B` into the local closure and `F_i` into the strict fibre of the tower `T_i`, which meet
the newest fibre only in their contact points (`closure_newest_unique`, `fiberClosure_newest_unique`).

For `B ∩ F_i`: every common point maps into the stage puncture of `T_i`, i.e. `B ∩ F_i` has no point over
the affine chart of the `i`-th translated plane (`graphStrict_fiberStrict_disjoint_initialPlane`,
`graphStrict_fiberStrict_projection_mem_stagePuncture`); the remaining points would lie over the boundary
of that chart, where the graph and the fibre `y = a_i^p` do not meet — this last fact about `P¹ ×_k P¹` is
not proved here, so `B ∩ F_i = ∅` is not claimed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusIncidenceSPn

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure FrobeniusStrictTransformStageCover
  FrobeniusTranslatedCharts FrobeniusStageComplement.PlaneChartedScheme
  FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber
  FrobeniusAdaptedStrictTransform FrobeniusClosureContact FrobeniusFiberClosure
  FrobeniusMultiCentreGraphContacts FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreFiberContacts FrobeniusClosureNewestUnique

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-- The tower projection is injective on the isomorphism open. -/
theorem towerProjection_injOn (i : Fin n) {x x' : multiSurface (q + 1) n a}
    (hx : x ∈ isoPreimage q n a i) (hx' : x' ∈ isoPreimage q n a i)
    (h : (towerProjection (q + 1) n a i).base x = (towerProjection (q + 1) n a i).base x') :
    x = x' := by
  have hinj := (isoMap q n a i).isOpenEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨x', hx'⟩)
    (by rw [isoMap_base, isoMap_base]; exact h)
  exact congrArg Subtype.val hinj

section Graph

variable [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- Every common point of `B` and `F_i` maps into the stage puncture of `T_i`. -/
theorem graphStrict_fiberStrict_projection_mem_stagePuncture (i : Fin n)
    (x : multiSurface (q + 1) n a) (hB : x ∈ Set.range (graphStrictι (q + 1) n a).base)
    (hF : x ∈ Set.range (fiberStrictι (q + 1) n a i).base) :
    (towerProjection (q + 1) n a i).base x ∈
      stagePuncture (translatedInitial (q + 1) (a i)) (q + 1) :=
  closure_fiberClosure_mem_stagePuncture (translatedInitial (q + 1) (a i)) (q + 1) _
    (graphStrict_projection_mem_towerStrict q n a i x hB)
    (fiberStrict_projection_mem_towerStrict q n a i x hF)

/-- `B ∩ F_i` has no point over the affine chart of the `i`-th translated plane. -/
theorem graphStrict_fiberStrict_disjoint_initialPlane (i : Fin n) (x : multiSurface (q + 1) n a)
    (hB : x ∈ Set.range (graphStrictι (q + 1) n a).base)
    (hF : x ∈ Set.range (fiberStrictι (q + 1) n a i).base)
    (hplane : (towerProjection (q + 1) n a i).base x ∈
      initialPlaneOpen (translatedInitial (q + 1) (a i)) (q + 1)) : False :=
  closure_fiberClosure_disjoint_initialPlane (translatedInitial (q + 1) (a i)) (q + 1) _
    (graphStrict_projection_mem_towerStrict q n a i x hB)
    (fiberStrict_projection_mem_towerStrict q n a i x hF) hplane

/-- `B ∩ F_i` has no point over the translated affine chart around the `i`-th centre. -/
theorem graphStrict_fiberStrict_projection_not_mem_chart (i : Fin n) (x : multiSurface (q + 1) n a)
    (hB : x ∈ Set.range (graphStrictι (q + 1) n a).base)
    (hF : x ∈ Set.range (fiberStrictι (q + 1) n a i).base) :
    (multiProjection (q + 1) n a).base x ∉ (translatedPlaneChart (q + 1) (a i)).opensRange := by
  intro hmem
  apply graphStrict_fiberStrict_disjoint_initialPlane q n a i x hB hF
  change (selectedProjection (q + 1) (a i) (q + 1)).base ((towerProjection (q + 1) n a i).base x) ∈
    (translatedPlaneChart (q + 1) (a i)).opensRange
  rw [← Scheme.comp_base_apply, towerProjection_projection (q + 1) n a i]
  exact hmem

end Graph

section Distinct

variable [IsAlgClosed k] (ha : Function.Injective a)
include ha

/-- Every point of `P_i` lies in the isomorphism open of the `i`-th tower. -/
theorem newest_mem_isoPreimage (i : Fin n) (x : multiSurface (q + 1) n a)
    (hx : x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit)) : x ∈ isoPreimage q n a i := by
  rw [exceptionalSupport_eq] at hx
  obtain ⟨z, hz⟩ := hx
  change (towerProjection (q + 1) n a i).base x ∈ isoOpen q n a i
  rw [← hz]
  exact finalComponent_mem_otherComplement q n a ha i _ z

/-- `F_i ∩ P_i` has at most one point. -/
theorem fiberStrict_inter_newest_subsingleton (i : Fin n) :
    (Set.range (fiberStrictι (q + 1) n a i).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit)).Subsingleton := by
  intro x hx x' hx'
  have key : ∀ y ∈ Set.range (fiberStrictι (q + 1) n a i).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit),
      (towerProjection (q + 1) n a i).base y = fiberPoint q n a i := by
    intro y hy
    apply fiberClosure_newest_unique (translatedInitial (q + 1) (a i)) q
    · exact fiberStrict_projection_mem_towerStrict q n a i y hy.1
    · have h := hy.2
      rw [exceptionalSupport_eq] at h
      exact h
  exact towerProjection_injOn q n a i (newest_mem_isoPreimage q n a ha i x hx.2)
    (newest_mem_isoPreimage q n a ha i x' hx'.2) ((key x hx).trans (key x' hx').symm)

/-- **`F_i ∩ P_i` is exactly one point.** -/
theorem fiberStrict_inter_newest_eq_singleton (i : Fin n) :
    ∃ x, Set.range (fiberStrictι (q + 1) n a i).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit) = {x} :=
  Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr
    ⟨fiberStrict_meets_newest q n a ha i, fiberStrict_inter_newest_subsingleton q n a ha i⟩

variable [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- `B ∩ P_i` has at most one point. -/
theorem graphStrict_inter_newest_subsingleton (i : Fin n) :
    (Set.range (graphStrictι (q + 1) n a).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit)).Subsingleton := by
  intro x hx x' hx'
  have key : ∀ y ∈ Set.range (graphStrictι (q + 1) n a).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit),
      (towerProjection (q + 1) n a i).base y = contactPoint q n a i := by
    intro y hy
    apply closure_newest_unique (translatedInitial (q + 1) (a i)) q
    · exact graphStrict_projection_mem_towerStrict q n a i y hy.1
    · have h := hy.2
      rw [exceptionalSupport_eq] at h
      exact h
  exact towerProjection_injOn q n a i (newest_mem_isoPreimage q n a ha i x hx.2)
    (newest_mem_isoPreimage q n a ha i x' hx'.2) ((key x hx).trans (key x' hx').symm)

/-- **`B ∩ P_i` is exactly one point.** -/
theorem graphStrict_inter_newest_eq_singleton (i : Fin n) :
    ∃ x, Set.range (graphStrictι (q + 1) n a).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit) = {x} :=
  Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr
    ⟨graphStrict_meets_newest q n a ha i, graphStrict_inter_newest_subsingleton q n a ha i⟩

end Distinct

end KltDP.Examples.FrobeniusIncidenceSPn

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusTranslatedCharts
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber FrobeniusIncidenceSPn

/-- Bundle: the single-point contacts of Proposition 10.1 on `S_{p,n}`: `B ∩ P_i` and `F_i ∩ P_i` are
single points, no common point of `B` and `F_i` lies over the translated affine chart around the `i`-th
centre (every such point lies over the puncture of the `i`-th tower), and `P_i ≅ P¹`. -/
theorem sPn_single_point_contacts (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) :
    (∀ i : Fin n, ∃ x, Set.range (graphStrictι (q + 1) n a).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit) = {x}) ∧
    (∀ i : Fin n, ∃ x, Set.range (fiberStrictι (q + 1) n a i).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit) = {x}) ∧
    (∀ (i : Fin n) (x : multiSurface (q + 1) n a), x ∈ Set.range (graphStrictι (q + 1) n a).base →
      x ∈ Set.range (fiberStrictι (q + 1) n a i).base →
      (multiProjection (q + 1) n a).base x ∉ (translatedPlaneChart (q + 1) (a i)).opensRange) ∧
    (∀ (i : Fin n) (x : multiSurface (q + 1) n a), x ∈ Set.range (graphStrictι (q + 1) n a).base →
      x ∈ Set.range (fiberStrictι (q + 1) n a i).base →
      (towerProjection (q + 1) n a i).base x ∈
        stagePuncture (translatedInitial (q + 1) (a i)) (q + 1)) ∧
    (∀ i : Fin n, Nonempty (exceptionalCurve q n a i (Sum.inr PUnit.unit) ≅ projectiveSpace k 1)) :=
  ⟨fun i => graphStrict_inter_newest_eq_singleton q n a ha i,
    fun i => fiberStrict_inter_newest_eq_singleton q n a ha i,
    fun i x hB hF => graphStrict_fiberStrict_projection_not_mem_chart q n a i x hB hF,
    fun i x hB hF => graphStrict_fiberStrict_projection_mem_stagePuncture q n a i x hB hF,
    fun i => ⟨newestCurveIso q n a ha i⟩⟩

/-- The bundle has exactly one universe parameter. -/
theorem sPn_single_point_contacts_universe_check (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) : True := by
  have _ := sPn_single_point_contacts.{u} k q n a ha
  trivial

end KltDP.Examples
