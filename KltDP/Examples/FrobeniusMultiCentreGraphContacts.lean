import KltDP.Examples.FrobeniusAdaptedStrictTransform
import KltDP.Examples.FrobeniusMultiCentreGraphFiber

/-!
# Contacts of the graph strict transform `B` on `S_{p,n}`, via the towers

On `S_{p,n} = multiSurface (q+1) n a`, the lift of the whole graph minus all centres
(`graphLift`) followed by the projection to the `i`-th tower `T_i` is the lift of the graph minus the
`i`-th centre on `T_i` (the generic adapted-curve lift of `FrobeniusAdaptedStrictTransform`),
restricted along the inclusion of punctures (`graphLift_towerProjection`), by uniqueness of lifts
over the complement isomorphism.

Consequently the tower projection maps the support of `B` into the support of the whole-graph strict
transform of `T_i`, which is the accepted generic local closure `liftedGraphClosure A_i (q+1) 0`.
Since that closure misses every exceptional component of `T_i` created before the last blowup
(`FrobeniusClosureContact.closure_disjoint_finalSupport`), `B` is disjoint from every `C_{ij}` in
`S_{p,n}` (`graphStrict_disjoint_exceptional_same`); this is the first incidence of Proposition 10.1
established on `S_{p,n}` itself.

Not proved here: `B ∩ P_i ≠ ∅` on `S_{p,n}` (the converse closure direction through the
isomorphism open) and the fibre analogues; see `F29_CONTACTS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGraphContacts

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure FrobeniusTranslatedCharts
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber
  FrobeniusAdaptedStrictTransform FrobeniusClosureContact

variable {k : Type u} [Field k]

/-- The range of a composite with an isomorphism is the range of the second map. -/
theorem range_iso_comp_base {X Y Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z) :
    Set.range (e.hom ≫ f).base = Set.range f.base := by
  have hsurj : Function.Surjective e.hom.base := fun y =>
    ⟨e.inv.base y, by
      change (e.inv ≫ e.hom).base y = y
      rw [e.inv_hom_id]
      rfl⟩
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨e.hom.base w, rfl⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := hsurj w
    refine ⟨v, ?_⟩
    change f.base (e.hom.base v) = f.base w
    rw [hv]

variable (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k)

/-- The graph, adapted to the `i`-th tower. -/
abbrev towerGraph (i : Fin n) : CurveAdapted (translatedInitial (q + 1) (a i)) (q + 1) :=
  graphAdaptedTranslated (q + 1) (a i)

/-- The graph minus all centres lies inside the graph minus the `i`-th centre. -/
theorem graphPuncture_le (i : Fin n) : graphPuncture (q + 1) n a ≤ (towerGraph q n a i).puncture := by
  intro x hx
  change (graphι (q + 1)).base x ≠ (translatedInitial (q + 1) (a i)).chart.base (originPoint (k := k))
  rw [selected_center]
  exact (mem_centersComplement_iff (q + 1) n a ((graphι (q + 1)).base x)).mp hx i

/-- The inclusion of the two punctured graphs. -/
def punctureInclusion (i : Fin n) :
    (graphPuncture (q + 1) n a).toScheme ⟶ ((towerGraph q n a i).puncture).toScheme :=
  (graph (q + 1)).homOfLE (graphPuncture_le q n a i)

@[reassoc] theorem punctureInclusion_ι (i : Fin n) :
    punctureInclusion q n a i ≫ ((towerGraph q n a i).puncture).ι = (graphPuncture (q + 1) n a).ι :=
  Scheme.homOfLE_ι _ _

/-- The `S_{p,n}`-lift of the punctured graph followed by the tower projection is the tower's lift. -/
theorem graphLift_towerProjection (i : Fin n) :
    graphLift (q + 1) n a ≫ towerProjection (q + 1) n a i =
      punctureInclusion q n a i ≫ (towerGraph q n a i).lift (q + 1) := by
  letI := toInitial_restrict_isIso (translatedInitial (q + 1) (a i)) (q + 1)
  have w : (graphLift (q + 1) n a ≫ towerProjection (q + 1) n a i) ≫
      selectedProjection (q + 1) (a i) (q + 1) =
        punctureInclusion q n a i ≫ (towerGraph q n a i).puncturedCurve := by
    rw [Category.assoc, towerProjection_projection, graphLift_projection, puncturedGraph,
      CurveAdapted.puncturedCurve, ← Category.assoc, punctureInclusion_ι]
    rfl
  have w' : (graphLift (q + 1) n a ≫ towerProjection (q + 1) n a i) ≫
      (translatedInitial (q + 1) (a i)).toInitial (q + 1) =
        punctureInclusion q n a i ≫ (towerGraph q n a i).puncturedCurve := w
  exact liftOverIso_eq_of_projection ((translatedInitial (q + 1) (a i)).toInitial (q + 1))
    (initialPuncture (translatedInitial (q + 1) (a i))) (towerGraph q n a i).puncturedCurve
    (towerGraph q n a i).puncturedCurve_range _ _ w'

/-- The tower projection maps the support of `B` into the support of the tower's strict transform. -/
theorem graphStrict_projection_mem_towerStrict (i : Fin n) (x : multiSurface (q + 1) n a)
    (hx : x ∈ Set.range (graphStrictι (q + 1) n a).base) :
    (towerProjection (q + 1) n a i).base x ∈
      Set.range (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0).base := by
  rw [range_graphStrictι] at hx
  have him : (towerProjection (q + 1) n a i).base '' Set.range (graphLift (q + 1) n a).base ⊆
      Set.range ((towerGraph q n a i).lift (q + 1)).base := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(punctureInclusion q n a i).base z, ?_⟩
    change (punctureInclusion q n a i ≫ (towerGraph q n a i).lift (q + 1)).base z =
      (graphLift (q + 1) n a ≫ towerProjection (q + 1) n a i).base z
    rw [graphLift_towerProjection]
  have h1 : (towerProjection (q + 1) n a i).base x ∈
      closure (Set.range ((towerGraph q n a i).lift (q + 1)).base) :=
    closure_mono him
      (image_closure_subset_closure_image (towerProjection (q + 1) n a i).continuous ⟨x, hx, rfl⟩)
  rw [← CurveAdapted.range_strictι,
    ← (towerGraph q n a i).strictIsoLocal_hom_ι (q + 1) 0 (by omega), range_iso_comp_base] at h1
  exact h1

/-- `B` is disjoint from every exceptional curve `C_{ij}` of every tower in `S_{p,n}`. -/
theorem graphStrict_disjoint_exceptional_same (i : Fin n) (j : Fin q) :
    Disjoint (Set.range (graphStrictι (q + 1) n a).base)
      (exceptionalSupport q n a i (Sum.inl j)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [exceptionalSupport_eq, Set.mem_preimage] at hx'
  exact Set.disjoint_left.mp
    (closure_disjoint_finalSupport (translatedInitial (q + 1) (a i)) q 0 j)
    (graphStrict_projection_mem_towerStrict q n a i x hx) hx'

end KltDP.Examples.FrobeniusMultiCentreGraphContacts
