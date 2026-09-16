import KltDP.Examples.FrobeniusAdaptedFiberTransform
import KltDP.Examples.FrobeniusMultiCentreGraphNewest

/-!
# Contacts of the fibre strict transforms `F_i` on `S_{p,n}`

The fibre analogue of `FrobeniusMultiCentreGraphContacts` and `FrobeniusMultiCentreGraphNewest`:
the lift of the punctured horizontal fibre of `S_{p,n}` followed by the tower projection `τ_i` is the
whole-fibre lift on `T_i` (`fiberLift_towerProjection`); `τ_i` maps `F_i` into the generic strict
fibre `liftedFiberClosure A_i (q+1)` of `T_i`; hence `F_i ∩ C_{ij} = ∅` on `S_{p,n}`
(`fiberStrict_disjoint_exceptional_same`). Pulling the centre point of the strict fibre of `T_i`,
which lies on `P_i`, back through the isomorphism over the complement of the other centres gives
`F_i ∩ P_i ≠ ∅` on `S_{p,n}` (`fiberStrict_meets_newest`). No characteristic hypothesis is needed
for the fibres.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreFiberContacts

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure FrobeniusTranslatedCharts
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber
  FrobeniusGraphPicardClassZeroFiber FrobeniusFiberClosure FrobeniusAdaptedFiberTransform
  FrobeniusMultiCentreGraphContacts FrobeniusMultiCentreGraphNewest

variable {k : Type u} [Field k]

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The stage projection fixes the origin of the chart. -/
theorem stageProjection_originPoint (n : ℕ) :
    (stageProjection (k := k) n).base originPoint = originPoint := by
  have h := congrArg fieldMorphismPoint
    (FrobeniusStageComplement.originMorphism_stageProjection (k := k) n)
  rw [fieldMorphismPoint_comp, originMorphism_point] at h
  exact h

variable (q n : ℕ) (a : Fin n → k)

/-- The horizontal fibre at height `(a i)^p`, adapted to the `i`-th tower. -/
abbrev towerFiber (i : Fin n) : FiberAdapted (translatedInitial (q + 1) (a i)) :=
  fiberAdaptedTranslated (q + 1) (a i)

/-- The fibre minus all centres lies inside the fibre minus the `i`-th centre. -/
theorem fiberPuncture_le (i : Fin n) :
    fiberPuncture (q + 1) n a i ≤ (towerFiber q n a i).puncture := by
  intro x hx
  change (horizontalFiberMorphism (a i ^ (q + 1))).base x ≠
    (translatedInitial (q + 1) (a i)).chart.base (originPoint (k := k))
  rw [selected_center]
  exact (mem_centersComplement_iff (q + 1) n a
    ((horizontalFiberMorphism (a i ^ (q + 1))).base x)).mp hx i

/-- The inclusion of the two punctured fibres. -/
def fiberPunctureInclusion (i : Fin n) :
    (fiberPuncture (q + 1) n a i).toScheme ⟶ ((towerFiber q n a i).puncture).toScheme :=
  (projectiveSpace k 1).homOfLE (fiberPuncture_le q n a i)

@[reassoc] theorem fiberPunctureInclusion_ι (i : Fin n) :
    fiberPunctureInclusion q n a i ≫ ((towerFiber q n a i).puncture).ι =
      (fiberPuncture (q + 1) n a i).ι :=
  Scheme.homOfLE_ι _ _

/-- The `S_{p,n}`-lift of the punctured fibre followed by the tower projection is the tower's lift. -/
theorem fiberLift_towerProjection (i : Fin n) :
    fiberLift (q + 1) n a i ≫ towerProjection (q + 1) n a i =
      fiberPunctureInclusion q n a i ≫ (towerFiber q n a i).lift (q + 1) := by
  letI := toInitial_restrict_isIso (translatedInitial (q + 1) (a i)) (q + 1)
  have w : (fiberLift (q + 1) n a i ≫ towerProjection (q + 1) n a i) ≫
      selectedProjection (q + 1) (a i) (q + 1) =
        fiberPunctureInclusion q n a i ≫ (towerFiber q n a i).puncturedCurve := by
    rw [Category.assoc, towerProjection_projection, fiberLift_projection, puncturedFiber,
      FiberAdapted.puncturedCurve, ← Category.assoc, fiberPunctureInclusion_ι]
    rfl
  have w' : (fiberLift (q + 1) n a i ≫ towerProjection (q + 1) n a i) ≫
      (translatedInitial (q + 1) (a i)).toInitial (q + 1) =
        fiberPunctureInclusion q n a i ≫ (towerFiber q n a i).puncturedCurve := w
  exact liftOverIso_eq_of_projection ((translatedInitial (q + 1) (a i)).toInitial (q + 1))
    (initialPuncture (translatedInitial (q + 1) (a i))) (towerFiber q n a i).puncturedCurve
    (towerFiber q n a i).puncturedCurve_range _ _ w'

/-- The support of the generic strict fibre of `T_i` is the closure of its lifted punctured fibre. -/
theorem range_fiberClosureInclusion_eq_closure_lift (i : Fin n) :
    Set.range (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)).base =
      closure (Set.range ((towerFiber q n a i).lift (q + 1)).base) := by
  rw [← FiberAdapted.range_strictι, ← (towerFiber q n a i).strictIsoLocal_hom_ι (q + 1),
    range_iso_comp_base]

/-- The tower projection maps the support of `F_i` into the generic strict fibre of `T_i`. -/
theorem fiberStrict_projection_mem_towerStrict (i : Fin n) (x : multiSurface (q + 1) n a)
    (hx : x ∈ Set.range (fiberStrictι (q + 1) n a i).base) :
    (towerProjection (q + 1) n a i).base x ∈
      Set.range (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)).base := by
  rw [range_fiberStrictι] at hx
  have him : (towerProjection (q + 1) n a i).base '' Set.range (fiberLift (q + 1) n a i).base ⊆
      Set.range ((towerFiber q n a i).lift (q + 1)).base := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(fiberPunctureInclusion q n a i).base z, ?_⟩
    change (fiberPunctureInclusion q n a i ≫ (towerFiber q n a i).lift (q + 1)).base z =
      (fiberLift (q + 1) n a i ≫ towerProjection (q + 1) n a i).base z
    rw [fiberLift_towerProjection]
  have h1 : (towerProjection (q + 1) n a i).base x ∈
      closure (Set.range ((towerFiber q n a i).lift (q + 1)).base) :=
    closure_mono him
      (image_closure_subset_closure_image (towerProjection (q + 1) n a i).continuous ⟨x, hx, rfl⟩)
  rw [← range_fiberClosureInclusion_eq_closure_lift] at h1
  exact h1

/-- `F_i` is disjoint from every exceptional curve `C_{ij}` of its own tower in `S_{p,n}`. -/
theorem fiberStrict_disjoint_exceptional_same (i : Fin n) (j : Fin q) :
    Disjoint (Set.range (fiberStrictι (q + 1) n a i).base)
      (exceptionalSupport q n a i (Sum.inl j)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [exceptionalSupport_eq, Set.mem_preimage] at hx'
  exact Set.disjoint_left.mp
    (fiberClosure_disjoint_finalSupport (translatedInitial (q + 1) (a i)) q j)
    (fiberStrict_projection_mem_towerStrict q n a i x hx) hx'

/-! ## The centre point of the strict fibre of the `i`-th tower -/

/-- The centre point of the generic strict fibre of `T_i`, as a point of `T_i`. -/
def fiberPoint (i : Fin n) : selectedStage (q + 1) (a i) (q + 1) :=
  (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)).base
    (fiberContactPoint (translatedInitial (q + 1) (a i)) (q + 1))

theorem fiberPoint_mem_closure (i : Fin n) :
    fiberPoint q n a i ∈ closure (Set.range ((towerFiber q n a i).lift (q + 1)).base) := by
  rw [← range_fiberClosureInclusion_eq_closure_lift]
  exact ⟨_, rfl⟩

theorem fiberPoint_mem_newest (i : Fin n) :
    fiberPoint q n a i ∈
      finalSupport (translatedInitial (q + 1) (a i)) q (Sum.inr PUnit.unit : FinalIndex.{0} q) :=
  fiberClosure_terminal_mem_newestFiber (translatedInitial (q + 1) (a i)) q

/-- The centre point of the strict fibre lies over the selected centre. -/
theorem fiberPoint_projection (i : Fin n) :
    (selectedProjection (q + 1) (a i) (q + 1)).base (fiberPoint q n a i) =
      graphPoint (q + 1) (a i) := by
  change ((translatedInitial (q + 1) (a i)).toInitial (q + 1)).base (fiberPoint q n a i) = _
  rw [fiberPoint, fiberContactPoint_inclusion, ← Scheme.comp_base_apply,
    PlaneChartedScheme.stage_chart_toInitial, Scheme.comp_base_apply, stageProjection_originPoint,
    selected_center]

section Distinct

variable [IsAlgClosed k] (ha : Function.Injective a)
include ha

theorem fiberPoint_mem_isoOpen (i : Fin n) : fiberPoint q n a i ∈ isoOpen q n a i := by
  change (selectedProjection (q + 1) (a i) (q + 1)).base (fiberPoint q n a i) ∈
    otherComplement q n a i
  rw [fiberPoint_projection]
  exact center_mem_otherComplement q n a ha i

end Distinct

/-- Over the isomorphism open, the lifted punctured fibre of `T_i` comes from the lifted punctured
fibre of `S_{p,n}`. -/
theorem isoMap_preimage_fiberLift_subset (i : Fin n) :
    (isoMap q n a i).base ⁻¹' Set.range ((towerFiber q n a i).lift (q + 1)).base ⊆
      (isoPreimage q n a i).ι.base ⁻¹' Set.range (fiberLift (q + 1) n a i).base := by
  intro y hy
  obtain ⟨z, hz⟩ := hy
  have hgU : (isoMap q n a i).base y ∈ isoOpen q n a i := isoMap_mem q n a i y
  have hproj : (selectedProjection (q + 1) (a i) (q + 1)).base ((isoMap q n a i).base y) =
      (horizontalFiberMorphism (a i ^ (q + 1))).base z.1 := by
    rw [← hz, ← Scheme.comp_base_apply]
    change ((towerFiber q n a i).lift (q + 1) ≫
      (translatedInitial (q + 1) (a i)).toInitial (q + 1)).base z = _
    rw [FiberAdapted.lift_projection, FiberAdapted.puncturedCurve, Scheme.comp_base_apply,
      Scheme.Opens.ι_base_apply]
    rfl
  have hzC : (horizontalFiberMorphism (a i ^ (q + 1))).base z.1 ∈ centersComplement (q + 1) n a := by
    rw [mem_centersComplement_iff]
    intro j
    by_cases hj : j = i
    · rw [hj]
      have h2 : (horizontalFiberMorphism (a i ^ (q + 1))).base z.1 ≠
          (translatedInitial (q + 1) (a i)).chart.base (originPoint (k := k)) := z.2
      rwa [selected_center] at h2
    · have h3 : (selectedProjection (q + 1) (a i) (q + 1)).base ((isoMap q n a i).base y) ∈
          otherComplement q n a i := hgU
      rw [hproj] at h3
      exact (mem_otherComplement_iff q n a i _).mp h3 j hj
  let z' : (fiberPuncture (q + 1) n a i).toScheme := ⟨z.1, hzC⟩
  have hz' : (fiberPunctureInclusion q n a i).base z' = z :=
    Subtype.ext (Scheme.homOfLE_apply (fiberPuncture_le q n a i) z')
  have hτ : (towerProjection (q + 1) n a i).base ((fiberLift (q + 1) n a i).base z') =
      (isoMap q n a i).base y := by
    rw [← Scheme.comp_base_apply, fiberLift_towerProjection, Scheme.comp_base_apply, hz', hz]
  have hW : (fiberLift (q + 1) n a i).base z' ∈ isoPreimage q n a i := by
    change (towerProjection (q + 1) n a i).base ((fiberLift (q + 1) n a i).base z') ∈
      isoOpen q n a i
    rw [hτ]
    exact hgU
  have hinj : (⟨(fiberLift (q + 1) n a i).base z', hW⟩ : (isoPreimage q n a i).toScheme) = y := by
    apply (isoMap q n a i).isOpenEmbedding.injective
    rw [isoMap_base]
    exact hτ
  refine ⟨z', ?_⟩
  rw [Scheme.Opens.ι_base_apply, ← hinj]

section Meets

variable [IsAlgClosed k] (ha : Function.Injective a)
include ha

/-- `F_i` meets the newest exceptional curve `P_i` of its own tower in `S_{p,n}`. -/
theorem fiberStrict_meets_newest (i : Fin n) :
    (Set.range (fiberStrictι (q + 1) n a i).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit)).Nonempty := by
  obtain ⟨c, hc⟩ : ∃ c : (isoOpen q n a i).toScheme, c.1 = fiberPoint q n a i :=
    ⟨⟨fiberPoint q n a i, fiberPoint_mem_isoOpen q n a ha i⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : (isoPreimage q n a i).toScheme,
      (isoMap q n a i).base y = fiberPoint q n a i := by
    refine ⟨(inv (towerProjection (q + 1) n a i ∣_ isoOpen q n a i)).base c, ?_⟩
    rw [isoMap, ← Scheme.comp_base_apply, IsIso.inv_hom_id_assoc, Scheme.Opens.ι_base_apply]
    exact hc
  have hyC : y ∈ (isoMap q n a i).base ⁻¹'
      closure (Set.range ((towerFiber q n a i).lift (q + 1)).base) := by
    rw [Set.mem_preimage, hy]
    exact fiberPoint_mem_closure q n a i
  rw [(isoMap q n a i).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    (isoMap q n a i).continuous] at hyC
  have hyW : y ∈
      closure ((isoPreimage q n a i).ι.base ⁻¹' Set.range (fiberLift (q + 1) n a i).base) :=
    closure_mono (isoMap_preimage_fiberLift_subset q n a i) hyC
  have hx : (isoPreimage q n a i).ι.base y ∈ closure (Set.range (fiberLift (q + 1) n a i).base) :=
    (isoPreimage q n a i).ι.continuous.closure_preimage_subset _ hyW
  refine ⟨(isoPreimage q n a i).ι.base y, ?_, ?_⟩
  · rw [range_fiberStrictι]
    exact hx
  · rw [exceptionalSupport_eq, Set.mem_preimage]
    have hτ : (towerProjection (q + 1) n a i).base ((isoPreimage q n a i).ι.base y) =
        fiberPoint q n a i := by
      rw [← hy, isoMap_base, Scheme.Opens.ι_base_apply]
    rw [hτ]
    exact fiberPoint_mem_newest q n a i

end Meets

end KltDP.Examples.FrobeniusMultiCentreFiberContacts
