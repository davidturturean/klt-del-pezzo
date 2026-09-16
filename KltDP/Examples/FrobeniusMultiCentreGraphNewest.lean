import KltDP.Examples.FrobeniusMultiCentreGraphContacts
import KltDP.Examples.FrobeniusFiberClosure

/-!
# `B` meets every newest exceptional curve `P_i` on `S_{p,n}`

The tower projection `τ_i : S_{p,n} ⟶ T_i` is an isomorphism over the open `U_i ⊆ T_i` lying over
the complement of the other centres (`towerProjection_restrict_isIso`). The whole-graph strict
transform of `T_i` is the accepted local closure `liftedGraphClosure A_i (q+1) 0`, whose terminal
contact point `c_i` lies on the newest fibre `P_i` of `T_i` (`closure_terminal_mem_newestFiber`) and
over the centre `(a_i, a_i^p)`, hence in `U_i` when the centres are distinct.

Pulling `c_i` back through the isomorphism gives a point `x_i ∈ S_{p,n}` over `c_i`. The lifted
punctured graph of `S_{p,n}` restricted to `τ_i^{-1} U_i` is exactly the preimage of the lifted
punctured graph of `T_i` (`isoMap_preimage_lift_subset`); since the restricted `τ_i` is an open map,
closures correspond and `x_i` lies in the support of `B` (`graphStrict_meets_newest`).

This is the incidence `B ∩ P_i ≠ ∅` of Proposition 10.1 on `S_{p,n}` itself. The stronger
single-point (transversal) statement is not proved here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGraphNewest

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure FrobeniusTranslatedCharts
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber
  FrobeniusAdaptedStrictTransform FrobeniusClosureContact FrobeniusMultiCentreGraphContacts
  FrobeniusBlowupIncidence FrobeniusFiberClosure

variable {k : Type u} [Field k]

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The origin of the monomial curve is the origin of the plane (positive exponent). -/
theorem curveInPlane_curvePoint (m : ℕ) (hm : 0 < m) :
    (curveInPlane (k := k) m).base curvePoint = originPoint := by
  have h := congrArg fieldMorphismPoint (parameterOrigin_curveInPlane (k := k) m hm)
  have hp : fieldMorphismPoint (parameterOriginMorphism (k := k)) = curvePoint :=
    FrobeniusGraphStalkContact.polynomialEvaluation_point 0
  rw [fieldMorphismPoint_comp, originMorphism_point, hp] at h
  exact h

variable (q n : ℕ) (a : Fin n → k)

/-! ## The isomorphism open of the `i`-th tower -/

/-- The open of `T_i` over the complement of the other centres. -/
def isoOpen (i : Fin n) : (selectedStage (q + 1) (a i) (q + 1)).Opens :=
  selectedProjection (q + 1) (a i) (q + 1) ⁻¹ᵁ otherComplement q n a i

instance isoOpen_restrict_isIso (i : Fin n) :
    IsIso (towerProjection (q + 1) n a i ∣_ isoOpen q n a i) :=
  towerProjection_restrict_isIso q n a i (otherComplement q n a i)
    (fun j hj => center_not_mem_otherComplement q n a i j hj)

/-- Its preimage in `S_{p,n}`. -/
abbrev isoPreimage (i : Fin n) : (multiSurface (q + 1) n a).Opens :=
  towerProjection (q + 1) n a i ⁻¹ᵁ isoOpen q n a i

/-- The restricted tower projection, as a morphism into `T_i`. -/
def isoMap (i : Fin n) : (isoPreimage q n a i).toScheme ⟶ selectedStage (q + 1) (a i) (q + 1) :=
  (towerProjection (q + 1) n a i ∣_ isoOpen q n a i) ≫ (isoOpen q n a i).ι

instance isoMap_isOpenImmersion (i : Fin n) : IsOpenImmersion (isoMap q n a i) := by
  unfold isoMap
  infer_instance

theorem isoMap_eq (i : Fin n) :
    isoMap q n a i = (isoPreimage q n a i).ι ≫ towerProjection (q + 1) n a i :=
  morphismRestrict_ι _ _

theorem isoMap_base (i : Fin n) (y : (isoPreimage q n a i).toScheme) :
    (isoMap q n a i).base y = (towerProjection (q + 1) n a i).base y.1 := by
  rw [isoMap_eq, Scheme.comp_base_apply, Scheme.Opens.ι_base_apply]

theorem isoMap_mem (i : Fin n) (y : (isoPreimage q n a i).toScheme) :
    (isoMap q n a i).base y ∈ isoOpen q n a i := by
  have h : (isoMap q n a i).base y ∈ Set.range (isoOpen q n a i).ι.base :=
    ⟨(towerProjection (q + 1) n a i ∣_ isoOpen q n a i).base y,
      (Scheme.comp_base_apply _ _ y).symm⟩
  rwa [Scheme.Opens.range_ι] at h

/-! ## The terminal contact point of the `i`-th tower -/

/-- The terminal contact point of the local closure of `T_i`, as a point of `T_i`. -/
def contactPoint (i : Fin n) : selectedStage (q + 1) (a i) (q + 1) :=
  (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0).base
    (closureContactPoint (translatedInitial (q + 1) (a i)) (q + 1) 0)

theorem contactPoint_mem_newest (i : Fin n) :
    contactPoint q n a i ∈
      finalSupport (translatedInitial (q + 1) (a i)) q (Sum.inr PUnit.unit : FinalIndex.{0} q) :=
  closure_terminal_mem_newestFiber (translatedInitial (q + 1) (a i)) q

/-- The terminal contact point lies over the selected centre. -/
theorem contactPoint_projection (i : Fin n) :
    (selectedProjection (q + 1) (a i) (q + 1)).base (contactPoint q n a i) =
      graphPoint (q + 1) (a i) := by
  change ((translatedInitial (q + 1) (a i)).toInitial (q + 1)).base
    ((closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0).base
      ((residualToClosure (translatedInitial (q + 1) (a i)) (q + 1) 0).base curvePoint)) = _
  rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, residualToClosure_inclusion_assoc,
    PlaneChartedScheme.residualCurve_toInitial, Scheme.comp_base_apply,
    curveInPlane_curvePoint (0 + (q + 1)) (by omega), selected_center]

section Distinct

variable [IsAlgClosed k] (ha : Function.Injective a)
include ha

theorem contactPoint_mem_isoOpen (i : Fin n) : contactPoint q n a i ∈ isoOpen q n a i := by
  change (selectedProjection (q + 1) (a i) (q + 1)).base (contactPoint q n a i) ∈
    otherComplement q n a i
  rw [contactPoint_projection]
  exact center_mem_otherComplement q n a ha i

end Distinct

/-! ## The graph on the towers -/

variable [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- The support of the local closure of the `i`-th tower is the closure of the lifted punctured
graph of that tower. -/
theorem range_closureInclusion_eq_closure_lift (i : Fin n) :
    Set.range (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0).base =
      closure (Set.range ((towerGraph q n a i).lift (q + 1)).base) := by
  rw [← CurveAdapted.range_strictι,
    ← (towerGraph q n a i).strictIsoLocal_hom_ι (q + 1) 0 (by omega), range_iso_comp_base]

/-- Over the isomorphism open, the lifted punctured graph of `T_i` comes from the lifted punctured
graph of `S_{p,n}`. -/
theorem isoMap_preimage_lift_subset (i : Fin n) :
    (isoMap q n a i).base ⁻¹' Set.range ((towerGraph q n a i).lift (q + 1)).base ⊆
      (isoPreimage q n a i).ι.base ⁻¹' Set.range (graphLift (q + 1) n a).base := by
  intro y hy
  obtain ⟨z, hz⟩ := hy
  have hgU : (isoMap q n a i).base y ∈ isoOpen q n a i := isoMap_mem q n a i y
  have hproj : (selectedProjection (q + 1) (a i) (q + 1)).base ((isoMap q n a i).base y) =
      (graphι (q + 1)).base z.1 := by
    rw [← hz, ← Scheme.comp_base_apply]
    change ((towerGraph q n a i).lift (q + 1) ≫
      (translatedInitial (q + 1) (a i)).toInitial (q + 1)).base z = _
    rw [CurveAdapted.lift_projection, CurveAdapted.puncturedCurve, Scheme.comp_base_apply,
      Scheme.Opens.ι_base_apply]
    rfl
  have hzC : (graphι (q + 1)).base z.1 ∈ centersComplement (q + 1) n a := by
    rw [mem_centersComplement_iff]
    intro j
    by_cases hj : j = i
    · rw [hj]
      have h2 : (graphι (q + 1)).base z.1 ≠
          (translatedInitial (q + 1) (a i)).chart.base (originPoint (k := k)) := z.2
      rwa [selected_center] at h2
    · have h3 : (selectedProjection (q + 1) (a i) (q + 1)).base ((isoMap q n a i).base y) ∈
          otherComplement q n a i := hgU
      rw [hproj] at h3
      exact (mem_otherComplement_iff q n a i _).mp h3 j hj
  let z' : (graphPuncture (q + 1) n a).toScheme := ⟨z.1, hzC⟩
  have hz' : (punctureInclusion q n a i).base z' = z :=
    Subtype.ext (Scheme.homOfLE_apply (graphPuncture_le q n a i) z')
  have hτ : (towerProjection (q + 1) n a i).base ((graphLift (q + 1) n a).base z') =
      (isoMap q n a i).base y := by
    rw [← Scheme.comp_base_apply, graphLift_towerProjection, Scheme.comp_base_apply, hz', hz]
  have hW : (graphLift (q + 1) n a).base z' ∈ isoPreimage q n a i := by
    change (towerProjection (q + 1) n a i).base ((graphLift (q + 1) n a).base z') ∈ isoOpen q n a i
    rw [hτ]
    exact hgU
  have hinj : (⟨(graphLift (q + 1) n a).base z', hW⟩ : (isoPreimage q n a i).toScheme) = y := by
    apply (isoMap q n a i).isOpenEmbedding.injective
    rw [isoMap_base]
    exact hτ
  refine ⟨z', ?_⟩
  rw [Scheme.Opens.ι_base_apply, ← hinj]

theorem contactPoint_mem_closure (i : Fin n) :
    contactPoint q n a i ∈ closure (Set.range ((towerGraph q n a i).lift (q + 1)).base) := by
  rw [← range_closureInclusion_eq_closure_lift]
  exact ⟨_, rfl⟩

section Meets

variable [IsAlgClosed k] (ha : Function.Injective a)
include ha

/-- `B` meets every newest exceptional curve `P_i` of `S_{p,n}`. -/
theorem graphStrict_meets_newest (i : Fin n) :
    (Set.range (graphStrictι (q + 1) n a).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit)).Nonempty := by
  obtain ⟨c, hc⟩ : ∃ c : (isoOpen q n a i).toScheme, c.1 = contactPoint q n a i :=
    ⟨⟨contactPoint q n a i, contactPoint_mem_isoOpen q n a ha i⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : (isoPreimage q n a i).toScheme,
      (isoMap q n a i).base y = contactPoint q n a i := by
    refine ⟨(inv (towerProjection (q + 1) n a i ∣_ isoOpen q n a i)).base c, ?_⟩
    rw [isoMap, ← Scheme.comp_base_apply, IsIso.inv_hom_id_assoc, Scheme.Opens.ι_base_apply]
    exact hc
  have hyC : y ∈ (isoMap q n a i).base ⁻¹'
      closure (Set.range ((towerGraph q n a i).lift (q + 1)).base) := by
    rw [Set.mem_preimage, hy]
    exact contactPoint_mem_closure q n a i
  rw [(isoMap q n a i).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    (isoMap q n a i).continuous] at hyC
  have hyW : y ∈ closure ((isoPreimage q n a i).ι.base ⁻¹' Set.range (graphLift (q + 1) n a).base) :=
    closure_mono (isoMap_preimage_lift_subset q n a i) hyC
  have hx : (isoPreimage q n a i).ι.base y ∈ closure (Set.range (graphLift (q + 1) n a).base) :=
    (isoPreimage q n a i).ι.continuous.closure_preimage_subset _ hyW
  refine ⟨(isoPreimage q n a i).ι.base y, ?_, ?_⟩
  · rw [range_graphStrictι]
    exact hx
  · rw [exceptionalSupport_eq, Set.mem_preimage]
    have hτ : (towerProjection (q + 1) n a i).base ((isoPreimage q n a i).ι.base y) =
        contactPoint q n a i := by
      rw [← hy, isoMap_base, Scheme.Opens.ι_base_apply]
    rw [hτ]
    exact contactPoint_mem_newest q n a i

end Meets

end KltDP.Examples.FrobeniusMultiCentreGraphNewest
