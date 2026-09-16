import KltDP.Examples.FrobeniusAdaptedFiberTransform
import KltDP.Examples.FrobeniusMultiCentreGraphContacts

/-!
# The complete scheme-theoretic fibre of a contact tower

On the tower `T = selectedStage p a n` at the selected point `(a, a^p)`, the complete scheme-theoretic
fibre of the `b`-ruling over `a^p` is the literal pullback of the horizontal fibre
`horizontalFiberMorphism (a^p) : P¹ ⟶ P¹ ×_k P¹` along the tower projection
(`specialFiber p a n`), a closed subscheme of `T` (`specialFiberι`).

Its support is the union of the support of the strict fibre `liftedFiberClosure A n` and the
exceptional locus (the fibre of the tower over the centre) — `specialFiberSupport_eq_union` — and every
final exceptional component `C_j`, `P` lies in the exceptional locus
(`finalSupport_subset_exceptionalLocus`). This is the set-theoretic content of the divisor identity
`F + Σ_j j·C_j + p·P`; the multiplicities are established in the accepted plane charts in
`FrobeniusSpecialFiberCharts`. Only `[Field k]` is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusSpecialFiberTower

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure FrobeniusTranslatedCharts
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreExceptional
  FrobeniusGraphPicardClassZeroFiber FrobeniusBlowupIncidence FrobeniusFiberClosure
  FrobeniusFiberTranslation FrobeniusAdaptedFiberTransform FrobeniusMultiCentreGraphContacts
  FrobeniusUnaffectedFibers

variable {k : Type u} [Field k]

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## Injectivity of the tower projection over the puncture -/

section Puncture

variable (A : PlaneChartedScheme k)

/-- The tower projection restricted to the stage puncture, as a morphism into the initial scheme. -/
def punctureMap (n : ℕ) : (stagePuncture A n).toScheme ⟶ A.carrier :=
  (A.toInitial n ∣_ initialPuncture A) ≫ (initialPuncture A).ι

instance punctureMap_isOpenImmersion (n : ℕ) : IsOpenImmersion (punctureMap A n) := by
  letI := toInitial_restrict_isIso A n
  unfold punctureMap
  infer_instance

theorem punctureMap_base (n : ℕ) (y : (stagePuncture A n).toScheme) :
    (punctureMap A n).base y = (A.toInitial n).base ((stagePuncture A n).ι.base y) := by
  rw [punctureMap, morphismRestrict_ι, Scheme.comp_base_apply]
  rfl

/-- The tower projection is injective on the stage puncture. -/
theorem toInitial_injective_on_puncture (n : ℕ) {x y : (A.stage n).carrier}
    (hx : x ∈ stagePuncture A n) (hy : y ∈ stagePuncture A n)
    (h : (A.toInitial n).base x = (A.toInitial n).base y) : x = y := by
  have h' : (⟨x, hx⟩ : (stagePuncture A n).toScheme) = ⟨y, hy⟩ := by
    apply (punctureMap A n).isOpenEmbedding.injective
    rw [punctureMap_base, punctureMap_base]
    exact h
  exact congrArg Subtype.val h'

/-- The origin of the fibre line is the origin of the plane. -/
theorem fiberCurve_curvePoint : (fiberCurve (k := k)).base curvePoint = originPoint := by
  have h := congrArg fieldMorphismPoint (parameterOrigin_fiberCurve (k := k))
  have hp : fieldMorphismPoint (parameterOriginMorphism (k := k)) = curvePoint :=
    FrobeniusGraphStalkContact.polynomialEvaluation_point 0
  rw [fieldMorphismPoint_comp, originMorphism_point, hp] at h
  exact h

end Puncture

/-! ## The special fibre of the translated tower -/

variable (p : ℕ) (a : k) (n : ℕ)

/-- The complete scheme-theoretic fibre of the tower over the `b`-ruling point `y = a^p`. -/
def specialFiber : Scheme.{u} :=
  pullback (selectedProjection p a n) (horizontalFiberMorphism (a ^ p))

/-- Its closed immersion into the tower. -/
def specialFiberι : specialFiber p a n ⟶ selectedStage p a n := pullback.fst _ _

/-- Its projection to the fibre `P¹`. -/
def specialFiberToLine : specialFiber p a n ⟶ projectiveSpace k 1 := pullback.snd _ _

instance specialFiberι_isClosedImmersion : IsClosedImmersion (specialFiberι p a n) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

theorem specialFiber_isPullback :
    IsPullback (specialFiberι p a n) (specialFiberToLine p a n) (selectedProjection p a n)
      (horizontalFiberMorphism (a ^ p)) :=
  IsPullback.of_hasPullback _ _

/-- The support of the special fibre. -/
def specialFiberSupport : Set (selectedStage p a n) := Set.range (specialFiberι p a n).base

theorem specialFiberSupport_eq :
    specialFiberSupport p a n =
      (selectedProjection p a n).base ⁻¹' Set.range (horizontalFiberMorphism (a ^ p)).base :=
  Scheme.Pullback.range_fst _ _

theorem specialFiberSupport_isClosed : IsClosed (specialFiberSupport p a n) :=
  (specialFiberι p a n).isClosedEmbedding.isClosed_range

/-- The exceptional locus: the fibre of the tower over the selected centre. -/
def exceptionalLocus : Set (selectedStage p a n) :=
  (selectedProjection p a n).base ⁻¹' {graphPoint p a}

/-- The selected centre lies on the horizontal fibre. -/
theorem graphPoint_mem_horizontalFiber :
    graphPoint p a ∈ Set.range (horizontalFiberMorphism (a ^ p)).base := by
  have h : graphPoint p a = (fiberCurve ≫ translatedPlaneChart p a).base curvePoint := by
    rw [Scheme.comp_base_apply, fiberCurve_curvePoint]
    exact (selected_center p a).symm
  rw [h, fiberCurve_translatedChart, Scheme.comp_base_apply, Scheme.comp_base_apply]
  exact ⟨_, rfl⟩

theorem exceptionalLocus_subset_specialFiber :
    exceptionalLocus p a n ⊆ specialFiberSupport p a n := by
  intro x hx
  rw [specialFiberSupport_eq, Set.mem_preimage]
  have hx' : (selectedProjection p a n).base x = graphPoint p a := hx
  rw [hx']
  exact graphPoint_mem_horizontalFiber p a

/-- Every final exceptional component lies in the exceptional locus. -/
theorem finalSupport_subset_exceptionalLocus (q : ℕ) (idx : FinalIndex.{0} q) :
    finalSupport (translatedInitial p a) q idx ⊆ exceptionalLocus p a (q + 1) := by
  rintro _ ⟨z, rfl⟩
  show (selectedProjection p a (q + 1)).base ((finalComponentι (translatedInitial p a) q idx).base z) ∈
    ({graphPoint p a} : Set (projectiveProduct k))
  rw [Set.mem_singleton_iff]
  exact (finalComponent_projection_center (translatedInitial p a) q idx z).trans (selected_center p a)

/-- The strict fibre lies in the special fibre. -/
theorem fiberClosure_subset_specialFiber :
    Set.range (fiberClosureInclusion (translatedInitial p a) n).base ⊆ specialFiberSupport p a n := by
  intro x hx
  rw [range_fiberClosureInclusion_eq_residual] at hx
  rw [specialFiberSupport_eq, Set.mem_preimage]
  have h1 : (selectedProjection p a n).base x ∈
      closure ((selectedProjection p a n).base '' Set.range (fiberResidual (translatedInitial p a) n).base) :=
    image_closure_subset_closure_image (selectedProjection p a n).continuous ⟨x, hx, rfl⟩
  have h2 : (selectedProjection p a n).base '' Set.range (fiberResidual (translatedInitial p a) n).base ⊆
      Set.range (horizontalFiberMorphism (a ^ p)).base := by
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    have h3 : (selectedProjection p a n).base ((fiberResidual (translatedInitial p a) n).base t) =
        ((parameterTranslationIso a).hom ≫ ProjectiveLineComparison.polynomialChartMap k 0 ≫
          horizontalFiberMorphism (a ^ p)).base t := by
      rw [← Scheme.comp_base_apply]
      change (fiberResidual (translatedInitial p a) n ≫ (translatedInitial p a).toInitial n).base t = _
      rw [fiberResidual_toInitial]
      exact congrArg (fun f => f.base t) (fiberCurve_translatedChart p a)
    rw [h3, Scheme.comp_base_apply, Scheme.comp_base_apply]
    exact ⟨_, rfl⟩
  exact (closure_minimal h2 (horizontalFiberMorphism (a ^ p)).isClosedEmbedding.isClosed_range) h1

/-- The support of the strict fibre is the closure of the lifted punctured horizontal fibre. -/
theorem range_fiberClosureInclusion_eq_closure_lift :
    Set.range (fiberClosureInclusion (translatedInitial p a) n).base =
      closure (Set.range ((fiberAdaptedTranslated p a).lift n).base) := by
  rw [← FiberAdapted.range_strictι, ← (fiberAdaptedTranslated p a).strictIsoLocal_hom_ι n,
    range_iso_comp_base]

/-- The support of the special fibre is the strict fibre together with the exceptional locus. -/
theorem specialFiberSupport_eq_union :
    specialFiberSupport p a n =
      Set.range (fiberClosureInclusion (translatedInitial p a) n).base ∪ exceptionalLocus p a n := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [specialFiberSupport_eq, Set.mem_preimage] at hx
    by_cases hc : (selectedProjection p a n).base x = graphPoint p a
    · exact Or.inr hc
    · left
      obtain ⟨z, hz⟩ := hx
      -- `z` avoids the centre
      have hzp : z ∈ (fiberAdaptedTranslated p a).puncture := by
        change (horizontalFiberMorphism (a ^ p)).base z ≠
          (translatedInitial p a).chart.base (originPoint (k := k))
        rw [selected_center, hz]
        exact hc
      let z' : ((fiberAdaptedTranslated p a).puncture).toScheme := ⟨z, hzp⟩
      have hlift : ((fiberAdaptedTranslated p a).lift n).base z' = x := by
        apply toInitial_injective_on_puncture (translatedInitial p a) n
        · change ((translatedInitial p a).toInitial n).base
            (((fiberAdaptedTranslated p a).lift n).base z') ≠
              (translatedInitial p a).chart.base (originPoint (k := k))
          rw [← Scheme.comp_base_apply, FiberAdapted.lift_projection, FiberAdapted.puncturedCurve,
            Scheme.comp_base_apply, Scheme.Opens.ι_base_apply]
          exact hzp
        · change (selectedProjection p a n).base x ≠ (translatedInitial p a).chart.base originPoint
          rw [selected_center]
          exact hc
        · rw [← Scheme.comp_base_apply, FiberAdapted.lift_projection, FiberAdapted.puncturedCurve,
            Scheme.comp_base_apply, Scheme.Opens.ι_base_apply]
          exact hz
      rw [range_fiberClosureInclusion_eq_closure_lift]
      exact subset_closure ⟨z', hlift⟩
  · intro x hx
    rcases hx with hx | hx
    · exact fiberClosure_subset_specialFiber p a n hx
    · exact exceptionalLocus_subset_specialFiber p a n hx

end KltDP.Examples.FrobeniusSpecialFiberTower
