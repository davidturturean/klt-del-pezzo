import KltDP.Examples.FrobeniusSpecialFiberTower
import KltDP.Examples.FrobeniusMultiCentreFiberContacts

/-!
# The complete scheme-theoretic fibre over a selected point on `S_{p,n}`

Route (iv) of BRIEF7 at the level of supports: on `S_{p,n} = multiSurface (q+1) n a` the complete
scheme-theoretic fibre over the `b`-ruling point `y = (a i)^p` is the literal pullback of the horizontal
fibre along the projection to `P¹ ×_k P¹` (`specialFiberS`), a closed subscheme. Its support is the
strict fibre `F_i` together with the exceptional locus of the `i`-th cluster (the fibre of `S_{p,n}`
over the centre `(a_i, a_i^p)`), which contains every `C_{ij}` and `P_i`
(`specialFiberSSupport_eq_union`, `exceptionalSupport_subset_clusterLocus`). The other clusters do not
meet this fibre because in characteristic `p` the heights `(a j)^p` are distinct for distinct `a j`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusSpecialFiberSPn

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber
  FrobeniusGraphPicardClassZeroFiber FrobeniusUnaffectedFibers FrobeniusSpecialFiberTower

variable {k : Type u} [Field k]

variable (q n : ℕ) (a : Fin n → k)

/-- The complete scheme-theoretic fibre of `S_{p,n}` over the `b`-ruling point `y = (a i)^p`. -/
def specialFiberS (i : Fin n) : Scheme.{u} :=
  pullback (multiProjection (q + 1) n a) (horizontalFiberMorphism (a i ^ (q + 1)))

/-- Its closed immersion into `S_{p,n}`. -/
def specialFiberSι (i : Fin n) : specialFiberS q n a i ⟶ multiSurface (q + 1) n a := pullback.fst _ _

/-- Its projection to the fibre `P¹`. -/
def specialFiberSToLine (i : Fin n) : specialFiberS q n a i ⟶ projectiveSpace k 1 := pullback.snd _ _

instance specialFiberSι_isClosedImmersion (i : Fin n) : IsClosedImmersion (specialFiberSι q n a i) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

theorem specialFiberS_isPullback (i : Fin n) :
    IsPullback (specialFiberSι q n a i) (specialFiberSToLine q n a i) (multiProjection (q + 1) n a)
      (horizontalFiberMorphism (a i ^ (q + 1))) :=
  IsPullback.of_hasPullback _ _

/-- The support of the special fibre of `S_{p,n}`. -/
def specialFiberSSupport (i : Fin n) : Set (multiSurface (q + 1) n a) :=
  Set.range (specialFiberSι q n a i).base

theorem specialFiberSSupport_eq (i : Fin n) :
    specialFiberSSupport q n a i =
      (multiProjection (q + 1) n a).base ⁻¹' Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base :=
  Scheme.Pullback.range_fst _ _

/-- The exceptional locus of the `i`-th cluster: the fibre of `S_{p,n}` over the `i`-th centre. -/
def clusterLocus (i : Fin n) : Set (multiSurface (q + 1) n a) :=
  (multiProjection (q + 1) n a).base ⁻¹' {graphPoint (q + 1) (a i)}

theorem clusterLocus_subset_specialFiberS (i : Fin n) :
    clusterLocus q n a i ⊆ specialFiberSSupport q n a i := by
  intro x hx
  rw [specialFiberSSupport_eq, Set.mem_preimage]
  have hx' : (multiProjection (q + 1) n a).base x = graphPoint (q + 1) (a i) := hx
  rw [hx']
  exact graphPoint_mem_horizontalFiber (q + 1) (a i)

/-- Every exceptional curve `C_{ij}`, `P_i` of the `i`-th cluster lies in its exceptional locus. -/
theorem exceptionalSupport_subset_clusterLocus (i : Fin n) (idx : FinalIndex.{0} q) :
    exceptionalSupport q n a i idx ⊆ clusterLocus q n a i := by
  intro x hx
  show (multiProjection (q + 1) n a).base x ∈ ({graphPoint (q + 1) (a i)} : Set (projectiveProduct k))
  rw [Set.mem_singleton_iff]
  exact exceptionalSupport_projection q n a i idx x hx

/-- The strict fibre `F_i` lies in the special fibre. -/
theorem fiberStrict_subset_specialFiberS (i : Fin n) :
    Set.range (fiberStrictι (q + 1) n a i).base ⊆ specialFiberSSupport q n a i := by
  intro x hx
  rw [range_fiberStrictι] at hx
  rw [specialFiberSSupport_eq, Set.mem_preimage]
  have h1 : (multiProjection (q + 1) n a).base x ∈
      closure ((multiProjection (q + 1) n a).base '' Set.range (fiberLift (q + 1) n a i).base) :=
    image_closure_subset_closure_image (multiProjection (q + 1) n a).continuous ⟨x, hx, rfl⟩
  have h2 : (multiProjection (q + 1) n a).base '' Set.range (fiberLift (q + 1) n a i).base ⊆
      Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(fiberPuncture (q + 1) n a i).ι.base z, ?_⟩
    rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, fiberLift_projection]
    rfl
  exact (closure_minimal h2
    (horizontalFiberMorphism (a i ^ (q + 1))).isClosedEmbedding.isClosed_range) h1

/-! ## Injectivity of the projection over the complement of the centres -/

/-- The projection restricted to the complement of all centres. -/
def centersMap :
    (multiProjection (q + 1) n a ⁻¹ᵁ centersComplement (q + 1) n a).toScheme ⟶ projectiveProduct k :=
  (multiProjection (q + 1) n a ∣_ centersComplement (q + 1) n a) ≫ (centersComplement (q + 1) n a).ι

instance centersMap_isOpenImmersion : IsOpenImmersion (centersMap q n a) := by
  letI := multiProjection_restrict_centersComplement_isIso (q + 1) n a
  unfold centersMap
  infer_instance

theorem centersMap_base (y : (multiProjection (q + 1) n a ⁻¹ᵁ centersComplement (q + 1) n a).toScheme) :
    (centersMap q n a).base y =
      (multiProjection (q + 1) n a).base
        ((multiProjection (q + 1) n a ⁻¹ᵁ centersComplement (q + 1) n a).ι.base y) := by
  rw [centersMap, morphismRestrict_ι, Scheme.comp_base_apply]

theorem multiProjection_injective_on_complement {x y : multiSurface (q + 1) n a}
    (hx : x ∈ multiProjection (q + 1) n a ⁻¹ᵁ centersComplement (q + 1) n a)
    (hy : y ∈ multiProjection (q + 1) n a ⁻¹ᵁ centersComplement (q + 1) n a)
    (h : (multiProjection (q + 1) n a).base x = (multiProjection (q + 1) n a).base y) : x = y := by
  have h' : (⟨x, hx⟩ : (multiProjection (q + 1) n a ⁻¹ᵁ centersComplement (q + 1) n a).toScheme) =
      ⟨y, hy⟩ := by
    apply (centersMap q n a).isOpenEmbedding.injective
    rw [centersMap_base, centersMap_base]
    exact h
  exact congrArg Subtype.val h'

/-! ## The support decomposition -/

section Heights

variable [Fact (q + 1).Prime] [CharP k (q + 1)] (ha : Function.Injective a)
include ha

/-- Distinct selected parameters have distinct heights `a^p` in characteristic `p`. -/
theorem heights_ne {i j : Fin n} (hij : j ≠ i) : a i ^ (q + 1) ≠ a j ^ (q + 1) := by
  intro h
  apply hij
  apply ha
  exact (frobenius_inj k (q + 1) (show frobenius k (q + 1) (a i) = frobenius k (q + 1) (a j) by
    simpa only [frobenius_def] using h)).symm

end Heights

section Unaffected

variable [IsAlgClosed k]

/-- A horizontal fibre at a non-selected height avoids every centre. -/
theorem horizontalFiber_range_centersComplement (c : k) (hc : ∀ j, c ≠ a j ^ (q + 1)) :
    Set.range (horizontalFiberMorphism c).base ⊆
      Set.range (centersComplement (q + 1) n a).ι.base := by
  rintro _ ⟨z, rfl⟩
  refine ⟨⟨(horizontalFiberMorphism c).base z, ?_⟩, rfl⟩
  rw [mem_centersComplement_iff]
  intro j
  have h := horizontalFiber_avoids_center (q + 1) (a j) c (hc j) z
  rwa [selected_center] at h

/-- The lift of a horizontal fibre at a non-selected height to `S_{p,n}`. -/
def unaffectedFiberLift (c : k) (hc : ∀ j, c ≠ a j ^ (q + 1)) :
    projectiveSpace k 1 ⟶ multiSurface (q + 1) n a :=
  letI := multiProjection_restrict_centersComplement_isIso (q + 1) n a
  liftOverIso (multiProjection (q + 1) n a) (centersComplement (q + 1) n a)
    (horizontalFiberMorphism c) (horizontalFiber_range_centersComplement q n a c hc)

theorem unaffectedFiberLift_isPullback (c : k) (hc : ∀ j, c ≠ a j ^ (q + 1)) :
    IsPullback (unaffectedFiberLift q n a c hc) (𝟙 (projectiveSpace k 1))
      (multiProjection (q + 1) n a) (horizontalFiberMorphism c) := by
  letI := multiProjection_restrict_centersComplement_isIso (q + 1) n a
  exact liftOverIso_isPullback _ _ _ _

/-- The complete scheme-theoretic fibre of `S_{p,n}` over a non-selected height is the projective
line. -/
def unaffectedFiberIso (c : k) (hc : ∀ j, c ≠ a j ^ (q + 1)) :
    projectiveSpace k 1 ≅ pullback (multiProjection (q + 1) n a) (horizontalFiberMorphism c) :=
  (unaffectedFiberLift_isPullback q n a c hc).isoPullback

end Unaffected

section Distinct

variable [IsAlgClosed k] [Fact (q + 1).Prime] [CharP k (q + 1)] (ha : Function.Injective a)
include ha

/-- A point of the horizontal fibre `y = (a i)^p` other than the `i`-th centre avoids all centres. -/
theorem horizontalFiber_mem_centersComplement (i : Fin n) (z : projectiveSpace k 1)
    (hz : (horizontalFiberMorphism (a i ^ (q + 1))).base z ≠ graphPoint (q + 1) (a i)) :
    (horizontalFiberMorphism (a i ^ (q + 1))).base z ∈ centersComplement (q + 1) n a := by
  rw [mem_centersComplement_iff]
  intro j
  by_cases hj : j = i
  · rw [hj]
    exact hz
  · have h := horizontalFiber_avoids_center (q + 1) (a j) (a i ^ (q + 1)) (heights_ne q n a ha hj) z
    rwa [selected_center] at h

/-- The support of the special fibre of `S_{p,n}` over `y = (a i)^p` is `F_i` together with the
exceptional locus of the `i`-th cluster. -/
theorem specialFiberSSupport_eq_union (i : Fin n) :
    specialFiberSSupport q n a i =
      Set.range (fiberStrictι (q + 1) n a i).base ∪ clusterLocus q n a i := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [specialFiberSSupport_eq, Set.mem_preimage] at hx
    by_cases hc : (multiProjection (q + 1) n a).base x = graphPoint (q + 1) (a i)
    · exact Or.inr hc
    · left
      obtain ⟨z, hz⟩ := hx
      have hzC : (horizontalFiberMorphism (a i ^ (q + 1))).base z ∈ centersComplement (q + 1) n a :=
        horizontalFiber_mem_centersComplement q n a ha i z (by rw [hz]; exact hc)
      let z' : (fiberPuncture (q + 1) n a i).toScheme := ⟨z, hzC⟩
      have hlift : (fiberLift (q + 1) n a i).base z' = x := by
        apply multiProjection_injective_on_complement q n a
        · change (multiProjection (q + 1) n a).base ((fiberLift (q + 1) n a i).base z') ∈
            centersComplement (q + 1) n a
          rw [← Scheme.comp_base_apply, fiberLift_projection, puncturedFiber, Scheme.comp_base_apply,
            Scheme.Opens.ι_base_apply]
          exact hzC
        · change (multiProjection (q + 1) n a).base x ∈ centersComplement (q + 1) n a
          rw [← hz]
          exact hzC
        · rw [← Scheme.comp_base_apply, fiberLift_projection, puncturedFiber, Scheme.comp_base_apply,
            Scheme.Opens.ι_base_apply]
          exact hz
      rw [range_fiberStrictι]
      exact subset_closure ⟨z', hlift⟩
  · intro x hx
    rcases hx with hx | hx
    · exact fiberStrict_subset_specialFiberS q n a i hx
    · exact clusterLocus_subset_specialFiberS q n a i hx

/-- The special fibre over `(a i)^p` is disjoint from the exceptional curves of the other clusters. -/
theorem specialFiberS_disjoint_other_exceptional (i j : Fin n) (hij : j ≠ i)
    (idx : FinalIndex.{0} q) :
    Disjoint (specialFiberSSupport q n a i) (exceptionalSupport q n a j idx) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [specialFiberSSupport_eq, Set.mem_preimage] at hx
  obtain ⟨z, hz⟩ := hx
  have h := horizontalFiber_avoids_center (q + 1) (a j) (a i ^ (q + 1)) (heights_ne q n a ha hij) z
  rw [selected_center, hz] at h
  exact h (exceptionalSupport_projection q n a j idx x hx')

end Distinct

end KltDP.Examples.FrobeniusSpecialFiberSPn

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGraphPicardClassZeroFiber FrobeniusExceptionalFinalConfiguration
  FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber
  FrobeniusSpecialFiberSPn

/-- Bundle: the complete scheme-theoretic fibres of `S_{p,n}` over the selected heights `(a i)^p`. -/
theorem f29_special_fiber_sPn (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ) [Fact (q + 1).Prime]
    [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) :
    (∀ i : Fin n, IsClosedImmersion (specialFiberSι q n a i)) ∧
    (∀ i : Fin n, IsPullback (specialFiberSι q n a i) (specialFiberSToLine q n a i)
      (multiProjection (q + 1) n a) (horizontalFiberMorphism (a i ^ (q + 1)))) ∧
    (∀ i : Fin n, specialFiberSSupport q n a i =
      Set.range (fiberStrictι (q + 1) n a i).base ∪ clusterLocus q n a i) ∧
    (∀ (i : Fin n) (idx : FinalIndex.{0} q),
      exceptionalSupport q n a i idx ⊆ specialFiberSSupport q n a i) ∧
    (∀ i : Fin n, Set.range (fiberStrictι (q + 1) n a i).base ⊆ specialFiberSSupport q n a i) ∧
    (∀ (i j : Fin n), j ≠ i → ∀ idx : FinalIndex.{0} q,
      Disjoint (specialFiberSSupport q n a i) (exceptionalSupport q n a j idx)) ∧
    (∀ c : k, (∀ j, c ≠ a j ^ (q + 1)) →
      Nonempty (projectiveSpace k 1 ≅ pullback (multiProjection (q + 1) n a) (horizontalFiberMorphism c))) :=
  ⟨fun i => specialFiberSι_isClosedImmersion q n a i,
    fun i => specialFiberS_isPullback q n a i,
    fun i => specialFiberSSupport_eq_union q n a ha i,
    fun i idx => (exceptionalSupport_subset_clusterLocus q n a i idx).trans
      (clusterLocus_subset_specialFiberS q n a i),
    fun i => fiberStrict_subset_specialFiberS q n a i,
    fun i j hij idx => specialFiberS_disjoint_other_exceptional q n a ha i j hij idx,
    fun c hc => ⟨unaffectedFiberIso q n a c hc⟩⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_special_fiber_sPn_universe_check (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) : True := by
  have _ := f29_special_fiber_sPn.{u} k q n a ha
  trivial

end KltDP.Examples
