import KltDP.Geometry.GluedIdealSheafLift
import KltDP.Geometry.SchematicImageToImageIso
import KltDP.Examples.FrobeniusGlobalExceptionalSuccessor
import KltDP.Examples.FrobeniusMultiCentreExceptional

/-!
# The blowdown of the previous exceptional strict transform onto the previous exceptional curve

The strict transform `C = previousStrictTransform A` of the exceptional curve `P = previousFiber A` under
the next blowup projects into `P` (`range_strictBlowdown_subset`), so the kernel of `P ↪ A.next` is
contained in that of `C ⟶ A.next` (`previousFiberι_ker_le`, through the reduced-source vanishing ideals of
BRIEF13), and the generic `liftGlued` together with `toImageIso` (BRIEF14) give the **blowdown morphism**
`strictToFiber A : C ⟶ P` with `strictToFiber A ≫ previousFiberι A = previousStrictι A ≫ A.next.nextProjection`
(`strictToFiber_ι`). It is surjective (`strictToFiber_surjective`): off the next centre by the accepted lift
`wholePreviousLift`, at the centre by the accepted `adjacentPoint`.

If `strictToFiber A` is a closed immersion (the remaining local statement, see the note), the pinned
`isIso_of_isClosedImmersion_of_surjective` makes it an isomorphism, so `C ≅ P ≅ P¹`
(`strictIsoProjectiveLine`), and the older exceptional curves `C_ij` of `S_{p,n}` are `≅ P¹`
(`sPn_oldExceptional_iso_projectiveLine_of`). The closed-immersion property itself is not proved here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusPreviousStrictBlowdown

open KltDP.Geometry KltDP.Geometry.SchematicImageOpenBaseChange
  KltDP.Geometry.SchematicImageToImageIso KltDP.Geometry.GluedIdealSheafLift
  FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalSuccessor

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

local instance originPoint_asIdeal_isMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The strict transform blown down to the previous stage. -/
abbrev strictBlowdown : previousStrictTransform A ⟶ A.next.carrier :=
  previousStrictι A ≫ A.next.nextProjection

/-- The blowdown of the strict transform lands in the previous exceptional curve. -/
theorem range_strictBlowdown_subset :
    Set.range (strictBlowdown A).base ⊆ Set.range (previousFiberι A).base := by
  rintro _ ⟨z, rfl⟩
  have hz : (previousStrictι A).base z ∈ closure (Set.range (successorCurve A).base) := by
    rw [← range_previousStrictι]
    exact ⟨z, rfl⟩
  have hsub : closure (Set.range (successorCurve A).base) ⊆
      A.next.nextProjection.base ⁻¹' Set.range (previousFiberι A).base := by
    apply closure_minimal
    · rintro _ ⟨t, rfl⟩
      refine ⟨(previousFiberChart A).base t, ?_⟩
      change (previousFiberChart A ≫ previousFiberι A).base t =
        (successorCurve A ≫ A.next.nextProjection).base t
      rw [successorCurve_projection]
    · exact (previousFiberι A).isClosedEmbedding.isClosed_range.preimage
        A.next.nextProjection.base.hom.continuous
  exact hsub hz

/-- The kernel of the previous exceptional curve is contained in that of the blowdown. -/
theorem previousFiberι_ker_le : (previousFiberι A).ker ≤ (strictBlowdown A).ker := by
  rw [ker_eq_vanishingIdeal_rangeClosure (previousFiberι A),
    ker_eq_vanishingIdeal_rangeClosure (strictBlowdown A)]
  apply Scheme.IdealSheafData.vanishingIdeal_antimono
  change closure (Set.range (strictBlowdown A).base) ⊆ closure (Set.range (previousFiberι A).base)
  exact closure_mono (range_strictBlowdown_subset A)

/-- **The blowdown morphism** of the strict transform onto the previous exceptional curve. -/
def strictToFiber : previousStrictTransform A ⟶ previousFiber A :=
  liftGlued (previousFiberι A).ker (strictBlowdown A) (previousFiberι_ker_le A) ≫
    (toImageIso (previousFiberι A)).inv

@[reassoc] theorem strictToFiber_ι :
    strictToFiber A ≫ previousFiberι A = previousStrictι A ≫ A.next.nextProjection := by
  rw [strictToFiber, Category.assoc, toImageIso_inv_comp, liftGlued_gluedTo]

theorem strictToFiber_base (z : previousStrictTransform A) :
    (previousFiberι A).base ((strictToFiber A).base z) =
      A.next.nextProjection.base ((previousStrictι A).base z) := by
  change (strictToFiber A ≫ previousFiberι A).base z =
    (previousStrictι A ≫ A.next.nextProjection).base z
  rw [strictToFiber_ι]

/-! ## Surjectivity -/

theorem range_wholePreviousLift_subset :
    Set.range (wholePreviousLift A).base ⊆ Set.range (previousStrictι A).base := by
  letI : NoetherianSpace (projectiveSpace k 1) := projectiveSpace_noetherianSpace k 1
  letI : NoetherianSpace (previousFiber A) :=
    (previousFiberIso A).hom.isOpenEmbedding.isInducing.noetherianSpace
  letI : NoetherianSpace (previousPuncture A).toScheme :=
    (previousPuncture A).ι.isOpenEmbedding.isInducing.noetherianSpace
  intro x hx
  have h : Set.range (previousStrictι A).base = closure (Set.range (wholePreviousLift A).base) := by
    rw [Scheme.IdealSheafData.range_gluedTo]
    exact Scheme.Hom.support_ker (wholePreviousLift A)
  rw [h]
  exact subset_closure hx

/-- The adjacent point blows down to the next centre. -/
theorem strictBlowdown_adjacentPoint :
    (strictBlowdown A).base (adjacentPoint A) = A.next.chart.base (originPoint (k := k)) := by
  have h := adjacentPoint_mem_newFiber A
  rw [PointBlowupGluing.range_globalCenterFiberι] at h
  exact h

/-- **The blowdown is surjective.** -/
theorem strictToFiber_surjective : Surjective (strictToFiber A) := by
  constructor
  intro y
  by_cases hy : y ∈ previousPuncture A
  · obtain ⟨z, hz⟩ := range_wholePreviousLift_subset A ⟨⟨y, hy⟩, rfl⟩
    refine ⟨z, (previousFiberι A).isClosedEmbedding.injective ?_⟩
    rw [strictToFiber_base, hz]
    change (wholePreviousLift A ≫ A.next.nextProjection).base ⟨y, hy⟩ = _
    rw [wholePreviousLift_projection]
    rfl
  · have h : (previousFiberι A).base y = A.next.chart.base (originPoint (k := k)) := by
      by_contra hne
      apply hy
      change (previousFiberι A).base y ∈
        ({A.next.chart.base (originPoint (k := k))} : Set A.next.carrier)ᶜ
      exact hne
    refine ⟨adjacentPoint A, (previousFiberι A).isClosedEmbedding.injective ?_⟩
    rw [strictToFiber_base, h]
    exact strictBlowdown_adjacentPoint A

/-! ## The isomorphism, given the closed-immersion property -/

/-- If the blowdown is a closed immersion, it is an isomorphism (pinned
`isIso_of_isClosedImmersion_of_surjective`), and the strict transform is `P¹`. -/
def strictIsoProjectiveLine (h : IsClosedImmersion (strictToFiber A)) :
    previousStrictTransform A ≅ projectiveSpace k 1 :=
  letI := h
  letI := strictToFiber_surjective A
  letI : IsIso (strictToFiber A) := isIso_of_isClosedImmersion_of_surjective _
  asIso (strictToFiber A) ≪≫ previousFiberIso A

end KltDP.Examples.FrobeniusPreviousStrictBlowdown

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalSuccessor
  FrobeniusTranslatedCharts FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreExceptional
  FrobeniusPreviousStrictBlowdown

/-- Conditional bundle: if the blowdown of every previous exceptional strict transform is a closed
immersion, then every older exceptional curve `C_ij` of `S_{p,n}` is isomorphic to `P¹` (through the
lane's `exceptionalCurveIso` and the birth-stage isomorphism). -/
theorem sPn_oldExceptional_iso_projectiveLine_of (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    (a : Fin n → k) (ha : Function.Injective a)
    (h : ∀ A : PlaneChartedScheme k, IsClosedImmersion (strictToFiber A)) :
    ∀ (i : Fin n) (j : Fin q),
      Nonempty (exceptionalCurve q n a i (Sum.inl j) ≅ projectiveSpace k 1) :=
  fun i j => ⟨exceptionalCurveIso q n a ha i (Sum.inl j) ≪≫
    strictIsoProjectiveLine ((translatedInitial (q + 1) (a i)).stage j.val) (h _)⟩

/-- The conditional bundle has exactly one universe parameter. -/
theorem sPn_oldExceptional_iso_projectiveLine_of_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
    (h : ∀ A : PlaneChartedScheme k, IsClosedImmersion (strictToFiber A)) : True := by
  have _ := sPn_oldExceptional_iso_projectiveLine_of.{u} k q n a ha h
  trivial

end KltDP.Examples
