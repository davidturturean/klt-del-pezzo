import KltDP.Examples.FrobeniusExceptionalLaterStages
import KltDP.Geometry.SchematicImageGlued

/-!
# Adjacent exceptional points on the actual later strict transform

The whole previous strict transform projects into its original exceptional
fiber because its dense chart does, and that fiber is closed. The adjacent
point avoids the following center, so it belongs to the whole punctured
fiber used to construct the next strict transform. Its lift factors through
that actual kernel subscheme. The existing complement isomorphism identifies
this point with the lift of the original adjacent point.

Reuse: the original closure description and projection maps, the existing
glued schematic-image factorization, and pinned restriction-isomorphism
injectivity. The endpoint is membership in the newer strict transform itself.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusExceptionalAdjacentTransport

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalSuccessor
open FrobeniusExceptionalLaterStages FrobeniusStageComplement.PlaneChartedScheme

private theorem point_eq_of_iso_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)]
    {x y : X} (hx : f.base x ∈ U) (hy : f.base y ∈ U)
    (hxy : f.base x = f.base y) : x = y := by
  have hsub : (f ∣_ U).base ⟨x, hx⟩ = (f ∣_ U).base ⟨y, hy⟩ := by
    apply Subtype.ext
    exact (morphismRestrict_base_coe f U ⟨x, hx⟩).trans
      (hxy.trans (morphismRestrict_base_coe f U ⟨y, hy⟩).symm)
  exact congrArg Subtype.val ((f ∣_ U).isOpenEmbedding.injective hsub)

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- Every point of the original whole strict transform projects into its
original exceptional fiber, including points outside its selected chart. -/
theorem previousStrict_projection_mem_previousFiber (z : previousStrictTransform A) :
    A.next.nextProjection.base ((previousStrictι A).base z) ∈
      Set.range (previousFiberι A).base := by
  have hclosure : closure (Set.range (successorCurve A).base) ⊆
      A.next.nextProjection.base ⁻¹' Set.range (previousFiberι A).base := by
    apply closure_minimal
    · rintro _ ⟨q, rfl⟩
      refine ⟨(previousFiberChart A).base q, ?_⟩
      simpa only [Scheme.comp_base_apply] using
        (congrArg (fun m => m.base q) (successorCurve_projection A)).symm
    · exact (previousFiberι A).isClosedEmbedding.isClosed_range.preimage
        A.next.nextProjection.continuous
  apply hclosure
  rw [← range_previousStrictι]
  exact ⟨z, rfl⟩

/-- The entire punctured previous fiber factors through its literal kernel image. -/
private def wholePreviousToStrict :
    (previousPuncture A).toScheme ⟶ previousStrictTransform A :=
  SchematicImageGlued.toImage (wholePreviousLift A)

private theorem wholePreviousToStrict_ι :
    wholePreviousToStrict A ≫ previousStrictι A = wholePreviousLift A :=
  SchematicImageGlued.toImage_inclusion (wholePreviousLift A)

/-- After the following blowup, the lifted original adjacent point lies
on the newer actual strict transform of the adjacent exceptional fiber. -/
theorem laterAdjacentPoint_mem_nextStrict :
    ∃ z : previousStrictTransform A.next,
      (previousStrictι A.next).base z = (laterCurveMap A 1).base (adjacentPoint A) := by
  obtain ⟨q, hq⟩ : ∃ q : previousFiber A.next,
      (previousFiberι A.next).base q = (previousStrictι A).base (adjacentPoint A) :=
    adjacentPoint_mem_newFiber A
  have hp : (previousStrictι A).base (adjacentPoint A) ∈
      initialPuncture A.next.next := by
    change (previousStrictι A).base (adjacentPoint A) ≠
      A.next.next.chart.base (originPoint (k := k))
    intro h
    exact nextCenter_not_on_previousStrict A ⟨adjacentPoint A, h⟩
  have hqU : q ∈ previousPuncture A.next := by
    change (previousFiberι A.next).base q ∈ initialPuncture A.next.next
    rw [hq]
    exact hp
  let q' : (previousPuncture A.next).toScheme := ⟨q, hqU⟩
  refine ⟨(wholePreviousToStrict A.next).base q', ?_⟩
  have hfactor := congrArg (fun m => m.base q') (wholePreviousToStrict_ι A.next)
  change (previousStrictι A.next).base ((wholePreviousToStrict A.next).base q') =
    (wholePreviousLift A.next).base q' at hfactor
  rw [hfactor]
  have hwhole : A.next.next.nextProjection.base ((wholePreviousLift A.next).base q') =
      (previousStrictι A).base (adjacentPoint A) := by
    change (wholePreviousLift A.next ≫ A.next.next.nextProjection).base q' = _
    rw [wholePreviousLift_projection]
    exact hq
  have hlater : A.next.next.nextProjection.base
      ((laterCurveMap A 1).base (adjacentPoint A)) =
        (previousStrictι A).base (adjacentPoint A) := by
    have h := congrArg (fun m => m.base (adjacentPoint A)) (laterCurveMap_step A 0)
    simpa only [laterCurveMap_zero] using h
  letI := nextProjection_restrict_isIso A.next.next
  exact point_eq_of_iso_restrict A.next.next.nextProjection (initialPuncture A.next.next)
    (hwhole.symm ▸ hp) (hlater.symm ▸ hp) (hwhole.trans hlater.symm)

end KltDP.Examples.FrobeniusExceptionalAdjacentTransport
