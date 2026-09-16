import KltDP.Examples.FrobeniusStrictTransformIsoProjectiveLine
import KltDP.Examples.FrobeniusStrictTransformPrimeCurves

/-!
# The blowdowns of the origin tower preserve generic points (BRIEF15, item 3, first part)

`stepProjection n : stage (n+1) ⟶ stage n` is an isomorphism over the centre complement, which
contains the generic point of stage `n`; the generic point of stage `n+1` specialises to the lift
of the generic point, so its image specialises to the generic point and equals it (schemes are
`T0`): `stepProjection_base_genericPoint`, and by composition
`projectiveContactProjection_base_genericPoint`. These are exactly the fields of the accepted class
`GenericPointPreserving` of `CartierDivisorPullback` (whose module is not in the dev711-07 tree, so the
instances are stated there as the bare equalities); with them the accepted `pullbackDivisor` applies
to every effective Cartier divisor with regular equations on any stage.

**Not proved here** (the remaining two items of the accepted header): the compatibility
`cartierPicardHom (π^*D) = schemePicardPullbackHom π (cartierPicardHom D)` and the additivity of
`pullbackDivisor` (the pullback is glued from equations; both need the zero-scheme base change).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusBlowdownGenericPoint

open KltDP.Geometry
open FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformIsoProjectiveLine FrobeniusStrictTransformPrimeCurves
open FrobeniusStageComplement.PlaneChartedScheme FrobeniusGraphClosed

variable {k : Type u} [Field k]

/-- The base of the origin tower is integral (accepted), as a local instance. -/
local instance initial_isIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- Every stage puncture has a point. -/
theorem stagePuncture_nonempty (N : ℕ) :
    ∃ x : projectiveContactStage (k := k) N,
      x ∈ stagePuncture (projectiveProductInitial (k := k)) N := by
  obtain ⟨g⟩ := graphPuncture_nonempty (k := k) 1
  have hz : (graphι 1).base g.1 ∈
      Set.range (initialPuncture (projectiveProductInitial (k := k))).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact g.2
  obtain ⟨w, hw⟩ := hz
  exact ⟨(stagePuncture (projectiveProductInitial (k := k)) N).ι.base
    ((stageComplementIso (projectiveProductInitial (k := k)) N).inv.base w),
    ((stageComplementIso (projectiveProductInitial (k := k)) N).inv.base w).2⟩

/-- The generic point of stage `n` lies in the centre complement. -/
theorem genericPoint_mem_initialPuncture (n : ℕ) :
    genericPoint (projectiveContactStage (k := k) n) ∈
      initialPuncture ((projectiveProductInitial (k := k)).stage n) := by
  obtain ⟨x, hx⟩ := stagePuncture_nonempty (k := k) n
  have hU : x ∈ initialPuncture ((projectiveProductInitial (k := k)).stage n) :=
    stagePuncture_le_currentPuncture (projectiveProductInitial (k := k)) n hx
  exact ((genericPoint_spec (projectiveContactStage (k := k) n)).mem_open_set_iff
    (initialPuncture ((projectiveProductInitial (k := k)).stage n)).isOpen).mpr
    ⟨x, Set.mem_univ x, hU⟩

/-- **The step blowdown maps the generic point to the generic point.** -/
theorem stepProjection_base_genericPoint (n : ℕ) :
    ((projectiveProductInitial (k := k)).stepProjection n).base
        (genericPoint (projectiveContactStage (k := k) (n + 1))) =
      genericPoint (projectiveContactStage (k := k) n) := by
  set π := (projectiveProductInitial (k := k)).stepProjection n
  set U := initialPuncture ((projectiveProductInitial (k := k)).stage n)
  have hξ : genericPoint (projectiveContactStage (k := k) n) ∈ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact genericPoint_mem_initialPuncture n
  obtain ⟨u₀, hu₀⟩ := hξ
  haveI : IsIso (π ∣_ U) := FrobeniusStrictTransformStepPuncture.stepProjection_puncture_isIso n
  have h1 : genericPoint (projectiveContactStage (k := k) (n + 1)) ⤳
      (π ⁻¹ᵁ U).ι.base ((inv (π ∣_ U)).base u₀) := genericPoint_specializes _
  have h2 := h1.map π.continuous
  have h3 : π.base ((π ⁻¹ᵁ U).ι.base ((inv (π ∣_ U)).base u₀)) =
      genericPoint (projectiveContactStage (k := k) n) := by
    rw [← Scheme.comp_base_apply, ← morphismRestrict_ι, Scheme.comp_base_apply,
      ← Scheme.comp_base_apply (inv (π ∣_ U)) (π ∣_ U), IsIso.inv_hom_id]
    exact hu₀
  rw [h3] at h2
  exact (h2.antisymm (genericPoint_specializes _)).eq

/-- **The blowdown to stage `0` maps the generic point to the generic point** (by composition). -/
theorem projectiveContactProjection_base_genericPoint :
    ∀ N : ℕ, (projectiveContactProjection (k := k) N).base
        (genericPoint (projectiveContactStage (k := k) N)) =
      genericPoint (projectiveContactStage (k := k) 0)
  | 0 => rfl
  | N + 1 => by
    show ((projectiveProductInitial (k := k)).stepProjection N ≫
      projectiveContactProjection N).base (genericPoint (projectiveContactStage (k := k) (N + 1))) = _
    rw [Scheme.comp_base_apply, stepProjection_base_genericPoint,
      projectiveContactProjection_base_genericPoint N]

end KltDP.Examples.FrobeniusBlowdownGenericPoint
