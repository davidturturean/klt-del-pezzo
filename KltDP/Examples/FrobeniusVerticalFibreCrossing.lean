import KltDP.Examples.FrobeniusUnaffectedFibers
import KltDP.Examples.FrobeniusGraphClosed
import KltDP.Examples.FrobeniusSpecialFiberTower
import KltDP.Examples.FrobeniusStrictTransformIsoProjectiveLine
import KltDP.Examples.ProjectiveProductTranslation
import KltDP.Examples.FrobeniusStrictTransformPrimeCurves
import KltDP.Examples.FrobeniusStageProjectiveOfLiteral

/-!
# `B` and `F̃` each meet a vertical ruling fibre in at most one point (BRIEF22, item 1)

The vertical ruling fibre `x = c` with `c ≠ 0` avoids the centre of the origin contact tower
(`verticalFiber_avoids_origin_center`: the centre is the graph point `(0, 0)` by the accepted
`productTranslation_center` at `a = 0` together with `productTranslation_zero`, and its first
coordinate is `point 0`), so the accepted generic `stageLift` lifts it to every stage
(`verticalLift`), where it stays inside the stage puncture.

On `P¹ × P¹` any section of the first projection meets `x = c` in at most one point
(`section_inter_verticalFiber_subsingleton`), because the first coordinate of a point of the section
determines it while on the fibre that coordinate is constantly `point c`. Both the graph
(`projectiveGraphMorphism_fst`) and the horizontal fibre (`horizontalFiberMorphism_fst`) are such
sections.

Every point of the intersection upstairs lies on the vertical lift, hence in the stage puncture,
where the tower projection is injective (accepted `toInitial_injective_on_puncture`). Pushing the
intersection down along the accepted blowdown compatibilities
(`graphStrictIsoProjectiveLine_hom_comp`, `fiberStrictIsoProjectiveLine_hom_comp`) therefore gives

* **`graphStrict_inter_vertical_subsingleton`**: `B_n ∩ (x = c)` has at most one point, every stage;
* **`fiberStrict_inter_vertical_subsingleton`**: `F̃_n ∩ (x = c)` has at most one point, every stage;

in the shape of the accepted `strict_inter_fiber_subsingleton`, together with the prime-curve forms on
`stageSurface (n+1) hproj` and the literal-conditional bundle
`f29_vertical_fibre_single_points_of_literal`, whose only hypothesis is Stacks 0C5P (BRIEF20).

**Not proved here**: the transversality (contact length one) of these crossings, and the stage-level
graph contact length against the horizontal fibre; see the record.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusVerticalFibreCrossing

open KltDP.Geometry KltDP.Literature.Stacks
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusProductPlaneChart
open FrobeniusGraphClosed
open FrobeniusGlobalBlowupStages FrobeniusStageComplement FrobeniusStageComplement.PlaneChartedScheme
open FrobeniusUnaffectedFibers FrobeniusSpecialFiberTower FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformIsoProjectiveLine FrobeniusFiberClosure
open FrobeniusGraphPicardClassZeroFiber ProjectiveProductTranslation
open FrobeniusStageSurface FrobeniusStrictTransformPrimeCurves FrobeniusStageProjectiveOfLiteral

variable {k : Type u} [Field k]

/-- The first coordinate of the centre of the origin tower is the rational point `[1:0]`: the centre
is the graph point `(0, 0)` (accepted `productTranslation_center` at `a = 0`, with the accepted
`productTranslation_zero`). -/
theorem originCenter_fst :
    (firstProjection (k := k)).base
        ((projectiveProductInitial (k := k)).chart.base (FrobeniusBlowupChartIteration.originPoint)) = point 0 := by
  have h : (planeChart (k := k)).base (FrobeniusBlowupChartIteration.originPoint) = graphPoint 1 (0 : k) := by
    have h0 := productTranslation_center (k := k) 1 (0 : k)
    rw [pow_one, productTranslation_zero] at h0
    simpa using h0
  change (firstProjection (k := k)).base ((planeChart (k := k)).base (FrobeniusBlowupChartIteration.originPoint)) = _
  rw [h]
  exact graphPoint_fst 1 0

/-- The first coordinate along the vertical fibre `x = c` is constantly `point c`. -/
theorem verticalFiber_fst (c : k) (t : projectiveSpace k 1) :
    (firstProjection (k := k)).base ((verticalFiberMorphismAt c).base t) = point c := by
  change ((verticalFiberMorphismAt c) ≫ firstProjection).base t = point c
  rw [verticalFiberMorphismAt_fst]
  change (pointMorphism c).base ((projectiveSpaceToSpec k 1).base t) = point c
  rw [Subsingleton.elim ((projectiveSpaceToSpec k 1).base t) (IsLocalRing.closedPoint k)]
  rfl

/-- **A section of the first projection meets the vertical fibre `x = c` in at most one point.** -/
theorem section_inter_verticalFiber_subsingleton {σ : projectiveSpace k 1 ⟶ projectiveProduct k}
    (hσ : σ ≫ firstProjection = 𝟙 (projectiveSpace k 1)) (c : k) :
    (Set.range σ.base ∩ Set.range (verticalFiberMorphismAt c).base).Subsingleton := by
  have hfst : ∀ s : projectiveSpace k 1, (firstProjection (k := k)).base (σ.base s) = s := by
    intro s
    change (σ ≫ firstProjection).base s = s
    rw [hσ]
    rfl
  rintro _ ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩ _ ⟨⟨s', rfl⟩, ⟨t', ht'⟩⟩
  have hs : s = point c := by
    rw [← hfst s, ← ht, verticalFiber_fst]
  have hs' : s' = point c := by
    rw [← hfst s', ← ht', verticalFiber_fst]
  rw [hs, hs']

section AlgClosed

variable [IsAlgClosed k]

/-- **The vertical fibre `x = c`, `c ≠ 0`, avoids the centre of the origin tower.** -/
theorem verticalFiber_avoids_origin_center (c : k) (hc : c ≠ 0) (y : projectiveSpace k 1) :
    (verticalFiberMorphismAt c).base y ≠
      (projectiveProductInitial (k := k)).chart.base (FrobeniusBlowupChartIteration.originPoint) := by
  intro h
  apply hc
  apply point_injective
  have h1 := verticalFiber_fst c y
  rw [h, originCenter_fst] at h1
  exact h1.symm

/-- **The vertical ruling fibre `x = c` (`c ≠ 0`) lifted to every stage of the origin tower.** -/
def verticalLift (c : k) (hc : c ≠ 0) (n : ℕ) :
    projectiveSpace k 1 ⟶ projectiveContactStage (k := k) n :=
  stageLift (projectiveProductInitial (k := k)) (verticalFiberMorphismAt c)
    (verticalFiber_avoids_origin_center c hc) n

@[reassoc] theorem verticalLift_projection (c : k) (hc : c ≠ 0) (n : ℕ) :
    verticalLift c hc n ≫ projectiveContactProjection n = verticalFiberMorphismAt c :=
  stageLift_toInitial (projectiveProductInitial (k := k)) (verticalFiberMorphismAt c)
    (verticalFiber_avoids_origin_center c hc) n

instance verticalLift_isClosedImmersion (c : k) (hc : c ≠ 0) (n : ℕ) :
    IsClosedImmersion (verticalLift c hc n) :=
  stageLift_isClosedImmersion (projectiveProductInitial (k := k)) (verticalFiberMorphismAt c)
    (verticalFiber_avoids_origin_center c hc) n

theorem verticalLift_mem_stagePuncture (c : k) (hc : c ≠ 0) (n : ℕ) (y : projectiveSpace k 1) :
    (verticalLift c hc n).base y ∈ stagePuncture (projectiveProductInitial (k := k)) n :=
  stageLift_mem_stagePuncture (projectiveProductInitial (k := k)) (verticalFiberMorphismAt c)
    (verticalFiber_avoids_origin_center c hc) n y

/-- The blowdown of a point of `B_n ∩ (x = c)` lies on the graph and on the vertical fibre. -/
theorem graphStrict_toInitial_mem (n m : ℕ) (c : k) (hc : c ≠ 0)
    (z : projectiveContactStage (k := k) n)
    (hz : z ∈ Set.range (strictTransformι (k := k) n (m + n)).base)
    (hz' : z ∈ Set.range (verticalLift c hc n).base) :
    ((projectiveProductInitial (k := k)).toInitial n).base z ∈
      Set.range (projectiveGraphMorphism (k := k) (m + n)).base ∩
      Set.range (verticalFiberMorphismAt c).base := by
  obtain ⟨s, rfl⟩ := hz
  obtain ⟨t, ht⟩ := hz'
  refine ⟨⟨(graphStrictIsoProjectiveLine (k := k) n m).hom.base s, ?_⟩, ⟨t, ?_⟩⟩
  · change ((graphStrictIsoProjectiveLine (k := k) n m).hom ≫
      projectiveGraphMorphism (m + n)).base s = _
    rw [graphStrictIsoProjectiveLine_hom_comp n m]
    rfl
  · rw [← ht]
    change _ = (verticalLift c hc n ≫ projectiveContactProjection n).base t
    rw [verticalLift_projection]

/-- The blowdown of a point of `F̃_n ∩ (x = c)` lies on the horizontal fibre and on `x = c`. -/
theorem fiberStrict_toInitial_mem (n : ℕ) (c : k) (hc : c ≠ 0)
    (z : projectiveContactStage (k := k) n)
    (hz : z ∈ Set.range
      (fiberClosureInclusion (projectiveProductInitial (k := k)) n).base)
    (hz' : z ∈ Set.range (verticalLift c hc n).base) :
    ((projectiveProductInitial (k := k)).toInitial n).base z ∈
      Set.range (horizontalFiberMorphism (0 : k)).base ∩
      Set.range (verticalFiberMorphismAt c).base := by
  obtain ⟨s, rfl⟩ := hz
  obtain ⟨t, ht⟩ := hz'
  refine ⟨⟨(fiberStrictIsoProjectiveLine (k := k) n).hom.base s, ?_⟩, ⟨t, ?_⟩⟩
  · change ((fiberStrictIsoProjectiveLine (k := k) n).hom ≫
      horizontalFiberMorphism (0 : k)).base s = _
    rw [fiberStrictIsoProjectiveLine_hom_comp n]
    rfl
  · rw [← ht]
    change _ = (verticalLift c hc n ≫ projectiveContactProjection n).base t
    rw [verticalLift_projection]

/-- **`B_n ∩ (x = c)` has at most one point**, at every stage of the origin tower. -/
theorem graphStrict_inter_vertical_subsingleton (n m : ℕ) (c : k) (hc : c ≠ 0) :
    (Set.range (strictTransformι (k := k) n (m + n)).base ∩
      Set.range (verticalLift c hc n).base).Subsingleton := by
  intro x hx y hy
  obtain ⟨tx, htx⟩ := hx.2
  obtain ⟨ty, hty⟩ := hy.2
  refine toInitial_injective_on_puncture (projectiveProductInitial (k := k)) n
    (htx ▸ verticalLift_mem_stagePuncture c hc n tx)
    (hty ▸ verticalLift_mem_stagePuncture c hc n ty) ?_
  exact section_inter_verticalFiber_subsingleton (projectiveGraphMorphism_fst (m + n)) c
    (graphStrict_toInitial_mem n m c hc x hx.1 hx.2)
    (graphStrict_toInitial_mem n m c hc y hy.1 hy.2)

/-- **`F̃_n ∩ (x = c)` has at most one point**, at every stage of the origin tower. -/
theorem fiberStrict_inter_vertical_subsingleton (n : ℕ) (c : k) (hc : c ≠ 0) :
    (Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) n).base ∩
      Set.range (verticalLift c hc n).base).Subsingleton := by
  intro x hx y hy
  obtain ⟨tx, htx⟩ := hx.2
  obtain ⟨ty, hty⟩ := hy.2
  refine toInitial_injective_on_puncture (projectiveProductInitial (k := k)) n
    (htx ▸ verticalLift_mem_stagePuncture c hc n tx)
    (hty ▸ verticalLift_mem_stagePuncture c hc n ty) ?_
  exact section_inter_verticalFiber_subsingleton (horizontalFiberMorphism_fst (0 : k)) c
    (fiberStrict_toInitial_mem n c hc x hx.1 hx.2)
    (fiberStrict_toInitial_mem n c hc y hy.1 hy.2)

section Surface

variable (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- The prime-curve form for `B` on `stageSurface (n+1) hproj`. -/
theorem graphStrictPrimeCurve_inter_vertical_subsingleton (m : ℕ) (c : k) (hc : c ≠ 0) :
    ((graphStrictPrimeCurve n hproj m : Set (stageSurface (n + 1) hproj).toScheme) ∩
      Set.range (verticalLift c hc (n + 1)).base).Subsingleton :=
  graphStrict_inter_vertical_subsingleton (n + 1) m c hc

/-- The prime-curve form for `F̃` on `stageSurface (n+1) hproj`. -/
theorem fiberStrictPrimeCurve_inter_vertical_subsingleton (c : k) (hc : c ≠ 0) :
    ((fiberStrictPrimeCurve n hproj : Set (stageSurface (n + 1) hproj).toScheme) ∩
      Set.range (verticalLift c hc (n + 1)).base).Subsingleton :=
  fiberStrict_inter_vertical_subsingleton (n + 1) c hc

end Surface

end AlgClosed

end KltDP.Examples.FrobeniusVerticalFibreCrossing

namespace KltDP.Examples

open KltDP.Geometry KltDP.Literature.Stacks FrobeniusGlobalBlowupStages FrobeniusStageSurface
  FrobeniusStrictTransformPrimeCurves FrobeniusStageProjectiveOfLiteral
  FrobeniusVerticalFibreCrossing

/-- **F29: `B` and `F̃` each meet a vertical ruling fibre in at most one point**, at every stage,
with Stacks 0C5P as the only hypothesis (the projectivity of the stage comes from BRIEF20's
`stage_isProjective_of_literal`). -/
theorem f29_vertical_fibre_single_points_of_literal (k : Type u) [Field k] [IsAlgClosed k]
    (hlit : RegularProperProjectiveLiteral k) (n m : ℕ) (c : k) (hc : c ≠ 0) :
    ((graphStrictPrimeCurve n (stage_isProjective_of_literal hlit (n + 1)) m :
        Set (stageSurface (n + 1) (stage_isProjective_of_literal hlit (n + 1))).toScheme) ∩
      Set.range (verticalLift c hc (n + 1)).base).Subsingleton ∧
    ((fiberStrictPrimeCurve n (stage_isProjective_of_literal hlit (n + 1)) :
        Set (stageSurface (n + 1) (stage_isProjective_of_literal hlit (n + 1))).toScheme) ∩
      Set.range (verticalLift c hc (n + 1)).base).Subsingleton :=
  ⟨graphStrictPrimeCurve_inter_vertical_subsingleton n _ m c hc,
    fiberStrictPrimeCurve_inter_vertical_subsingleton n _ c hc⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_vertical_fibre_single_points_of_literal_universe_check (k : Type u) [Field k]
    [IsAlgClosed k] (hlit : RegularProperProjectiveLiteral k) (n m : ℕ) (c : k) (hc : c ≠ 0) :
    True := by
  have _ := f29_vertical_fibre_single_points_of_literal.{u} k hlit n m c hc
  trivial

end KltDP.Examples
