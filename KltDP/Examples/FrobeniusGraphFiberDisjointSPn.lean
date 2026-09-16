import KltDP.Examples.FrobeniusIncidenceSPn
import KltDP.Examples.FrobeniusPowerInfinity
import KltDP.Examples.ProjectiveProductChartCriterion

/-!
# `B ∩ F_i = ∅` on `S_{p,n}`

A common point `x` of the strict graph `B` and the strict fibre `F_i` projects to a point `y` of
`P¹ ×_k P¹` on the graph and on the fibre `y = a_i^p`, and (BRIEF10,
`graphStrict_fiberStrict_projection_not_mem_chart`) outside the translated affine chart around the
`i`-th centre. By the coordinate criterion one coordinate of `y` is infinite; the second coordinate is
the finite point `[1 : a_i^p]` (`horizontalFiber_snd`), so the first is `∞`
(`eq_infinityPoint_of_not_mem_chart`); but on the graph the second coordinate is the power of the
first (`graph_snd`), and the power morphism fixes `∞` — so the second coordinate would be `∞`, which is
not finite. Hence `B` and `F_i` are disjoint (`graphStrict_fiberStrict_disjoint`), for every field of
characteristic `p` (no algebraic closure or injectivity of `a` is needed).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusGraphFiberDisjointSPn

open KltDP.Geometry ProjectiveLineComparison FrobeniusProjectivePoints FrobeniusProjectiveMorphism
  FrobeniusGraphClosed FrobeniusGraphPicardClassZeroFiber FrobeniusTranslatedCharts FrobeniusMultiCentreSurface
  FrobeniusMultiCentreGraphFiber FrobeniusIncidenceSPn ProjectiveLinePointAtInfinity
  FrobeniusPowerInfinity ProjectiveProductChartCriterion

variable {k : Type u} [Field k]

/-- On the graph, the second coordinate is the power of the first. -/
theorem graph_snd (p : ℕ) (g : graph (k := k) p) :
    secondProjection.base ((graphι p).base g) =
      (projectivePowerMorphism p).base (firstProjection.base ((graphι p).base g)) := by
  have h2 : (graphι p ≫ (firstProjection ≫ projectivePowerMorphism (k := k) p)).base g =
      (graphι p ≫ secondProjection).base g := by
    rw [show graphι p ≫ (firstProjection ≫ projectivePowerMorphism (k := k) p) =
      graphι p ≫ secondProjection from equalizer.condition _ _]
  rw [Scheme.comp_base_apply, Scheme.comp_base_apply, Scheme.comp_base_apply] at h2
  exact h2.symm

/-- On the horizontal fibre `y = c`, the second coordinate is the finite point `[1 : c]`. -/
theorem horizontalFiber_snd (c : k) (h : projectiveSpace k 1) :
    secondProjection.base ((horizontalFiberMorphism c).base h) = FrobeniusProjectivePoints.point c := by
  rw [← Scheme.comp_base_apply, horizontalFiberMorphism_snd, Scheme.comp_base_apply]
  have hm : (pointMorphism c).base ((projectiveSpaceToSpec k 1).base h) ∈
      Set.range (pointMorphism c).base := ⟨_, rfl⟩
  rw [range_fieldMorphism] at hm
  exact hm

variable (q n : ℕ) (a : Fin n → k) [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- **`B ∩ F_i = ∅`**: the strict graph and the strict fibre through the `i`-th centre are disjoint. -/
theorem graphStrict_fiberStrict_disjoint (i : Fin n) (x : multiSurface (q + 1) n a)
    (hB : x ∈ Set.range (graphStrictι (q + 1) n a).base)
    (hF : x ∈ Set.range (fiberStrictι (q + 1) n a i).base) : False := by
  have hnot := graphStrict_fiberStrict_projection_not_mem_chart q n a i x hB hF
  obtain ⟨g, hg⟩ := hB
  obtain ⟨f, hf⟩ := hF
  have hyG : (multiProjection (q + 1) n a).base x ∈ Set.range (graphι (k := k) (q + 1)).base := by
    rw [← hg]
    exact graphStrict_projection_mem (q + 1) n a g
  have hyF : (multiProjection (q + 1) n a).base x ∈
      Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base := by
    rw [← hf]
    exact fiberStrict_projection_mem (q + 1) n a i f
  obtain ⟨gg, hgg⟩ := hyG
  obtain ⟨hh, hhh⟩ := hyF
  have hsnd : secondProjection.base ((multiProjection (q + 1) n a).base x) =
      FrobeniusProjectivePoints.point (a i ^ (q + 1)) := by
    rw [← hhh]
    exact horizontalFiber_snd _ _
  have hnot' : (multiProjection (q + 1) n a).base x ∉
      Set.range (translatedPlaneChart (q + 1) (a i)).base := hnot
  rw [mem_range_translatedPlaneChart_iff] at hnot'
  have hfst : firstProjection.base ((multiProjection (q + 1) n a).base x) ∉ chartOpen k 0 := by
    intro hfst
    apply hnot'
    refine ⟨hfst, ?_⟩
    rw [hsnd]
    exact point_mem_chart _
  have hinf := eq_infinityPoint_of_not_mem_chart _ hfst
  have hsnd' : secondProjection.base ((multiProjection (q + 1) n a).base x) = infinityPoint := by
    rw [← hgg, graph_snd, hgg, hinf, projectivePowerMorphism_infinityPoint (q + 1) (Nat.succ_pos q)]
  have h1 : FrobeniusProjectivePoints.point (a i ^ (q + 1)) ∈ chartOpen k 0 := point_mem_chart _
  rw [← hsnd, hsnd'] at h1
  exact infinityPoint_not_mem_chart h1

theorem graphStrict_fiberStrict_disjoint' (i : Fin n) :
    Disjoint (Set.range (graphStrictι (q + 1) n a).base)
      (Set.range (fiberStrictι (q + 1) n a i).base) := by
  rw [Set.disjoint_left]
  intro x hB hF
  exact graphStrict_fiberStrict_disjoint q n a i x hB hF

end KltDP.Examples.FrobeniusGraphFiberDisjointSPn

namespace KltDP.Examples

open FrobeniusMultiCentreGraphFiber FrobeniusGraphFiberDisjointSPn

/-- Bundle: `B ∩ F_i = ∅` on `S_{p,n}` for every `i`, over any field of characteristic `p = q + 1`. -/
theorem sPn_graph_fiber_disjoint (k : Type u) [Field k] (q n : ℕ) [Fact (q + 1).Prime]
    [CharP k (q + 1)] (a : Fin n → k) :
    ∀ i : Fin n, Disjoint (Set.range (graphStrictι (q + 1) n a).base)
      (Set.range (fiberStrictι (q + 1) n a i).base) :=
  fun i => graphStrict_fiberStrict_disjoint' q n a i

/-- The bundle has exactly one universe parameter. -/
theorem sPn_graph_fiber_disjoint_universe_check (k : Type u) [Field k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) : True := by
  have _ := sPn_graph_fiber_disjoint.{u} k q n a
  trivial

end KltDP.Examples
