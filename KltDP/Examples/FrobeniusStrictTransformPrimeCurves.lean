import KltDP.Geometry.PrimeCurveOfClosedImmersion
import KltDP.Examples.FrobeniusStageSurface
import KltDP.Examples.FrobeniusExceptionalFinalConfiguration
import KltDP.Examples.FrobeniusPreviousStrictIsoProjectiveLine
import KltDP.Examples.FrobeniusGlobalStrictTransform
import KltDP.Examples.FrobeniusFiberClosure
import KltDP.Examples.FrobeniusFiberPicard
import KltDP.Examples.FrobeniusUnaffectedFibers
import KltDP.Examples.FrobeniusGraphPicardClassIntegral

/-!
# The strict transforms of the top stage as prime curves (BRIEF14, item 2)

On the stage-`(n+1)` surface `stageSurface (n + 1) hproj` of the origin contact tower, the three
families of curves of the manuscript's Prop. 10.1 table other than the newest exceptional curve
(accepted `exceptionalPrimeCurve`) are realised as `PrimeCurve`s:

* `oldExceptionalPrimeCurve n hproj j h` (`j + 2 ≤ n + 1`): the older exceptional curve `C_j`,
  embedded by the accepted closed immersion `finalOldMap projectiveProductInitial (n+1) j h`, with
  the accepted isomorphism `C_j ≅ P¹` (`previousStrictIsoProjectiveLine`), through the generic
  `primeCurveOfIsoProjectiveLine`;
* `graphStrictPrimeCurve n hproj m`: the strict transform `B` of the Frobenius graph, the accepted
  integral closed subscheme `strictTransform (n+1) (m + (n+1))` (residual exponent `m`);
* `fiberStrictPrimeCurve n hproj`: the strict transform `F̃` of the fibre `u = 0`, the accepted
  integral closed subscheme `liftedFiberClosure projectiveProductInitial (n+1)`.

For `B` and `F̃` no isomorphism with `P¹` is accepted; dimension one is obtained from the generic
`primeCurve`: the range is not the whole stage — it lies over the graph (resp. the horizontal fibre)
of stage `0`, a closed curve isomorphic to `P¹` which cannot fill the two-dimensional product
(`range_ne_univ_of_iso_projectiveLine`), and every point of the punctured base off it lifts to the
stage through the accepted complement isomorphism (`exists_point_projection_not_mem`) — and the
curve has two distinct points (images of two points of the affine line through the accepted open
charts `parameterToGraphPuncture ≫ wholeGraphToStrictTransform` resp. `fiberResidualToClosure`).

The isomorphisms `B ≅ P¹` and `F̃ ≅ P¹` (the blowdown restricted to the strict transform is an
isomorphism onto the graph resp. the fibre) are **not** proved here; they need the chart analysis
of lane F's `strictToFiber_isIso` for these two curves (recorded in `F29_INTERSECTION_TABLE.md`).

Bundle: `f29_strict_transform_prime_curves`, with a universe check.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStrictTransformPrimeCurves

open KltDP.Geometry KltDP.Geometry.PrimeCurveOfClosedImmersion
open FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusStageDimension
open FrobeniusStageSurface FrobeniusExceptionalFinalConfiguration FrobeniusGlobalExceptionalSuccessor
open FrobeniusPreviousStrictIsoProjectiveLine FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformClosure FrobeniusFiberClosure FrobeniusFiberPicard
open FrobeniusGraphClosed FrobeniusProjectivePoints FrobeniusGraphPicardClassZeroFiber
open FrobeniusStageComplement.PlaneChartedScheme

variable {k : Type u} [Field k]

/-- The base of the origin tower is integral (accepted), as a local instance. -/
local instance initial_isIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- The same accepted instance, stated on the projective product. -/
local instance product_isIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

section StageZero

/-- No closed curve isomorphic to `P¹` fills the two-dimensional stage `0`. -/
theorem range_ne_univ_of_iso_projectiveLine {Y : Scheme.{u}} (f : Y ⟶ projectiveProduct k)
    [IsClosedImmersion f] (e : Y ≅ projectiveSpace k 1) : Set.range f.base ≠ Set.univ := by
  intro h
  have h1 : topologicalKrullDim (Set.range f.base) = 1 := range_topologicalKrullDim_of_iso f e
  have h2 : topologicalKrullDim (Set.range f.base) = 2 := by
    rw [h]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.Set.univ (projectiveProduct k)).isHomeomorph).trans
      projectiveProduct_topologicalKrullDim
  rw [h1] at h2
  exact absurd h2 (by norm_num)

/-- The graph `B ⊆ P¹ × P¹` does not fill the product. -/
theorem range_graphι_ne_univ (p : ℕ) : Set.range (graphι (k := k) p).base ≠ Set.univ :=
  range_ne_univ_of_iso_projectiveLine (graphι p) (graphIsoProjectiveLine p)

/-- The horizontal fibre `F ⊆ P¹ × P¹` does not fill the product. -/
theorem range_horizontalFiberMorphism_ne_univ :
    Set.range (horizontalFiberMorphism (0 : k)).base ≠ Set.univ :=
  range_ne_univ_of_iso_projectiveLine (horizontalFiberMorphism 0) (Iso.refl _)

end StageZero

section Lift

/-- Every closed set `Z ≠ P¹ × P¹` misses a point of the punctured base, which lifts to a point of
stage `N` whose projection is off `Z` (through the accepted complement isomorphism). -/
theorem exists_point_projection_not_mem (N : ℕ)
    (Z : Set (projectiveProductInitial (k := k)).carrier) (hZ : IsClosed Z)
    (hne : Z ≠ Set.univ) :
    ∃ y : projectiveContactStage (k := k) N, (projectiveContactProjection N).base y ∉ Z := by
  have hpunct : ((initialPuncture (projectiveProductInitial (k := k)) :
      Set (projectiveProductInitial (k := k)).carrier)).Nonempty := by
    obtain ⟨g⟩ := graphPuncture_nonempty (k := k) 1
    exact ⟨(graphι 1).base g.1, g.2⟩
  have hZc : (Zᶜ).Nonempty := Set.nonempty_compl.mpr hne
  obtain ⟨z, hz1, hz2⟩ := nonempty_preirreducible_inter
    (initialPuncture (projectiveProductInitial (k := k))).isOpen hZ.isOpen_compl hpunct hZc
  have hz : z ∈ Set.range (initialPuncture (projectiveProductInitial (k := k))).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hz1
  obtain ⟨w, hw⟩ := hz
  refine ⟨(stagePuncture (projectiveProductInitial (k := k)) N).ι.base
    ((stageComplementIso (projectiveProductInitial (k := k)) N).inv.base w), ?_⟩
  have hcomp : (stageComplementIso (projectiveProductInitial (k := k)) N).inv ≫
      (stagePuncture (projectiveProductInitial (k := k)) N).ι ≫ projectiveContactProjection N =
        (initialPuncture (projectiveProductInitial (k := k))).ι := by
    rw [projectiveContactProjection, ← stageComplementIso_hom_ι, Iso.inv_hom_id_assoc]
  have h := congrArg (fun f => f.base w) hcomp
  simp only [Scheme.comp_base_apply] at h
  have hz2' : (initialPuncture (projectiveProductInitial (k := k))).ι.base w ∉ Z := by
    intro hmem
    apply hz2
    rw [← hw]
    exact hmem
  rw [h]
  exact hz2'

end Lift

section Graph

/-- The strict transform of the graph lies over the graph. -/
theorem range_strictTransformι_subset (N p : ℕ) :
    Set.range (strictTransformι (k := k) N p).base ⊆
      (projectiveContactProjection N).base ⁻¹' Set.range (graphι (k := k) p).base := by
  rw [range_strictTransformι]
  refine closure_minimal ?_
    ((graphι p).isClosedEmbedding.isClosed_range.preimage (projectiveContactProjection N).continuous)
  rintro _ ⟨g, rfl⟩
  have h := congrArg (fun f => f.base g) (wholeGraphLift_projection (k := k) N p)
  simp only [Scheme.comp_base_apply] at h
  exact ⟨(graphPuncture p).ι.base g, h.symm⟩

/-- The strict transform of the graph does not fill the stage. -/
theorem range_strictTransformι_ne_univ (N p : ℕ) :
    Set.range (strictTransformι (k := k) N p).base ≠ Set.univ := by
  obtain ⟨y, hy⟩ := exists_point_projection_not_mem N (Set.range (graphι (k := k) p).base)
    (graphι p).isClosedEmbedding.isClosed_range (range_graphι_ne_univ p)
  intro h
  apply hy
  have hy' : y ∈ Set.range (strictTransformι (k := k) N p).base := by
    rw [h]
    exact Set.mem_univ y
  exact range_strictTransformι_subset N p hy'

/-- Two distinct points of the strict transform of the graph: the images of two points of the
punctured parameter line through the accepted open charts. -/
theorem strictTransform_exists_pair_ne (N p : ℕ) :
    ∃ x y : strictTransform (k := k) N p, x ≠ y := by
  obtain ⟨s, t, hs, ht, hst⟩ := exists_pair_ne_basicOpen_X k
  have hs' : s ∈ Set.range (parameterPuncture (k := k)).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hs
  have ht' : t ∈ Set.range (parameterPuncture (k := k)).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact ht
  obtain ⟨s', rfl⟩ := hs'
  obtain ⟨t', rfl⟩ := ht'
  have heq : (parameterToGraphPuncture (k := k) p ≫ wholeGraphToStrictTransform N p) ≫
      strictTransformι N p ≫ projectiveContactProjection N =
        parameterToGraphPuncture p ≫ (graphPuncture p).ι ≫ graphι p := by
    simp only [Category.assoc, wholeGraphToStrictTransform_ι_assoc, wholeGraphLift_projection]
  have hinj : Function.Injective ((parameterToGraphPuncture (k := k) p ≫
      wholeGraphToStrictTransform N p) ≫ strictTransformι N p ≫
        projectiveContactProjection N).base := by
    rw [heq]
    intro x y hxy
    simp only [Scheme.comp_base_apply] at hxy
    exact (parameterToGraphPuncture p).isOpenEmbedding.injective
      ((graphPuncture p).ι.isOpenEmbedding.injective ((graphι p).isClosedEmbedding.injective hxy))
  refine ⟨(parameterToGraphPuncture p ≫ wholeGraphToStrictTransform N p).base s',
    (parameterToGraphPuncture p ≫ wholeGraphToStrictTransform N p).base t', fun h => hst ?_⟩
  exact congrArg (parameterPuncture (k := k)).ι.base (injective_of_comp _ _ hinj h)

end Graph

section Fiber

/-- At stage `0` the strict fibre closure is the horizontal fibre `F = {u = 0}` (accepted
`fiberStrictIdeal_zero`), so the chart fibre lies in `F`. -/
theorem range_fiberResidual_zero_subset :
    Set.range (fiberResidual (projectiveProductInitial (k := k)) 0).base ⊆
      Set.range (horizontalFiberMorphism (0 : k)).base := by
  have h1 : Set.range (fiberResidual (projectiveProductInitial (k := k)) 0).base ⊆
      Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) 0).base := by
    rw [range_fiberClosureInclusion_eq_residual]
    exact subset_closure
  have h2 : Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) 0).base =
      Set.range (horizontalFiberMorphism (0 : k)).base := by
    change Set.range (liftedFiberClosureIdeal (projectiveProductInitial (k := k)) 0).gluedTo.base = _
    rw [Scheme.IdealSheafData.range_gluedTo, fiberStrictIdeal_zero, Scheme.Hom.support_ker]
    exact (horizontalFiberMorphism (0 : k)).isClosedEmbedding.isClosed_range.closure_eq
  rw [h2] at h1
  exact h1

/-- The strict fibre of every stage lies over the horizontal fibre of stage `0`. -/
theorem range_fiberClosureInclusion_subset (N : ℕ) :
    Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) N).base ⊆
      (projectiveContactProjection N).base ⁻¹'
        Set.range (horizontalFiberMorphism (0 : k)).base := by
  rw [range_fiberClosureInclusion_eq_residual]
  refine closure_minimal ?_
    ((horizontalFiberMorphism (0 : k)).isClosedEmbedding.isClosed_range.preimage
      (projectiveContactProjection N).continuous)
  rintro _ ⟨s, rfl⟩
  have hres : fiberResidual (projectiveProductInitial (k := k)) N ≫ projectiveContactProjection N =
      fiberCurve ≫ (projectiveProductInitial (k := k)).chart :=
    fiberResidual_toInitial (projectiveProductInitial (k := k)) N
  have h := congrArg (fun f => f.base s) hres
  simp only [Scheme.comp_base_apply] at h
  have h0 : (fiberResidual (projectiveProductInitial (k := k)) 0).base s =
      (projectiveProductInitial (k := k)).chart.base (fiberCurve.base s) := by
    change (fiberCurve ≫ ((projectiveProductInitial (k := k)).stage 0).chart).base s = _
    rw [Scheme.comp_base_apply]
    rfl
  show (projectiveContactProjection N).base
    ((fiberResidual (projectiveProductInitial (k := k)) N).base s) ∈
      Set.range (horizontalFiberMorphism (0 : k)).base
  rw [h]
  exact range_fiberResidual_zero_subset (k := k) ⟨s, h0⟩

/-- The strict fibre does not fill the stage. -/
theorem range_fiberClosureInclusion_ne_univ (N : ℕ) :
    Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) N).base ≠ Set.univ := by
  obtain ⟨y, hy⟩ := exists_point_projection_not_mem N
    (Set.range (horizontalFiberMorphism (0 : k)).base)
    (horizontalFiberMorphism (0 : k)).isClosedEmbedding.isClosed_range
    range_horizontalFiberMorphism_ne_univ
  intro h
  apply hy
  have hy' : y ∈ Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) N).base := by
    rw [h]
    exact Set.mem_univ y
  exact range_fiberClosureInclusion_subset N hy'

/-- Two distinct points of the strict fibre: the images of two points of the affine line through
the accepted open chart `fiberResidualToClosure`. -/
theorem liftedFiberClosure_exists_pair_ne (N : ℕ) :
    ∃ x y : liftedFiberClosure (projectiveProductInitial (k := k)) N, x ≠ y := by
  obtain ⟨s, t, hst⟩ := exists_pair_ne_polynomialSpec k
  exact ⟨(fiberResidualToClosure (projectiveProductInitial (k := k)) N).base s,
    (fiberResidualToClosure (projectiveProductInitial (k := k)) N).base t,
    fun h => hst
      ((fiberResidualToClosure (projectiveProductInitial (k := k)) N).isOpenEmbedding.injective h)⟩

end Fiber

section PrimeCurves

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`C_j ≅ P¹`**: the older exceptional curve `C_j` is isomorphic to the projective line
(accepted `previousStrictIsoProjectiveLine`, restated on the origin tower). -/
abbrev oldExceptionalIsoProjectiveLine (j : ℕ) :
    previousStrictTransform ((projectiveProductInitial (k := k)).stage j) ≅ projectiveSpace k 1 :=
  previousStrictIsoProjectiveLine ((projectiveProductInitial (k := k)).stage j)

/-- **The older exceptional curve `C_j` (`j + 2 ≤ n + 1`) as a prime curve of stage `n+1`**, the
range of the accepted closed immersion `finalOldMap`. -/
def oldExceptionalPrimeCurve (j : ℕ) (h : j + 2 ≤ n + 1) :
    (stageSurface (n + 1) hproj).PrimeCurve :=
  primeCurveOfIsoProjectiveLine (stageSurface (n + 1) hproj)
    (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) (oldExceptionalIsoProjectiveLine j)

@[simp] theorem coe_oldExceptionalPrimeCurve (j : ℕ) (h : j + 2 ≤ n + 1) :
    (oldExceptionalPrimeCurve n hproj j h : Set (stageSurface (n + 1) hproj).toScheme) =
      Set.range (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h).base := rfl

/-- **The strict transform `B` of the graph as a prime curve of stage `n+1`** (residual exponent
`m`, i.e. Frobenius exponent `p = m + (n + 1)`, the range of the accepted integrality
`strictTransform_isIntegral`). -/
def graphStrictPrimeCurve (m : ℕ) : (stageSurface (n + 1) hproj).PrimeCurve :=
  primeCurve (stageSurface (n + 1) hproj) (strictTransformι (n + 1) (m + (n + 1)))
    (range_strictTransformι_ne_univ (n + 1) (m + (n + 1)))
    (strictTransform_exists_pair_ne (n + 1) (m + (n + 1)))

@[simp] theorem coe_graphStrictPrimeCurve (m : ℕ) :
    (graphStrictPrimeCurve n hproj m : Set (stageSurface (n + 1) hproj).toScheme) =
      Set.range (strictTransformι (k := k) (n + 1) (m + (n + 1))).base := rfl

/-- **The strict transform `F̃` of the fibre as a prime curve of stage `n+1`.** -/
def fiberStrictPrimeCurve : (stageSurface (n + 1) hproj).PrimeCurve :=
  primeCurve (stageSurface (n + 1) hproj)
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
    (range_fiberClosureInclusion_ne_univ (n + 1)) (liftedFiberClosure_exists_pair_ne (n + 1))

@[simp] theorem coe_fiberStrictPrimeCurve :
    (fiberStrictPrimeCurve n hproj : Set (stageSurface (n + 1) hproj).toScheme) =
      Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)).base := rfl

end PrimeCurves

end KltDP.Examples.FrobeniusStrictTransformPrimeCurves

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStageSurface
  FrobeniusExceptionalFinalConfiguration FrobeniusGlobalExceptionalSuccessor
  FrobeniusGlobalStrictTransform FrobeniusFiberClosure FrobeniusStrictTransformPrimeCurves

/-- **The strict transforms of the top stage are prime curves.** On `stageSurface (n+1) hproj`:
the strict transform `B` of the graph (for every residual exponent `m`), the strict transform `F̃`
of the fibre, and every older exceptional curve `C_j` (`j + 2 ≤ n + 1`, with `C_j ≅ P¹`) are the
carriers of prime curves. -/
theorem f29_strict_transform_prime_curves (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) :
    (∀ m : ℕ, ∃ C : (stageSurface (n + 1) hproj).PrimeCurve,
      (C : Set (stageSurface (n + 1) hproj).toScheme) =
        Set.range (strictTransformι (k := k) (n + 1) (m + (n + 1))).base) ∧
    (∃ C : (stageSurface (n + 1) hproj).PrimeCurve,
      (C : Set (stageSurface (n + 1) hproj).toScheme) =
        Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)).base) ∧
    (∀ (j : ℕ) (h : j + 2 ≤ n + 1), ∃ C : (stageSurface (n + 1) hproj).PrimeCurve,
      (C : Set (stageSurface (n + 1) hproj).toScheme) =
        Set.range (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h).base ∧
      Nonempty (previousStrictTransform ((projectiveProductInitial (k := k)).stage j) ≅
        projectiveSpace k 1)) :=
  ⟨fun m => ⟨graphStrictPrimeCurve n hproj m, rfl⟩,
    ⟨fiberStrictPrimeCurve n hproj, rfl⟩,
    fun j h => ⟨oldExceptionalPrimeCurve n hproj j h, rfl, ⟨oldExceptionalIsoProjectiveLine j⟩⟩⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_strict_transform_prime_curves_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) : True := by
  have _ := f29_strict_transform_prime_curves.{u} k n hproj
  trivial

end KltDP.Examples
