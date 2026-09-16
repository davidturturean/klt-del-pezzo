import KltDP.Examples.FrobeniusMultiCentreGraphFiber

/-!
# Bundle: the strict transforms `B` and `F_i` in `S_{p,n}`

`sPn_graph_and_fibers` collects, for an algebraically closed field `k` of characteristic `p` (`p`
prime) and an injective selection `a : Fin n → k`, the facts proved about the strict transform
`B = graphStrict p n a` of the graph and the strict transforms `F_i = fiberStrict p n a i` of the
tangent fibres `y = (a i)^p` in the multi-centre surface `S_{p,n} = multiSurface p n a`:

1. `B` and every `F_i` are closed subschemes of `S_{p,n}`, reduced and integral;
2. the punctured graph and punctured fibres factor through them, and their lifts are literal
   pullbacks along the projection to `P¹ ×_k P¹`;
3. every point of `B` projects into the graph and every point of `F_i` into its fibre;
4. distinct `F_i`, `F_j` are disjoint, and `F_i` is disjoint from every exceptional curve of a
   tower `j ≠ i` (`p = q + 1` for the exceptional indexing).

Not proved (see `F29_GRAPH_FIBERS.md`): the contacts of `B` and `F_i` with the exceptional curves
of their own tower, `B ∩ F_i = ∅`, single-point intersections, and `B ≅ P¹`, `F_i ≅ P¹`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed
  FrobeniusGraphPicardClassZeroFiber FrobeniusExceptionalFinalConfiguration
  FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber

/-- The strict transforms of the graph and the tangent fibres in `S_{p,n}`: the clauses proved. -/
theorem sPn_graph_and_fibers (k : Type u) [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k)
    (ha : Function.Injective a) :
    -- (1) closed integral curves
    IsClosedImmersion (graphStrictι (q + 1) n a) ∧
    IsIntegral (graphStrict (q + 1) n a) ∧
    (∀ i : Fin n, IsClosedImmersion (fiberStrictι (q + 1) n a i)) ∧
    (∀ i : Fin n, IsIntegral (fiberStrict (q + 1) n a i)) ∧
    -- (2) the punctured curves factor through them; the lifts are pullbacks
    (puncturedGraphToStrict (q + 1) n a ≫ graphStrictι (q + 1) n a = graphLift (q + 1) n a) ∧
    IsPullback (graphLift (q + 1) n a) (𝟙 _) (multiProjection (q + 1) n a)
      (puncturedGraph (q + 1) n a) ∧
    (∀ i : Fin n, puncturedFiberToStrict (q + 1) n a i ≫ fiberStrictι (q + 1) n a i =
        fiberLift (q + 1) n a i) ∧
    (∀ i : Fin n, IsPullback (fiberLift (q + 1) n a i) (𝟙 _) (multiProjection (q + 1) n a)
        (puncturedFiber (q + 1) n a i)) ∧
    -- (3) supports project into the graph and the fibres
    (∀ x : graphStrict (q + 1) n a,
        (multiProjection (q + 1) n a).base ((graphStrictι (q + 1) n a).base x) ∈
          Set.range (graphι (k := k) (q + 1)).base) ∧
    (∀ (i : Fin n) (x : fiberStrict (q + 1) n a i),
        (multiProjection (q + 1) n a).base ((fiberStrictι (q + 1) n a i).base x) ∈
          Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base) ∧
    -- (4) disjointness
    (∀ i j : Fin n, i ≠ j →
        Disjoint (Set.range (fiberStrictι (q + 1) n a i).base)
          (Set.range (fiberStrictι (q + 1) n a j).base)) ∧
    (∀ (i j : Fin n) (idx : FinalIndex.{0} q), i ≠ j →
        Disjoint (Set.range (fiberStrictι (q + 1) n a i).base) (exceptionalSupport q n a j idx)) :=
  ⟨graphStrictι_isClosedImmersion (q + 1) n a,
    graphStrict_isIntegral (q + 1) n a,
    fun i => fiberStrictι_isClosedImmersion (q + 1) n a i,
    fun i => fiberStrict_isIntegral (q + 1) n a i,
    puncturedGraphToStrict_ι (q + 1) n a,
    graphLift_isPullback (q + 1) n a,
    fun i => puncturedFiberToStrict_ι (q + 1) n a i,
    fun i => fiberLift_isPullback (q + 1) n a i,
    fun x => graphStrict_projection_mem (q + 1) n a x,
    fun i x => fiberStrict_projection_mem (q + 1) n a i x,
    fun _ _ hij => fiberStrict_disjoint (q + 1) n a ha hij,
    fun _ _ idx hij => fiberStrict_disjoint_exceptional q n a ha hij idx⟩

/-- The bundle has exactly one universe parameter. -/
theorem sPn_graph_and_fibers_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k)
    (ha : Function.Injective a) : True := by
  have _ := sPn_graph_and_fibers.{u} k q n a ha
  trivial

end KltDP.Examples
