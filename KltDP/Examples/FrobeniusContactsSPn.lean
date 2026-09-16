import KltDP.Examples.FrobeniusMultiCentreFiberContacts

/-!
# Bundle: contacts of the strict transforms with the exceptional curves on `S_{p,n}`

`sPn_contacts` collects, for an algebraically closed field `k` of characteristic `p = q + 1` (prime)
and an injective selection `a : Fin n → k`, the facts proved about the strict transform
`B = graphStrict p n a` of the graph and the exceptional curves `C_{ij} = E_{i, inl j}`,
`P_i = E_{i, inr}` of the multi-centre surface `S_{p,n} = multiSurface p n a`, together with the
tower-level statements on the `n` translated towers `T_i` that feed them:

1. compatibility of the schematic images with the isomorphism opens: the lift of the punctured graph
   of `S_{p,n}` followed by the tower projection `τ_i` is the whole-graph lift on `T_i`; `τ_i` maps
   `B` into the whole-graph strict transform of `T_i`, which is the accepted local closure; `τ_i` is
   an isomorphism over the complement of the other centres, and over it the lifted punctured graphs
   correspond;
2. contacts of `B` on `S_{p,n}`: `B ∩ C_{ij} = ∅` for every `i`, `j`, and `B ∩ P_i ≠ ∅` for every `i`;
3. on every tower `T_i`: the whole-graph strict transform is integral, its terminal point lies on
   `P_i`, and it misses every `C_{ij}`;
4. on every tower `T_i`: the strict fibre `F̃_i` (closure of the punctured tangent line in the
   selected chart) is a closed integral curve, its centre point lies on `P_i`, and it misses every
   `C_{ij}`;
5. the fibres on `S_{p,n}`: the lift of the punctured horizontal fibre followed by `τ_i` is the
   whole-fibre lift on `T_i`, whose strict transform is the generic strict fibre; `F_i ∩ C_{ij} = ∅`
   and `F_i ∩ P_i ≠ ∅` for every `i`, `j`.

Not proved (see `F29_CONTACTS.md`): single-point intersections and `B ∩ F_i = ∅`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusStrictTransformClosure
  FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber FrobeniusAdaptedStrictTransform
  FrobeniusClosureContact FrobeniusFiberClosure FrobeniusMultiCentreGraphContacts
  FrobeniusMultiCentreGraphNewest FrobeniusAdaptedFiberTransform FrobeniusMultiCentreFiberContacts

/-- The contacts of `B` with the exceptional curves of `S_{p,n}`, with the tower-level statements. -/
theorem sPn_contacts (k : Type u) [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k)
    (ha : Function.Injective a) :
    -- (1) compatibility of the schematic images with the isomorphism opens
    (∀ i : Fin n, graphLift (q + 1) n a ≫ towerProjection (q + 1) n a i =
        punctureInclusion q n a i ≫ (towerGraph q n a i).lift (q + 1)) ∧
    (∀ (i : Fin n) (x : multiSurface (q + 1) n a), x ∈ Set.range (graphStrictι (q + 1) n a).base →
        (towerProjection (q + 1) n a i).base x ∈
          Set.range (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0).base) ∧
    (∀ i : Fin n, IsIso (towerProjection (q + 1) n a i ∣_ isoOpen q n a i)) ∧
    (∀ i : Fin n,
        (isoMap q n a i).base ⁻¹' Set.range ((towerGraph q n a i).lift (q + 1)).base ⊆
          (isoPreimage q n a i).ι.base ⁻¹' Set.range (graphLift (q + 1) n a).base) ∧
    -- (2) contacts of `B` on `S_{p,n}`
    (∀ (i : Fin n) (j : Fin q),
        Disjoint (Set.range (graphStrictι (q + 1) n a).base)
          (exceptionalSupport q n a i (Sum.inl j))) ∧
    (∀ i : Fin n,
        (Set.range (graphStrictι (q + 1) n a).base ∩
          exceptionalSupport q n a i (Sum.inr PUnit.unit)).Nonempty) ∧
    -- (3) the whole-graph strict transform on every tower
    (∀ i : Fin n, IsIntegral ((towerGraph q n a i).strict (q + 1))) ∧
    (∀ i : Fin n, (towerGraph q n a i).strictι (q + 1) =
        ((towerGraph q n a i).strictIsoLocal (q + 1) 0 (by omega)).hom ≫
          closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0) ∧
    (∀ i : Fin n,
        (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0).base
            (closureContactPoint (translatedInitial (q + 1) (a i)) (q + 1) 0) ∈
          finalSupport (translatedInitial (q + 1) (a i)) q
            (Sum.inr PUnit.unit : FinalIndex.{0} q)) ∧
    (∀ (i : Fin n) (j : Fin q),
        Disjoint (Set.range (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0).base)
          (finalSupport (translatedInitial (q + 1) (a i)) q (Sum.inl j : FinalIndex.{0} q))) ∧
    -- (4) the strict fibre on every tower
    (∀ i : Fin n, IsClosedImmersion (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))) ∧
    (∀ i : Fin n, IsIntegral (liftedFiberClosure (translatedInitial (q + 1) (a i)) (q + 1))) ∧
    (∀ i : Fin n,
        (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)).base
            (fiberContactPoint (translatedInitial (q + 1) (a i)) (q + 1)) ∈
          finalSupport (translatedInitial (q + 1) (a i)) q
            (Sum.inr PUnit.unit : FinalIndex.{0} q)) ∧
    (∀ (i : Fin n) (j : Fin q),
        Disjoint (Set.range (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)).base)
          (finalSupport (translatedInitial (q + 1) (a i)) q (Sum.inl j : FinalIndex.{0} q))) ∧
    -- (5) the fibres on `S_{p,n}`: compatibility with the towers and the contacts
    (∀ i : Fin n, fiberLift (q + 1) n a i ≫ towerProjection (q + 1) n a i =
        fiberPunctureInclusion q n a i ≫ (towerFiber q n a i).lift (q + 1)) ∧
    (∀ i : Fin n, (towerFiber q n a i).strictι (q + 1) =
        ((towerFiber q n a i).strictIsoLocal (q + 1)).hom ≫
          fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)) ∧
    (∀ (i : Fin n) (j : Fin q),
        Disjoint (Set.range (fiberStrictι (q + 1) n a i).base)
          (exceptionalSupport q n a i (Sum.inl j))) ∧
    (∀ i : Fin n,
        (Set.range (fiberStrictι (q + 1) n a i).base ∩
          exceptionalSupport q n a i (Sum.inr PUnit.unit)).Nonempty) :=
  ⟨fun i => graphLift_towerProjection q n a i,
    fun i x hx => graphStrict_projection_mem_towerStrict q n a i x hx,
    fun i => isoOpen_restrict_isIso q n a i,
    fun i => isoMap_preimage_lift_subset q n a i,
    fun i j => graphStrict_disjoint_exceptional_same q n a i j,
    fun i => graphStrict_meets_newest q n a ha i,
    fun i => (towerGraph q n a i).strict_isIntegral (q + 1) 0 (by omega),
    fun i => ((towerGraph q n a i).strictIsoLocal_hom_ι (q + 1) 0 (by omega)).symm,
    fun i => closure_terminal_mem_newestFiber (translatedInitial (q + 1) (a i)) q,
    fun i j => closure_disjoint_finalSupport (translatedInitial (q + 1) (a i)) q 0 j,
    fun i => fiberClosureInclusion_isClosedImmersion (translatedInitial (q + 1) (a i)) (q + 1),
    fun i => liftedFiberClosure_isIntegral (translatedInitial (q + 1) (a i)) (q + 1),
    fun i => fiberClosure_terminal_mem_newestFiber (translatedInitial (q + 1) (a i)) q,
    fun i j => fiberClosure_disjoint_finalSupport (translatedInitial (q + 1) (a i)) q j,
    fun i => fiberLift_towerProjection q n a i,
    fun i => ((towerFiber q n a i).strictIsoLocal_hom_ι (q + 1)).symm,
    fun i j => fiberStrict_disjoint_exceptional_same q n a i j,
    fun i => fiberStrict_meets_newest q n a ha i⟩

/-- The bundle has exactly one universe parameter. -/
theorem sPn_contacts_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k)
    (ha : Function.Injective a) : True := by
  have _ := sPn_contacts.{u} k q n a ha
  trivial

end KltDP.Examples
