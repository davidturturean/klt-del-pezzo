import KltDP.Examples.FrobeniusContactBlowupsF29
import KltDP.Examples.FrobeniusMultiCentreChainTransversal
import KltDP.Examples.FrobeniusMultiCentreLocusPicard
import KltDP.Examples.FrobeniusMultiCentreIntegral
import KltDP.Examples.FrobeniusStageZeroProjective
import KltDP.Examples.FrobeniusStageNoetherianFiniteType
import KltDP.Examples.FrobeniusStrictTransformClassesFull
import KltDP.Examples.FrobeniusFiberZeroClass
import KltDP.Examples.FrobeniusTowerCartierIdentity
import KltDP.Examples.FrobeniusExceptionalCartierPicard
import KltDP.Examples.FrobeniusTransversalContactsStrict
import KltDP.Examples.FrobeniusGraphFiberDisjointSPn
import KltDP.Examples.FrobeniusExceptionalLocusCover
import KltDP.Examples.FrobeniusPreviousStrictIsoProjectiveLine

/-!
# F29 completion bundle: the contact towers, the surface `S_{p,n}` and its exceptional configuration

`f29_contact_blowups_full` collects, for an algebraically closed field `k` of characteristic
`p = q + 1` (prime) and an injective selection `a : Fin n → k` of graph points `(a_i, a_i^p)`, every
clause of obligation F29 (manuscript Proposition 10.1, `prop:frobenius-family`, lines 2892–2954) that
is proved for the actual objects — the multi-centre surface `S_{p,n} = multiSurface (q+1) n a`, its
`n` translated contact towers `T_i = translatedInitial (q+1) (a i)`, and (for the class table and the
Cartier fibre identity) the origin contact tower `projectiveContactStage`:

1. **construction**: `S_{p,n} → P¹ ×_k P¹` proper, `S_{p,n}` proper and smooth of relative dimension
   two over `k`, normal, integral, of dimension two; every stage of every tower proper, smooth,
   normal, integral, of dimension two; stage `0` projective; `S_{p,n}` is a `NormalProjectiveSurface`
   given a projective embedding `hproj` (the only remaining hypothesis of that kind); the tower
   projections `τ_i`, the isomorphism loci, distinct centres;
2. **exceptional configuration**: the `n·p` curves `C_{ij}`, `P_i` are closed subschemes, each
   `≅ P¹`, over the centres, closed, clusters disjoint, non-adjacent curves disjoint, adjacent curves
   meeting in exactly one point, transversally (`SinglePoints`, `TowerTransversal`);
3. **strict transforms** `B` and `F_i`: closed integral curves, literal pullbacks of the punctured
   graph/fibres, `B ∩ P_i` and `F_i ∩ P_i` single points with contact length one on the stalks of `B`
   resp. `F_i`, `B ∩ F_i = ∅`, `B ∩ C_{ij} = ∅`, `F_i ∩ C_{ij} = ∅`, `F_i ∩ F_j = ∅`, `F_i` disjoint
   from the other clusters;
4. **the complete scheme-theoretic fibres** of `S_{p,n}` over `y = a_i^p` (closed, pullbacks, support
   `F_i ∪ ⋃_j C_{ij} ∪ P_i`, disjoint from the other clusters) and the **unaffected fibres** over the
   other heights (`≅ P¹`), together with the per-tower unaffected fibres `y = c`, `x = c`;
5. **the class table** on the origin tower (`k` any field): `B = p·a + b − Σ E_j`,
   `C_j = E_j − E_{j+1}`, `F = π^*b − Σ E_j` with `F_0 = b`, `F_{n+1} = π^*F_n − E_n`, `P = E_last`;
6. **the Cartier fibre identity** on the origin tower: `π^*(y = 0) = F̃ + Σ (j+1)·C_j + (N+1)·P` as
   effective Cartier divisors, their classes being the Picard classes of 5, and the Picard form
   `π^*b = F̃ + Σ (j+1)·C_j + (N+1)·P`;
7. **Picard groups of the exceptional chains**: `Pic(C_{i1} ∪ ⋯ ∪ C_{iq} ∪ P_i) ≃ ℤ^{q+1}` on
   `S_{p,n}` and on each tower, and `Pic(exceptional locus of S_{p,n}) ≃ ℤ^{n(q+1)}` (lane A1's
   `locusPicardEquiv` with both hypotheses discharged).

The seven clause groups are the transparent `Prop`s `Construction`, `Configuration`,
`StrictTransforms`, `Fibres`, `ClassTable`, `CartierIdentity`, `ChainPicard` (each an `abbrev` whose body
is the explicit conjunction of clauses, proved by the theorem of the same name in lower case); the
bundle `f29_contact_blowups_full` is their conjunction, so that each group elaborates as a separate
command.

Not part of this bundle (not proved): the Cartier fibre identity and the class table *on `S_{p,n}`*
(they are proved on the origin tower `projectiveProductInitial` only; the clusters of `S_{p,n}` are
the translated towers, and no transport between the two is available), the numerical intersection
table on `S_{p,n}`, canonical-class statements (F30), and projectivity of the stages `≥ 1` of the
translated towers and of `S_{p,n}` (hypothesis `hproj`). See `F29_ACCEPTANCE_DRAFT.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusContactBlowupsF29Full

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusGraphPicardClassZeroFiber
  FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts
  FrobeniusContactTowerSelectedPoint FrobeniusStageComplement.PlaneChartedScheme
  FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional
  FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreGraphContacts
  FrobeniusMultiCentreFiberContacts FrobeniusTransversalContactsStrict FrobeniusSpecialFiberSPn
  FrobeniusExceptionalLocusCover FrobeniusUnaffectedFibers FrobeniusMultiCentreChainPicard
  FrobeniusMultiCentreLocusPicard FrobeniusMultiCentreIntegral FrobeniusMultiCentreNormal
  FrobeniusSelectedStageSurface FrobeniusStageZeroProjective FrobeniusStageNoetherianFiniteType
  FrobeniusExceptionalChainPicard FrobeniusExceptionalChainTransversal
  FrobeniusExceptionalChainTransversalLater FrobeniusStrictTransformPicardStep
  FrobeniusGraphPicardClassTotalTransform FrobeniusGraphPicardClassFiberClasses
  FrobeniusStrictTransformClassesTower FrobeniusOldExceptionalLaterStages
  FrobeniusStrictTransformClassesFull FrobeniusFiberPicard FrobeniusFiberZeroInvertible
  FrobeniusFiberZeroClass FrobeniusTowerFiberPullback FrobeniusFiberStrictCartier
  FrobeniusExceptionalCartier FrobeniusOldExceptionalLaterCartier FrobeniusExceptionalCartierPicard

/-- The base `P¹ × P¹` of the origin contact tower is integral (so that every stage is, through
BRIEF9's `instStageIsIntegral`, as required by the Cartier divisors of BRIEF19). -/
local instance f29FullInitialIntegral {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- The base of every translated tower is a Noetherian space (lane A1's
`projectiveProduct_noetherianSpace`), so that the final stages of the towers are Noetherian through
lane A1's `chainStage_noetherianSpace`. -/
local instance f29FullTranslatedNoetherianSpace {k : Type u} [Field k] (p : ℕ) (c : k) :
    NoetherianSpace (translatedInitial (k := k) p c).carrier :=
  projectiveProduct_noetherianSpace

/-- The base of every translated tower is locally Noetherian. -/
local instance f29FullTranslatedIsLocallyNoetherian {k : Type u} [Field k] (p : ℕ) (c : k) :
    IsLocallyNoetherian (translatedInitial (k := k) p c).carrier :=
  projectiveProduct_isLocallyNoetherian

/-! ## (1) Construction of `S_{p,n}` and of its towers -/

/-- Clause group (1): `S_{p,n} → P¹ ×_k P¹` proper; `S_{p,n}` proper, smooth of relative dimension two,
normal, integral, of dimension two over `k`; a `NormalProjectiveSurface` given `hproj`; every stage of
every tower proper, smooth, normal, integral, of dimension two; stage `0` projective; the tower
projections, the isomorphism loci, distinct centres. -/
abbrev Construction (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) : Prop :=
    IsProper (multiProjection (q + 1) n a) ∧
    IsProper (multiStructure (q + 1) n a) ∧
    IsSmoothOfRelativeDimension 2 (multiStructure (q + 1) n a) ∧
    IsNormalScheme (multiSurface (q + 1) n a) ∧
    IsIntegral (multiSurface (q + 1) n a) ∧
    topologicalKrullDim (multiSurface (q + 1) n a) = 2 ∧
    (∀ hproj : IsProjectiveOverField (multiStructure (q + 1) n a),
        (multiSurfaceSurface (q + 1) n a ha hproj).toScheme = multiSurface (q + 1) n a) ∧
    (∀ (i : Fin n) (m : ℕ),
        IsProper (selectedProjection (q + 1) (a i) m) ∧
        IsProper ((translatedInitial (q + 1) (a i)).stage m).structureMap ∧
        IsSmoothOfRelativeDimension 2 ((translatedInitial (q + 1) (a i)).stage m).structureMap ∧
        IsNormalScheme (selectedStage (q + 1) (a i) m) ∧
        IsIntegral (selectedStage (q + 1) (a i) m) ∧
        topologicalKrullDim (selectedStage (q + 1) (a i) m) = 2) ∧
    (∀ i : Fin n, IsProjectiveOverField ((translatedInitial (q + 1) (a i)).stage 0).structureMap) ∧
    (∀ i : Fin n, towerProjection (q + 1) n a i ≫ selectedProjection (q + 1) (a i) (q + 1) =
        multiProjection (q + 1) n a) ∧
    (∀ V : (projectiveProduct k).Opens, (∀ i, graphPoint (q + 1) (a i) ∉ V) →
        IsIso (multiProjection (q + 1) n a ∣_ V)) ∧
    (∀ i : Fin n, IsIso (towerProjection (q + 1) n a i ∣_ isoOpen q n a i)) ∧
    (∀ i j : Fin n, graphPoint (q + 1) (a i) = graphPoint (q + 1) (a j) → i = j)

theorem construction (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) : Construction k q n a ha :=
  ⟨multiProjection_isProper (q + 1) n a, multiStructure_isProper (q + 1) n a,
    multiStructure_smoothTwo (q + 1) n a ha, multiSurface_isNormalScheme (q + 1) n a ha,
    multiSurface_isIntegral (q + 1) n a ha, multiSurface_topologicalKrullDim (q + 1) n a ha,
    fun _ => rfl,
    fun i m => ⟨selectedProjection_isProper (q + 1) (a i) m,
      selectedStage_structure_isProper (q + 1) (a i) m,
      selectedStage_structure_smoothTwo (q + 1) (a i) m,
      selectedStage_isNormalScheme (q + 1) (a i) m,
      FrobeniusTowerFunctionField.PlaneChartedScheme.stage_isIntegral
        (translatedInitial (q + 1) (a i)) m,
      selectedStage_topologicalKrullDim (q + 1) (a i) m⟩,
    fun i => translated_stage_zero_projective (q + 1) (a i),
    fun i => towerProjection_projection (q + 1) n a i,
    fun V hV => multiProjection_restrict_isIso (q + 1) n a V hV,
    fun i => isoOpen_restrict_isIso q n a i,
    fun i j h => ha (selected_centers_injective (q + 1)
      (show (translatedInitial (q + 1) (a i)).chart.base originPoint =
        (translatedInitial (q + 1) (a j)).chart.base originPoint by
        rw [selected_center, selected_center]; exact h))⟩

/-! ## (2) The exceptional configuration of `S_{p,n}` -/

/-- Clause group (2): the `n·p` exceptional curves `C_{ij}`, `P_i` are closed subschemes, each `≅ P¹`,
closed supports over the centres, clusters disjoint, non-adjacent curves disjoint, adjacent curves
meeting in exactly one point, transversally (lane A1's `SinglePoints` and `TowerTransversal`). -/
abbrev Configuration (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) : Prop :=
    (∀ (i : Fin n) (idx : FinalIndex.{0} q), IsClosedImmersion (exceptionalCurveι q n a i idx)) ∧
    (∀ i : Fin n, Nonempty (exceptionalCurve q n a i (Sum.inr PUnit.unit) ≅ projectiveSpace k 1)) ∧
    (∀ (i : Fin n) (j : Fin q), Nonempty (exceptionalCurve q n a i (Sum.inl j) ≅ projectiveSpace k 1)) ∧
    (∀ (i : Fin n) (idx : FinalIndex.{0} q), IsClosed (exceptionalSupport q n a i idx)) ∧
    (∀ (i : Fin n) (idx : FinalIndex.{0} q) (x : multiSurface (q + 1) n a),
        x ∈ exceptionalSupport q n a i idx →
          (multiProjection (q + 1) n a).base x = graphPoint (q + 1) (a i)) ∧
    (∀ (i i' : Fin n) (idx idx' : FinalIndex.{0} q), i ≠ i' →
        Disjoint (exceptionalSupport q n a i idx) (exceptionalSupport q n a i' idx')) ∧
    (∀ (i : Fin n) (j j' : Fin q), j.val + 1 < j'.val →
        Disjoint (exceptionalSupport q n a i (Sum.inl j)) (exceptionalSupport q n a i (Sum.inl j'))) ∧
    (∀ (i : Fin n) (j : Fin q), j.val + 1 < q →
        Disjoint (exceptionalSupport q n a i (Sum.inl j))
          (exceptionalSupport q n a i (Sum.inr PUnit.unit))) ∧
    (∀ (i : Fin n) (j : ℕ) (hj : j + 1 < q),
        (exceptionalSupport q n a i (Sum.inl ⟨j, by omega⟩) ∩
          exceptionalSupport q n a i (Sum.inl ⟨j + 1, hj⟩)).Nonempty) ∧
    (∀ (m : ℕ) (hq : q = m + 1) (i : Fin n),
        (exceptionalSupport q n a i (Sum.inl ⟨m, by omega⟩) ∩
          exceptionalSupport q n a i (Sum.inr PUnit.unit)).Nonempty) ∧
    SinglePoints q n a ∧
    TowerTransversal q n a ha (FrobeniusMultiCentreChainTransversal.singlePoints q n a ha)

theorem configuration (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) : Configuration k q n a ha :=
  ⟨fun i idx => exceptionalCurveι_isClosedImmersion q n a i idx,
    fun i => ⟨newestCurveIso q n a ha i⟩,
    fun i j => sPn_oldExceptional_iso_projectiveLine k q n a ha i j,
    fun i idx => exceptionalSupport_isClosed q n a i idx,
    fun i idx x hx => exceptionalSupport_projection q n a i idx x hx,
    fun i i' idx idx' h => exceptionalSupport_disjoint_of_ne q n a ha h idx idx',
    fun i j j' h => exceptionalSupport_disjoint_nonadjacent q n a i j j' h,
    fun i j h => exceptionalSupport_disjoint_newest q n a i j h,
    fun i j hj => exceptionalSupport_adjacent q n a ha i j hj,
    fun m hq i => by
      subst hq
      exact exceptionalSupport_last_adjacent m n a ha i,
    FrobeniusMultiCentreChainTransversal.singlePoints q n a ha,
    FrobeniusMultiCentreChainTransversal.towerTransversal q n a ha⟩

/-! ## (3) The strict transforms `B` and `F_i` -/

/-- Clause group (3): `B`, `F_i` closed integral curves, literal pullbacks of the punctured graph and
fibres; `B ∩ P_i`, `F_i ∩ P_i` single points with contact length one on the stalks of `B`, `F_i`;
`B ∩ F_i = ∅`, `B ∩ C_{ij} = ∅`, `F_i ∩ C_{ij} = ∅`, `F_i ∩ F_j = ∅`, `F_i` off the other clusters. -/
abbrev StrictTransforms (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ) [Fact (q + 1).Prime]
    [CharP k (q + 1)] (a : Fin n → k) : Prop :=
    IsClosedImmersion (graphStrictι (q + 1) n a) ∧
    IsIntegral (graphStrict (q + 1) n a) ∧
    (∀ i : Fin n, IsClosedImmersion (fiberStrictι (q + 1) n a i)) ∧
    (∀ i : Fin n, IsIntegral (fiberStrict (q + 1) n a i)) ∧
    IsPullback (graphLift (q + 1) n a) (𝟙 _) (multiProjection (q + 1) n a)
      (puncturedGraph (q + 1) n a) ∧
    (∀ i : Fin n, IsPullback (fiberLift (q + 1) n a i) (𝟙 _) (multiProjection (q + 1) n a)
        (puncturedFiber (q + 1) n a i)) ∧
    (∀ x : graphStrict (q + 1) n a,
        (multiProjection (q + 1) n a).base ((graphStrictι (q + 1) n a).base x) ∈
          Set.range (graphι (k := k) (q + 1)).base) ∧
    (∀ (i : Fin n) (x : fiberStrict (q + 1) n a i),
        (multiProjection (q + 1) n a).base ((fiberStrictι (q + 1) n a i).base x) ∈
          Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base) ∧
    (∀ i : Fin n, ∃ (x : graphStrict (q + 1) n a)
      (hP : (graphStrictι (q + 1) n a).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit))
      (hx : (graphStrictι (q + 1) n a).base x ∈ isoPreimage q n a i),
      Set.range (graphStrictι (q + 1) n a).base ∩
        exceptionalSupport q n a i (Sum.inr PUnit.unit) = {(graphStrictι (q + 1) n a).base x} ∧
      Module.length ((graphStrict (q + 1) n a).presheaf.stalk x)
        ((graphStrict (q + 1) n a).presheaf.stalk x ⧸
          Ideal.span {graphContactGermS q n a i x hP hx}) = 1) ∧
    (∀ i : Fin n, ∃ (x : fiberStrict (q + 1) n a i)
      (hP : (fiberStrictι (q + 1) n a i).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit))
      (hx : (fiberStrictι (q + 1) n a i).base x ∈ isoPreimage q n a i),
      Set.range (fiberStrictι (q + 1) n a i).base ∩
        exceptionalSupport q n a i (Sum.inr PUnit.unit) = {(fiberStrictι (q + 1) n a i).base x} ∧
      Module.length ((fiberStrict (q + 1) n a i).presheaf.stalk x)
        ((fiberStrict (q + 1) n a i).presheaf.stalk x ⧸
          Ideal.span {fiberContactGermS q n a i x hP hx}) = 1) ∧
    (∀ i : Fin n, Disjoint (Set.range (graphStrictι (q + 1) n a).base)
        (Set.range (fiberStrictι (q + 1) n a i).base)) ∧
    (∀ (i : Fin n) (j : Fin q),
        Disjoint (Set.range (graphStrictι (q + 1) n a).base)
          (exceptionalSupport q n a i (Sum.inl j))) ∧
    (∀ (i : Fin n) (j : Fin q),
        Disjoint (Set.range (fiberStrictι (q + 1) n a i).base)
          (exceptionalSupport q n a i (Sum.inl j))) ∧
    (∀ i j : Fin n, i ≠ j →
        Disjoint (Set.range (fiberStrictι (q + 1) n a i).base)
          (Set.range (fiberStrictι (q + 1) n a j).base)) ∧
    (∀ (i j : Fin n) (idx : FinalIndex.{0} q), i ≠ j →
        Disjoint (Set.range (fiberStrictι (q + 1) n a i).base) (exceptionalSupport q n a j idx))

theorem strictTransforms (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ) [Fact (q + 1).Prime]
    [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) :
    StrictTransforms k q n a :=
  ⟨graphStrictι_isClosedImmersion (q + 1) n a,
    graphStrict_isIntegral (q + 1) n a,
    fun i => fiberStrictι_isClosedImmersion (q + 1) n a i,
    fun i => fiberStrict_isIntegral (q + 1) n a i,
    graphLift_isPullback (q + 1) n a,
    fun i => fiberLift_isPullback (q + 1) n a i,
    fun x => graphStrict_projection_mem (q + 1) n a x,
    fun i x => fiberStrict_projection_mem (q + 1) n a i x,
    (sPn_transversal_contacts' k q n a ha).1,
    (sPn_transversal_contacts' k q n a ha).2,
    fun i => sPn_graph_fiber_disjoint k q n a i,
    fun i j => graphStrict_disjoint_exceptional_same q n a i j,
    fun i j => fiberStrict_disjoint_exceptional_same q n a i j,
    fun _ _ hij => fiberStrict_disjoint (q + 1) n a ha hij,
    fun _ _ idx hij => fiberStrict_disjoint_exceptional q n a ha hij idx⟩

/-! ## (4) The complete scheme-theoretic fibres and the unaffected fibres -/

/-- Clause group (4): the complete scheme-theoretic fibres of `S_{p,n}` over `y = a_i^p` (closed,
literal pullbacks, support `F_i ∪ ⋃_j C_{ij} ∪ P_i`, off the other clusters); the unaffected fibres
of `S_{p,n}` over the other heights (`≅ P¹`); the per-tower unaffected fibres `y = c`, `x = c`. -/
abbrev Fibres (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ) [Fact (q + 1).Prime]
    [CharP k (q + 1)] (a : Fin n → k) : Prop :=
    (∀ i : Fin n, IsClosedImmersion (specialFiberSι q n a i)) ∧
    (∀ i : Fin n, IsPullback (specialFiberSι q n a i) (specialFiberSToLine q n a i)
        (multiProjection (q + 1) n a) (horizontalFiberMorphism (a i ^ (q + 1)))) ∧
    (∀ i : Fin n, specialFiberSSupport q n a i =
        Set.range (fiberStrictι (q + 1) n a i).base ∪
          ⋃ idx : FinalIndex.{0} q, exceptionalSupport q n a i idx) ∧
    (∀ (i j : Fin n), j ≠ i → ∀ idx : FinalIndex.{0} q,
        Disjoint (specialFiberSSupport q n a i) (exceptionalSupport q n a j idx)) ∧
    (∀ (c : k) (hc : ∀ j, c ≠ a j ^ (q + 1)),
        IsPullback (unaffectedFiberLift q n a c hc) (𝟙 (projectiveSpace k 1))
          (multiProjection (q + 1) n a) (horizontalFiberMorphism c) ∧
        Nonempty (projectiveSpace k 1 ≅
          pullback (multiProjection (q + 1) n a) (horizontalFiberMorphism c))) ∧
    (∀ (i : Fin n) (c : k) (hc : c ≠ a i ^ (q + 1)) (m : ℕ),
        IsPullback (horizontalFiberLift (q + 1) (a i) c hc m) (𝟙 (projectiveSpace k 1))
          (selectedProjection (q + 1) (a i) m) (horizontalFiberMorphism c) ∧
        IsClosedImmersion (horizontalFiberLift (q + 1) (a i) c hc m) ∧
        ∀ y, (horizontalFiberLift (q + 1) (a i) c hc m).base y ∈
          stagePuncture (translatedInitial (q + 1) (a i)) m) ∧
    (∀ (i : Fin n) (c : k) (hc : c ≠ a i) (m : ℕ),
        IsPullback (verticalFiberLift (q + 1) (a i) c hc m) (𝟙 (projectiveSpace k 1))
          (selectedProjection (q + 1) (a i) m) (verticalFiberMorphismAt c) ∧
        IsClosedImmersion (verticalFiberLift (q + 1) (a i) c hc m) ∧
        ∀ y, (verticalFiberLift (q + 1) (a i) c hc m).base y ∈
          stagePuncture (translatedInitial (q + 1) (a i)) m)

theorem fibres (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ) [Fact (q + 1).Prime]
    [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) : Fibres k q n a :=
  ⟨fun i => specialFiberSι_isClosedImmersion q n a i,
    fun i => specialFiberS_isPullback q n a i,
    fun i => specialFiberSSupport_eq_components q n a ha i,
    fun i j hij idx => specialFiberS_disjoint_other_exceptional q n a ha i j hij idx,
    fun c hc => ⟨unaffectedFiberLift_isPullback q n a c hc, ⟨unaffectedFiberIso q n a c hc⟩⟩,
    fun i c hc m => ⟨horizontalFiberLift_isPullback (q + 1) (a i) c hc m,
      horizontalFiberLift_isClosedImmersion (q + 1) (a i) c hc m,
      fun y => horizontalFiberLift_mem_puncture (q + 1) (a i) c hc m y⟩,
    fun i c hc m => ⟨verticalFiberLift_isPullback (q + 1) (a i) c hc m,
      verticalFiberLift_isClosedImmersion (q + 1) (a i) c hc m,
      fun y => verticalFiberLift_mem_puncture (q + 1) (a i) c hc m y⟩⟩

/-! ## (5) The class table on the origin contact tower -/

/-- Clause group (5), on the origin contact tower over any field `k` (Proposition 10.1's class
table, ideal-sheaf sign convention): `B = (m+N)·a + b − Σ E_j` on stage `N` for the graph
`y = x^{m+N}`, in particular `B = p·a + b − Σ E_j` for the `p`-fold tower; `C_j = E_j − E_{j+1}`;
`F_N = π^*b − Σ E_j` with `F_0 = b` and `F_{m+1} = π^*F_m − E_m`; `P = E_last`. -/
abbrev ClassTable (k : Type u) [Field k] (q : ℕ) : Prop :=
    (∀ N m : ℕ, strictCurvePicardClass (k := k) N m =
        (m + N) • firstFiberTotalClass N + secondFiberTotalClass N -
          ∑ j : Fin N, totalExceptionalClass N j) ∧
    (∀ N : ℕ, N ≤ q + 1 → strictCurvePicardClass (k := k) N (q + 1 - N) =
        (q + 1) • firstFiberTotalClass N + secondFiberTotalClass N -
          ∑ j : Fin N, totalExceptionalClass N j) ∧
    (∀ (N j : ℕ) (h : j + 1 + 1 ≤ N),
        oldExceptionalStrictClass (k := k) N j h =
          totalExceptionalClass N ⟨j, by omega⟩ - totalExceptionalClass N ⟨j + 1, by omega⟩) ∧
    (∀ N : ℕ, fiberClass (k := k) N =
        (schemePicardPullbackHom (between (projectiveProductInitial (k := k))
          (Nat.zero_le N))).toAdditive secondFiberClass -
          ∑ j : Fin N, totalExceptionalClass N j) ∧
    fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) 0 = secondFiberClass ∧
    (∀ m : ℕ, fiberClass (k := k) (m + 1) =
        (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection m)).toAdditive
          (fiberClass m) - stepExceptionalPicardClass m) ∧
    (∀ N : ℕ, totalExceptionalClass (k := k) (N + 1) (Fin.last N) = stepExceptionalPicardClass N)

theorem classTable (k : Type u) [Field k] (q : ℕ) : ClassTable k q :=
  ⟨fun N m => strictCurvePicardClass_tower N m,
    fun N h => strictCurvePicardClass_pFold (q + 1) N h,
    fun N j h => oldExceptionalStrictClasses_tower N j h,
    fun N => by
      rw [fiberClass_tower, fiberZeroTotalClass, fiberTotalClass_eq_pullback_secondFiberClass],
    fiberPicardClass_zero_eq_secondFiberClass,
    fun m => fiberClass_succ m,
    fun N => totalExceptionalClass_last N⟩

/-! ## (6) The Cartier fibre identity on the origin contact tower -/

/-- Clause group (6), on the origin contact tower over any field `k`: the total transform of the
fibre `y = 0` is an effective Cartier divisor with regular equations and
`π^*(y = 0) = F̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P` on stage `N+1`; the Cartier classes of `F̃`, `P`,
`C_j` are the Picard classes of (5); the Picard form `π^*b = F̃ + Σ (j+1)·C_j + (N+1)·P`. -/
abbrev CartierIdentity (k : Type u) [Field k] : Prop :=
    (∀ N : ℕ, totalFiberDivisor (k := k) (N + 1) =
        fiberStrictDivisor (N + 1) +
          ∑ j : Fin N, (j.val + 1) • oldFinalDivisor (N + 1) j.val (by omega) +
          (N + 1) • stepExceptionalDivisor N) ∧
    (∀ N : ℕ, HasRegularCartierEquations _ (totalFiberDivisor (k := k) N)) ∧
    (∀ m : ℕ, cartierPicardHom _ (fiberStrictDivisor (k := k) m) =
        fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) m) ∧
    (∀ m : ℕ, cartierPicardHom _ (stepExceptionalDivisor (k := k) m) = stepExceptionalPicardClass m) ∧
    (∀ (N j : ℕ) (h : j + 1 + 1 ≤ N),
        cartierPicardHom _ (oldFinalDivisor (k := k) N j h) = oldExceptionalStrictClass N j h) ∧
    (∀ N : ℕ,
        (schemePicardPullbackHom (between (projectiveProductInitial (k := k))
          (Nat.zero_le (N + 1)))).toAdditive secondFiberClass =
        fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) (N + 1) +
          ∑ j : Fin N, (j.val + 1) • oldExceptionalStrictClass (k := k) (N + 1) j.val (by omega) +
            (N + 1) • totalExceptionalClass (N + 1) (Fin.last N))

theorem cartierIdentity (k : Type u) [Field k] : CartierIdentity k :=
  ⟨fun N => f29_tower_fiber_relation k N,
    fun N => totalFiberDivisor_hasRegularEquations N,
    fun m => fiberStrictDivisor_picard m,
    fun m => stepExceptionalDivisor_picard' m,
    fun N j h => oldFinalDivisor_picard N j h,
    f29_tower_fiber_picard_relation_b k⟩

/-! ## (7) The Picard groups of the exceptional chains -/

/-- Clause group (7): `Pic(C_{i1} ∪ ⋯ ∪ C_{iq} ∪ P_i) ≃ ℤ^{q+1}` on `S_{p,n}`,
`Pic(exceptional locus) ≃ ℤ^{n(q+1)}` (lane A1's `locusPicardEquiv`, both hypotheses discharged),
and on each tower `T_i`: single points, transversality, `Pic(C_1 ∪ ⋯ ∪ C_q ∪ P) ≃ ℤ^{q+1}`. -/
abbrev ChainPicard (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) : Prop :=
    (∀ i : Fin n, Nonempty ((towerChain q n a ha i).Pic ≃* (Fin (q + 1) → Multiplicative ℤ))) ∧
    Nonempty ((exceptionalScheme q n a).Pic ≃* (Fin n × Fin (q + 1) → Multiplicative ℤ)) ∧
    (∀ i : Fin n, ChainSinglePoints q (translatedInitial (q + 1) (a i))) ∧
    (∀ i : Fin n, ChainTransversal q (translatedInitial (q + 1) (a i))
        (chainSinglePoints (translatedInitial (q + 1) (a i)) q)) ∧
    (∀ i : Fin n, Nonempty ((chainScheme q (translatedInitial (q + 1) (a i))).Pic ≃*
        (Fin (q + 1) → Multiplicative ℤ)))

theorem chainPicard (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) : ChainPicard k q n a ha :=
  ⟨fun i => ⟨FrobeniusMultiCentreChainTransversal.towerChainPicardEquiv_unconditional q n a ha i⟩,
    ⟨locusPicardEquiv q n a ha (FrobeniusMultiCentreChainTransversal.singlePoints q n a ha)
      (FrobeniusMultiCentreChainTransversal.towerTransversal q n a ha)⟩,
    fun i => chainSinglePoints (translatedInitial (q + 1) (a i)) q,
    fun i => chainTransversal (translatedInitial (q + 1) (a i)) q,
    fun i => ⟨chainPicardEquivFin_unconditional (translatedInitial (q + 1) (a i)) q⟩⟩

end KltDP.Examples.FrobeniusContactBlowupsF29Full

namespace KltDP.Examples

open FrobeniusContactBlowupsF29Full

/-- **Obligation F29, completion bundle.** Every clause of Proposition 10.1 proved for the actual
`S_{p,n}` and its towers (groups 1–4, 7) and, for the class table and the Cartier fibre identity
(groups 5–6), for the origin contact tower. Each group is the explicit conjunction recorded in the
corresponding `abbrev` above. -/
theorem f29_contact_blowups_full (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) :
    Construction k q n a ha ∧ Configuration k q n a ha ∧ StrictTransforms k q n a ∧
    Fibres k q n a ∧ ClassTable k q ∧ CartierIdentity k ∧ ChainPicard k q n a ha :=
  ⟨construction k q n a ha, configuration k q n a ha, strictTransforms k q n a ha,
    fibres k q n a ha, classTable k q, cartierIdentity k, chainPicard k q n a ha⟩

/-- The bundle has exactly one universe parameter: this elaborates only if
`f29_contact_blowups_full` carries no other universe level. -/
theorem f29_contact_blowups_full_universe_check (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) : True := by
  have _ := f29_contact_blowups_full.{u} k q n a ha
  trivial

end KltDP.Examples
