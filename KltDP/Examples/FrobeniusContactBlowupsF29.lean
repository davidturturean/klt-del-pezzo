import KltDP.Examples.FrobeniusUnaffectedFibers
import KltDP.Examples.FrobeniusGraphExceptionalSeparation
import KltDP.Examples.FrobeniusGraphPicardClassTotalTransform

/-!
# F29 bundle: iterated contact blowups and the local fibre incidences proved so far

`f29_contact_blowups` collects, for an algebraically closed field `k` of characteristic `p`
(`p` prime), the clauses of obligation F29 that are proved for the accepted actual objects:

1. at every rational graph point `(a, a^p)` the whole tower of `n` contact blowups exists, its
   composite projection to `P¹ ×_k P¹` is proper, and every stage is proper and smooth of
   relative dimension two over `k`;
2. the centre of that tower is the accepted closed point `graphPoint p a`, all stage centres
   project to it, and distinct `a` give distinct centres;
3. when the accumulated exponent is `p`, the residual local curve of a stage projects onto the
   whole Frobenius graph, and before that the next centre lies on it;
4. in the tower at the origin the strict transform of the whole graph is a closed integral
   subscheme at every stage, with contact length one with the new exceptional curve, `m` with
   the strict fibre, `m + 1` with the pulled fibre, and strict-fibre germ `1` at the terminal
   point; before the terminal stage the contact point is the next centre;
5. the total transform of the graph class is `p • a + b` in the actual Picard group of every
   stage;
6. the earlier exceptional components form a chain in the final stage: adjacent ones meet,
   non-adjacent ones are disjoint, the last one meets the newest fibre, all are closed, and the
   newest fibre is a projective line;
7. the graph strict transform misses every exceptional component created before the last blowup
   and its terminal contact point lies on the newest exceptional fibre;
8. the fibres `y = c` (`c ≠ a^p`) and `x = c` (`c ≠ a`) are unaffected by the tower at `(a, a^p)`:
   they lift to every stage as closed immersions which are literal pullbacks, inside the puncture.

Not part of this bundle (not proved): the strict-transform classes `B`, `F_i`, `C_ij` in the
Picard group of the final stage, the complete scheme-theoretic fibre `F + Σ j C_j + p P`,
uniqueness of the graph/`P` intersection point, and the multi-centre surface `S_{p,n}`. See
`F29_CORRESPONDENCE.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
  FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupIncidence
  FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupSmooth FrobeniusTranslatedCharts
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusGlobalStrictTransform
  FrobeniusStrictTransformContact FrobeniusGlobalExceptionalSuccessor
  FrobeniusExceptionalFinalConfiguration FrobeniusGraphPicardClassZeroFiber
  FrobeniusGraphPicardClassTotalTransform FrobeniusContactTowerSelectedPoint
  FrobeniusUnaffectedFibers FrobeniusGraphExceptionalSeparation

/-- Obligation F29 for the accepted contact towers: the clauses proved so far. -/
theorem f29_contact_blowups (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    -- (1) the tower at every selected point: proper projection, proper and smooth stages
    (∀ (a : k) (n : ℕ), IsProper (selectedProjection p a n) ∧
        IsProper ((translatedInitial (k := k) p a).stage n).structureMap ∧
        IsSmoothOfRelativeDimension 2 ((translatedInitial (k := k) p a).stage n).structureMap) ∧
    -- (2) centres
    (∀ a : k, (translatedInitial p a).chart.base (originPoint (k := k)) = graphPoint p a ∧
        IsClosed ({graphPoint p a} : Set (projectiveProduct k))) ∧
    (∀ (a : k) (n : ℕ), (selectedProjection p a n).base
        (((translatedInitial p a).stage n).chart.base (originPoint (k := k))) = graphPoint p a) ∧
    Function.Injective (β := projectiveProduct k)
      (fun a : k => (translatedInitial p a).chart.base (originPoint (k := k))) ∧
    -- (3) residual curves lie on the graph; the next centre lies on them
    (∀ (a : k) (n m : ℕ), m + n = p →
        (translatedInitial p a).residualCurve n m ≫ selectedProjection p a n =
          (parameterTranslationIso a).hom ≫
            ProjectiveLineComparison.polynomialChartMap k 0 ≫ projectiveGraphMorphism p) ∧
    (∀ (a : k) (n m : ℕ), 0 < m →
        parameterOriginMorphism (k := k) ≫ (translatedInitial p a).residualCurve n m =
          ((translatedInitial p a).stage n).centerMorphism) ∧
    -- (4) origin tower: strict transform of the whole graph and its contact lengths
    (∀ n m : ℕ, IsClosedImmersion (strictTransformι (k := k) n (m + n)) ∧
        IsIntegral (strictTransform (k := k) n (m + n))) ∧
    (∀ n m : ℕ,
        Module.length (contactStalk (k := k) (n + 1) m)
          (contactStalk (k := k) (n + 1) m ⧸ Ideal.span {contactGerm n m chartU}) = 1 ∧
        Module.length (contactStalk (k := k) (n + 1) m)
          (contactStalk (k := k) (n + 1) m ⧸ Ideal.span {contactGerm n m chartW}) = m ∧
        Module.length (contactStalk (k := k) (n + 1) m)
          (contactStalk (k := k) (n + 1) m ⧸
            Ideal.span {contactGerm n m (baseMap vCoord)}) = m + 1) ∧
    (∀ n : ℕ, contactGerm (k := k) n 0 chartW = 1) ∧
    (∀ n m : ℕ, 0 < m →
        (strictTransformι (k := k) n (m + n)).base (contactPoint n m) =
          ((projectiveProductInitial (k := k)).stage n).chart.base originPoint) ∧
    -- (5) total-transform class on every stage
    (∀ n : ℕ, -Additive.ofMul (graphTotalIdealLine (k := k) n p).toPic =
        p • firstFiberTotalClass n + secondFiberTotalClass n) ∧
    -- (6) the exceptional chain in the final stage
    (∀ (n j : ℕ) (hj : j + 1 < n),
        (finalSupport (projectiveProductInitial (k := k)) n (Sum.inl ⟨j, by omega⟩ : FinalIndex.{0} n) ∩
          finalSupport (projectiveProductInitial (k := k)) n
            (Sum.inl ⟨j + 1, hj⟩ : FinalIndex.{0} n)).Nonempty) ∧
    (∀ n : ℕ,
        (finalSupport (projectiveProductInitial (k := k)) (n + 1)
            (Sum.inl ⟨n, by omega⟩ : FinalIndex.{0} (n + 1)) ∩
          finalSupport (projectiveProductInitial (k := k)) (n + 1)
            (Sum.inr PUnit.unit : FinalIndex.{0} (n + 1))).Nonempty) ∧
    (∀ (n : ℕ) (i j : Fin n), i.val + 1 < j.val →
        Disjoint (finalSupport (projectiveProductInitial (k := k)) n (Sum.inl i : FinalIndex.{0} n))
          (finalSupport (projectiveProductInitial (k := k)) n (Sum.inl j : FinalIndex.{0} n))) ∧
    (∀ (n : ℕ) (i : Fin n), i.val + 1 < n →
        Disjoint (finalSupport (projectiveProductInitial (k := k)) n (Sum.inl i : FinalIndex.{0} n))
          (finalSupport (projectiveProductInitial (k := k)) n
            (Sum.inr PUnit.unit : FinalIndex.{0} n))) ∧
    (∀ (n : ℕ) (a : FinalIndex.{0} n),
        IsClosedImmersion (finalComponentι (projectiveProductInitial (k := k)) n a)) ∧
    (∀ n : ℕ, Nonempty (previousFiber ((projectiveProductInitial (k := k)).stage n) ≅
        projectiveSpace k 1)) ∧
    -- (7) separation of the graph strict transform from the earlier exceptional components
    (∀ (N j m : ℕ) (h : j + 2 ≤ N),
        Disjoint (Set.range (strictTransformι (k := k) N (m + N)).base)
          (Set.range (finalOldMap (projectiveProductInitial (k := k)) N j h).base)) ∧
    (∀ n : ℕ, (strictTransformι (k := k) (n + 1) (0 + (n + 1))).base (contactPoint (n + 1) 0) ∈
        Set.range (previousFiberι ((projectiveProductInitial (k := k)).stage n)).base) ∧
    -- (8) unaffected fibres over non-selected points
    (∀ (a c : k) (hc : c ≠ a ^ p) (n : ℕ),
        IsPullback (horizontalFiberLift p a c hc n) (𝟙 (projectiveSpace k 1))
          (selectedProjection p a n) (horizontalFiberMorphism c) ∧
        IsClosedImmersion (horizontalFiberLift p a c hc n) ∧
        ∀ y, (horizontalFiberLift p a c hc n).base y ∈ stagePuncture (translatedInitial p a) n) ∧
    (∀ (a c : k) (hc : c ≠ a) (n : ℕ),
        IsPullback (verticalFiberLift p a c hc n) (𝟙 (projectiveSpace k 1))
          (selectedProjection p a n) (verticalFiberMorphismAt c) ∧
        IsClosedImmersion (verticalFiberLift p a c hc n) ∧
        ∀ y, (verticalFiberLift p a c hc n).base y ∈ stagePuncture (translatedInitial p a) n) :=
  ⟨fun a n => ⟨selectedProjection_isProper p a n, selectedStage_structure_isProper p a n,
      selectedStage_structure_smoothTwo p a n⟩,
    fun a => ⟨selected_center p a, selected_center_isClosed p a⟩,
    fun a n => selectedStage_center_projection p a n,
    selected_centers_injective p,
    fun a n m hm => selectedResidualCurve_toGraph p a n m hm,
    fun a n m hm => selected_center_on_residualCurve p a n m hm,
    fun n m => ⟨strictTransformι_isClosedImmersion n (m + n), strictTransform_isIntegral n m⟩,
    fun n m => ⟨exceptional_contact_length n m, strictFiber_contact_length n m,
      totalFiber_contact_length n m⟩,
    fun n => terminal_strictFiber_germ n,
    fun n m hm => contactPoint_inclusion n m hm,
    fun n => inverse_graphTotalIdeal_picard_eq_actual_fibers n p,
    fun n j hj => finalSupport_adjacent (projectiveProductInitial (k := k)) n j hj,
    fun n => finalSupport_last_adjacent (projectiveProductInitial (k := k)) n,
    fun n i j hij => finalSupport_nonadjacent (projectiveProductInitial (k := k)) n i j hij,
    fun n i hi => finalSupport_nonadjacent_newest (projectiveProductInitial (k := k)) n i hi,
    fun n a => finalComponentι_isClosedImmersion (projectiveProductInitial (k := k)) n a,
    fun n => ⟨previousFiberIso ((projectiveProductInitial (k := k)).stage n)⟩,
    fun N j m h => strictTransform_disjoint_finalOld N j m h,
    fun n => terminal_contactPoint_mem_newestFiber n,
    fun a c hc n => ⟨horizontalFiberLift_isPullback p a c hc n,
      horizontalFiberLift_isClosedImmersion p a c hc n,
      fun y => horizontalFiberLift_mem_puncture p a c hc n y⟩,
    fun a c hc n => ⟨verticalFiberLift_isPullback p a c hc n,
      verticalFiberLift_isClosedImmersion p a c hc n,
      fun y => verticalFiberLift_mem_puncture p a c hc n y⟩⟩

/-- The bundle has exactly one universe parameter: this elaborates only if `f29_contact_blowups`
carries no other universe level. -/
theorem f29_contact_blowups_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] : True := by
  have _ := f29_contact_blowups.{u} k p
  trivial

end KltDP.Examples
