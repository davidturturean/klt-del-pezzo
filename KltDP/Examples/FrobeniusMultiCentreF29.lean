import KltDP.Examples.FrobeniusContactTowerInfinity
import KltDP.Examples.FrobeniusMultiCentreSurface

/-!
# F29 bundle (multi-centre part): the tower at infinity and the surface `S_{p,n}`

`f29_multi_centre` collects, for an algebraically closed field `k` of characteristic `p` (`p`
prime), the multi-centre clauses of obligation F29 proved in this lane:

1. the contact-blowup tower at the point `(∞,∞)` of the graph, built on the accepted reciprocal
   product chart: proper projection, proper and smooth stages, the residual curve of accumulated
   exponent `p` lies on the whole graph, and the centre at infinity is closed and distinct from
   every finite selected centre;
2. for every `n` and every injective selection `a : Fin n → k` the multi-centre surface
   `S_{p,n} = multiSurface p n a` (the iterated fibre product over `P¹ ×_k P¹` of the `n` towers) has
   a proper projection to the product, is proper and smooth of relative dimension two over `k`, is
   an isomorphism over any open avoiding the selected centres, projects compatibly onto each tower,
   and carries the total-transform relation `−[Π^*O(B_0)] = p • a + b` in its actual Picard group,
   together with the `n·p` total-transform classes `E_{ij}` defined from the exceptional ideal lines;
3. an injective selection of `n` parameters exists for every `n` (`k` is infinite).

The strict-transform classes `B`, `F_i`, `C_ij`, `P_i` on `S_{p,n}` and the complete
scheme-theoretic fibre are not part of this bundle (see `F29_MULTI_CENTRE.md`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts FrobeniusStageComplement.PlaneChartedScheme
  FrobeniusContactTowerSelectedPoint FrobeniusContactTowerInfinity FrobeniusMultiCentreSurface

/-- The multi-centre clauses of obligation F29: the tower at infinity and the surface `S_{p,n}`. -/
theorem f29_multi_centre (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    -- (1) the tower at `(∞,∞)`
    (∀ n : ℕ, IsProper (infinityProjection (k := k) n) ∧
        IsProper ((infinityInitial k).stage n).structureMap ∧
        IsSmoothOfRelativeDimension 2 ((infinityInitial k).stage n).structureMap) ∧
    (∀ n m : ℕ, m + n = p →
        (infinityInitial k).residualCurve n m ≫ infinityProjection n =
          polynomialChartMap k 1 ≫ projectiveGraphMorphism p) ∧
    IsClosed ({infinityCenter k} : Set (projectiveProduct k)) ∧
    (∀ a : k, infinityCenter k ≠ graphPoint p a) ∧
    -- (2) the multi-centre surface for every injective selection
    (∀ (n : ℕ) (a : Fin n → k), Function.Injective a →
        IsProper (multiProjection p n a) ∧ IsProper (multiStructure p n a) ∧
        IsSmoothOfRelativeDimension 2 (multiStructure p n a) ∧
        (∀ V : (projectiveProduct k).Opens, (∀ i, graphPoint p (a i) ∉ V) →
          IsIso (multiProjection p n a ∣_ V)) ∧
        (∀ i : Fin n, towerProjection p n a i ≫ selectedProjection p (a i) p =
          multiProjection p n a) ∧
        (-Additive.ofMul (multiGraphTotalIdealLine p n a).toPic =
          p • multiFirstFiberClass p n a + multiSecondFiberClass p n a) ∧
        (∀ (i : Fin n) (j : Fin p), exceptionalClass p n a i j =
          -Additive.ofMul (pullbackInvertibleSheaf (towerProjection p n a i)
            (towerExceptionalLine p (a i) j)).toPic)) ∧
    -- (3) injective selections exist for every `n`
    (∀ n : ℕ, ∃ a : Fin n → k, Function.Injective a) :=
  ⟨fun n => ⟨infinityProjection_isProper n, infinityStage_structure_isProper n,
      infinityStage_structure_smoothTwo n⟩,
    fun n m hm => infinityResidualCurve_toGraph p n m hm,
    infinityCenter_isClosed,
    fun a => infinityCenter_ne_graphPoint p a,
    fun n a ha => ⟨multiProjection_isProper p n a, multiStructure_isProper p n a,
      multiStructure_smoothTwo p n a ha,
      fun V hV => multiProjection_restrict_isIso p n a V hV,
      fun i => towerProjection_projection p n a i,
      inverse_multiGraphTotalIdeal_picard p n a,
      fun _ _ => rfl⟩,
    fun n => ⟨fun i => affineCoordinates (k := k) n i, (affineCoordinates (k := k) n).injective⟩⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_multi_centre_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] : True := by
  have _ := f29_multi_centre.{u} k p
  trivial

end KltDP.Examples
