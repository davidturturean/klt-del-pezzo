# Paper to Lean

Every numbered statement of the manuscript (`source/manuscript.tex`) has a Lean counterpart. The table lists, for each statement, its status and the modules that contain the declarations; the exact declaration names are recorded in `audit/claim-status.json`.

**Formalized** means every clause of the statement has a compiled Lean declaration. **Formalized; isolated clauses** means the statement's role in the main theorem is fully proved and one or more side clauses (listed in the registry) are stated but not proved: for Lemma 3.1 the smoothness of the generic fibre of the ruling, for Lemma 3.2 the normal-crossing tree shape of the fibres and the equality in the fibre count (the inequality is proved), for Propositions A.1 and A.2 the four extra curve families and the completeness of the negative-curve list.

## Named manuscript results

| ID | Manuscript statement / inventory title | Status | Lean source |
| --- | --- | --- | --- |
| `thm:main` | [1.1. Uniform seven-point bound](../source/manuscript.tex#L106) | Formalized | [Final](../KltDP/Manuscript/Main/Final.lean), [Assembly3](../KltDP/Manuscript/Main/Assembly3.lean); 3 further files in the declaration record |
| `thm:examples` | [1.2. Bernasconi; Keel--McKernan](../source/manuscript.tex#L121) | Formalized | [Examples](../KltDP/Manuscript/S01/Examples.lean) |
| `lem:stieltjes` | [2.1. Positivity of a Stieltjes inverse](../source/manuscript.tex#L359) | Formalized | [Stieltjes](../KltDP/Manuscript/S02/Stieltjes.lean) |
| `lem:tree-picard` | [2.2. Picard group of a rational tree](../source/manuscript.tex#L367) | Formalized | [RationalTreePicard](../KltDP/Manuscript/S02/RationalTreePicard.lean), [RationalTreePicardStalkTransport](../KltDP/Geometry/RationalTreePicardStalkTransport.lean); 1 further file in the declaration record |
| `thm:keel` | [2.3. Keel {\cite[Theorem~0.2](../source/manuscript.tex#L381) | Admitted literature statement | [KeelSemiampleness](../KltDP/Manuscript/S02/KeelSemiampleness.lean), [KeelCompleteSystem](../KltDP/Literature/KeelCompleteSystem.lean) |
| `prop:minimal-resolution` | [2.4. Geometry of the minimal resolution](../source/manuscript.tex#L392) | Formalized | [ResolutionDatum](../KltDP/Manuscript/Datum/ResolutionDatum.lean), [MinimalResolutionGeometry](../KltDP/Manuscript/S02/MinimalResolutionGeometry.lean); 4 further files in the declaration record |
| `lem:square-degree` | [2.5. Square and degree formulas](../source/manuscript.tex#L461) | Formalized | [SquareDegree](../KltDP/Manuscript/S02/SquareDegree.lean) |
| `thm:anticanonical-contraction` | [2.6. Anticanonical contraction to a rank-one klt del Pezzo surface](../source/manuscript.tex#L491) | Formalized | [AnticanonicalContraction](../KltDP/Manuscript/S02/AnticanonicalContraction.lean) |
| `thm:numerical-contraction` | [2.7. Numerical rank-one contraction on a rational surface](../source/manuscript.tex#L560) | Formalized | [NumericalContraction](../KltDP/Manuscript/S02/NumericalContraction.lean) |
| `lem:projection` | [2.8. Rank-one projection identity](../source/manuscript.tex#L610) | Formalized | [Projection](../KltDP/Manuscript/S02/Projection.lean) |
| `lem:exterior-null-curves` | [2.9. Null curves outside the minimal exceptional divisor](../source/manuscript.tex#L638) | Formalized | [ExteriorNullCurves](../KltDP/Manuscript/S02/ExteriorNullCurves.lean) |
| `lem:primitive-square-zero` | [3.1. A nef divisor of square zero and canonical degree minus two](../source/manuscript.tex#L675) | Formalized; isolated clauses | [PrimitiveSquareZero](../KltDP/Manuscript/S03/PrimitiveSquareZero.lean) |
| `lem:ruling-fibers` | [3.2. Primitive rational rulings and their fibers](../source/manuscript.tex#L714) | Formalized; isolated clauses | [RulingFibers](../KltDP/Manuscript/S03/RulingFibers.lean) |
| `lem:nef-threshold` | [3.3. The least exterior degree is the nef anticanonical threshold](../source/manuscript.tex#L766) | Formalized | [NefThresholdArithmetic](../KltDP/Manuscript/S03/NefThresholdArithmetic.lean), [NefThreshold](../KltDP/Manuscript/S03/NefThreshold.lean); 1 further file in the declaration record |
| `lem:elementary-discrepancy` | [4.1. Elementary discrepancy bound](../source/manuscript.tex#L844) | Formalized | [DiscrepancyLemmas](../KltDP/Manuscript/S04/DiscrepancyLemmas.lean) |
| `lem:excess-contact` | [4.2. Existence and rigidity of an excess contact](../source/manuscript.tex#L868) | Formalized | [ExcessContact](../KltDP/Manuscript/S04/ExcessContact.lean) |
| `lem:discrepancy-separation` | [4.3. Discrepancy separation in one exceptional component](../source/manuscript.tex#L903) | Formalized | [DiscrepancyLemmas](../KltDP/Manuscript/S04/DiscrepancyLemmas.lean) |
| `lem:exceptional-valency` | [4.4. Valencies of exceptional trees](../source/manuscript.tex#L939) | Formalized | [DiscrepancyLemmas](../KltDP/Manuscript/S04/DiscrepancyLemmas.lean) |
| `thm:one-component-replacement` | [4.5. Replacement of one exceptional component](../source/manuscript.tex#L990) | Formalized | [OneComponentReplacement](../KltDP/Manuscript/S04/OneComponentReplacement.lean) |
| `thm:isolated-node-exchange` | [4.6. The isolated-$A_1$ exchange with its two-curve contraction](../source/manuscript.tex#L1114) | Formalized | [Interfaces](../KltDP/Manuscript/S07/Interfaces.lean), [IsolatedNodeExchange](../KltDP/Manuscript/S04/IsolatedNodeExchange.lean); 2 further files in the declaration record |
| `thm:no-even-nodes` | [5.1. Vanishing of the isolated-node code](../source/manuscript.tex#L1242) | Formalized | [IsolatedNodeVanishing](../KltDP/Geometry/IsolatedNodeVanishing.lean), [PicardIndex](../KltDP/Manuscript/S05/PicardIndex.lean) |
| `lem:picard-index` | [5.2. The full-index obstruction from isolated nodes](../source/manuscript.tex#L1342) | Formalized | [PicardIndex](../KltDP/Manuscript/S05/PicardIndex.lean) |
| `lem:picard-parity` | [5.3. Riemann--Roch parity and the full Picard index](../source/manuscript.tex#L1388) | Formalized | [PicardParity](../KltDP/Manuscript/S05/PicardParity.lean) |
| `lem:eight-curve-forest` | [5.4. An eight-curve weight-two forest has at most four connected components](../source/manuscript.tex#L1442) | Formalized | [EightCurveForest](../KltDP/Manuscript/S05/EightCurveForest.lean) |
| `prop:zero-adjoint` | [5.5. The zero-adjoint three-curve configuration](../source/manuscript.tex#L1483) | Formalized | [ZeroAdjoint](../KltDP/Manuscript/S05/ZeroAdjoint.lean) |
| `lem:square-one-adjoint` | [6.1. The effective adjoint remainder of a square-one configuration](../source/manuscript.tex#L1569) | Formalized | [SquareOneAdjoint](../KltDP/Manuscript/S06/SquareOneAdjoint.lean), [SquareOneBound](../KltDP/Manuscript/S06/SquareOneBound.lean) |
| `prop:square-one-bound` | [6.2. Singular-point bounds for square-one configurations](../source/manuscript.tex#L1641) | Formalized | [SquareOneBound](../KltDP/Manuscript/S06/SquareOneBound.lean) |
| `lem:adjacent-contact-adjoint` | [6.3. The adjacent-contact adjoint](../source/manuscript.tex#L1709) | Formalized | [AdjacentContactAdjoint](../KltDP/Manuscript/S06/AdjacentContactAdjoint.lean) |
| `cor:multiple-contact` | [6.4. The only possible multiple weight-two contact at a shortest curve](../source/manuscript.tex#L1788) | Formalized | [MultipleContact](../KltDP/Manuscript/S06/MultipleContact.lean) |
| `prop:cubic-adjoint` | [6.5. An effective adjoint from three $(-2)$-contacts](../source/manuscript.tex#L1823) | Formalized | [CubicAdjoint](../KltDP/Manuscript/S06/CubicAdjoint.lean) |
| `prop:three-contact-single-component` | [6.6. A singular-point bound for a single exterior adjoint component](../source/manuscript.tex#L1883) | Formalized | [ThreeContactSingleComponent](../KltDP/Manuscript/S06/ThreeContactSingleComponent.lean) |
| `thm:three-contact-descent` | [6.7. Strict adjoint descent from any three weight-two contacts](../source/manuscript.tex#L1932) | Formalized | [ThreeContactDescent](../KltDP/Manuscript/S06/ThreeContactDescent.lean) |
| `lem:forest-count` | [7.1. Connected-component count from a rational ruling](../source/manuscript.tex#L2000) | Formalized | [ForestCount](../KltDP/Manuscript/S07/ForestCount.lean) |
| `lem:bisection-ramification` | [7.2. Ramification of a smooth bisection](../source/manuscript.tex#L2056) | Formalized | [BisectionRamification](../KltDP/Manuscript/S07/BisectionRamification.lean), [HurwitzInput](../KltDP/Manuscript/S07/HurwitzInput.lean) |
| `lem:fiber-degree-equality` | [7.3. Fibers of least possible anticanonical degree](../source/manuscript.tex#L2116) | Formalized | [FiberDegreeEquality](../KltDP/Manuscript/S07/FiberDegreeEquality.lean) |
| `lem:bisection-adjoint` | [7.4. A bisection adjoint is zero or one exterior curve](../source/manuscript.tex#L2174) | Formalized | [BisectionAdjoint](../KltDP/Manuscript/S07/BisectionAdjoint.lean) |
| `thm:two-contact-ruling` | [7.5. The singular-point bound from sections and bisections](../source/manuscript.tex#L2229) | Formalized | [TwoContactRuling](../KltDP/Manuscript/S07/TwoContactRuling.lean), [Interfaces](../KltDP/Manuscript/S07/Interfaces.lean) |
| `thm:adjoint-reduction` | [8.1. A single exterior adjoint curve for a minimal counterexample](../source/manuscript.tex#L2324) | Formalized | [AdjointReduction](../KltDP/Manuscript/S07/AdjointReduction.lean), [AdjointConfiguration](../KltDP/Manuscript/S07/AdjointConfiguration.lean) |
| `lem:rooted-trees` | [9.1. Inverse matrix entries for trees with one higher-weight vertex](../source/manuscript.tex#L2456) | Formalized | [RootedTrees](../KltDP/Manuscript/S09/RootedTrees.lean) |
| `lem:ten-forests` | [9.2. Classification of the candidate weighted forests](../source/manuscript.tex#L2514) | Formalized | [TenCandidateForests](../KltDP/Manuscript/S09/TenCandidateForests.lean), [TenCandidateForestsNonvacuity](../KltDP/Manuscript/S09/TenCandidateForestsNonvacuity.lean); 1 further file in the declaration record |
| `thm:forest-exclusion` | [9.3. The single exterior adjoint configuration is impossible](../source/manuscript.tex#L2782) | Formalized | [ForestExclusion](../KltDP/Manuscript/S08/ForestExclusion.lean) |
| `prop:frobenius-family` | [10.1. Canonical divisors in the Frobenius family](../source/manuscript.tex#L2892) | Formalized | [FrobeniusFamily](../KltDP/Manuscript/S10/FrobeniusFamily.lean) |
| `thm:characteristic-two` | [10.2. Rulings and divisibility on the Keel--McKernan family](../source/manuscript.tex#L3008) | Formalized | [CharacteristicTwo](../KltDP/Manuscript/S10/CharacteristicTwo.lean) |
| `cor:inseparable-covers` | [10.3. Failure of the separability arguments in characteristic two](../source/manuscript.tex#L3086) | Formalized | [InseparableCovers](../KltDP/Manuscript/S10/InseparableCovers.lean) |
| `prop:equality-negative-curves` | [A.1. The thirteen nonexceptional negative curves on the minimal resolution](../source/manuscript.tex#L3156) | Formalized; isolated clauses | [NegativeCurves](../KltDP/Manuscript/S11/NegativeCurves.lean) |
| `prop:equality-adjoints` | [A.2. Adjoint identities and singular-point counts on the equality example](../source/manuscript.tex#L3263) | Formalized; isolated clauses | [EqualityAdjoints](../KltDP/Manuscript/S11/EqualityAdjoints.lean) |
| `cor:equality-lattice` | [A.3. Intersection lattices at equality](../source/manuscript.tex#L3336) | Formalized | [EqualityLattices](../KltDP/Manuscript/S11/EqualityLattices.lean) |
