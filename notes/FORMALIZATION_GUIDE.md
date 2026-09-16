# Formalization guide

The Lean project is organized around actual geometric objects and reusable algebra. Integral Picard classes, rational Picard classes and numerical classes are distinct. A rational half-vector does not supply a line bundle, and an intersection matrix does not construct a surface.

## Manuscript results

| Manuscript | Lean entry point | Accepted scope |
| --- | --- | --- |
| Lemma 2.1, Stieltjes inverse positivity | [Stieltjes.lean](../KltDP/Manuscript/S02/Stieltjes.lean) | Real and rational positive-definite matrices with nonpositive off-diagonal entries |
| Lemma 2.2, rational-tree Picard group | [RationalTreePicard.lean](../KltDP/Manuscript/S02/RationalTreePicard.lean) | Actual reduced nodal curves under the explicit component and incidence hypotheses; the component coordinate is a transition exponent |
| Lemma 9.1, rooted-tree inverse entries | [RootedTrees.lean](../KltDP/Manuscript/S09/RootedTrees.lean) | Finite rooted-tree shapes, inverse entries and realization statements |
| Lemma 9.2, ten candidate forests | [TenCandidateForests.lean](../KltDP/Manuscript/S09/TenCandidateForests.lean) and [nonvacuity](../KltDP/Manuscript/S09/TenCandidateForestsNonvacuity.lean) | Classification under the original rational graph hypotheses, marked isomorphisms and nonvacuous rows; surface realization remains separate |

The [complete mapping](PAPER_TO_LEAN.md) lists all 47 named results and all 72 support obligations. An entry marked open can still have substantial supporting modules in this checkpoint.

## Geometry and algebra

| Area | Selected source | Boundary |
| --- | --- | --- |
| Divisors and numerical classes | [RationalPicardIntersection](../KltDP/Geometry/RationalPicardIntersection.lean), [IntegralNumericalClassGroup](../KltDP/Geometry/IntegralNumericalClassGroup.lean) | Pairings and quotient comparisons retain regularity and projectivity hypotheses; finite generation is not obtained from the quotient construction |
| Ampleness | [AmpleSelfIntersectionPositive](../KltDP/Geometry/AmpleSelfIntersectionPositive.lean), [ProjectiveLinePositiveDegreeAmple](../KltDP/Geometry/ProjectiveLinePositiveDegreeAmple.lean) | Positive ample self-intersection and positive-degree ampleness on the original projective line |
| Frobenius graph | [FrobeniusGraphF28](../KltDP/Examples/FrobeniusGraphF28.lean) | Actual graph, rational points, Picard class and contact order |
| Blowup charts | [FrobeniusBlowupDifferentialIntrinsicLeft](../KltDP/Examples/FrobeniusBlowupDifferentialIntrinsicLeft.lean), [right chart](../KltDP/Examples/FrobeniusBlowupDifferentialIntrinsicRight.lean) | Intrinsic differential and exceptional-ideal comparisons on the original charts |
| Characteristic two | [FrobeniusSevenNodes](../KltDP/Examples/FrobeniusSevenNodes.lean) | Constructed curve configuration and Picard parity; no complete contraction theorem or singular-point classification follows |
| Hodge input | [SurfaceHodgeIndexSource](../KltDP/Geometry/SurfaceHodgeIndexSource.lean) | Defines the full integral statement and proves consumers conditional on it; the raw Hodge statement is not proved or admitted |
| Finite algebra | [LinearAlgebra](../KltDP/LinearAlgebra), [Codes](../KltDP/Codes), [Support](../KltDP/Support) | Exact scalar, graph and lattice proofs with explicit hypotheses |
| Compatibility ports | [Compatibility](../KltDP/Compatibility) | Adaptations of existing libraries to the pinned toolchain; upstream notices are retained |

Lean declarations, their complete telescopes and their transitive dependencies determine the scope of a theorem. Some unchanged source comments describe an earlier staged state. The checkpoint certificate and claim registry determine whether a file or result had been accepted at this snapshot.
