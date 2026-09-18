import KltDP.Geometry.KltResolutionExceptionalProjectiveLine
import KltDP.Geometry.KltMinimalResolutionGeometry
import KltDP.Geometry.KltMinimalResolutionWeightedGraph
import KltDP.Geometry.KltMinimalResolutionReducedExceptionalSNC

/-!
# Exceptional geometry with rationality derived from klt

The actual exceptional projective-line isomorphisms are now constructed
from klt and arithmetic adjunction. They discharge the remaining curve
rationality input of the original forest, singular-count, weighted-matrix
and global SNC theorems. The original minimal resolution remains explicit. Its source smoothness
follows from regularity; no resolution-existence assertion is made.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  {π : S.toScheme ⟶ X.toScheme}

/-- The original exceptional forest and exact singular count, with all
exceptional-curve isomorphisms and canonical choices derived internally. -/
theorem IsMinimalResolution.exceptional_forest_and_singular_count_from_klt
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X) :
    Finite (ActualExceptionalIncidence.graph π).ConnectedComponent ∧
      X.singularPoints.card =
        Nat.card (ActualExceptionalIncidence.graph π).ConnectedComponent ∧
      (ActualExceptionalIncidence.graph π).IsAcyclic ∧
      ∀ C D : ActualExceptionalIncidence.Vertices π, C ≠ D →
        S.intersectionPairing hmin.regular
          (S.primeCurveCartier hmin.regular C.val)
          (S.primeCurveCartier hmin.regular D.val) ≤ 1 := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  exact hmin.exceptional_forest_and_singular_count_of_klt hklt
    (hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt hklt)

/-- Weights, positivity and discrepancy coefficients of the original
intersection graph require no separate rationality or matrix data. -/
theorem IsMinimalResolution.exists_weighted_canonical_graph_coefficients_of_klt
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X) :
    letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
      hmin.toIsResolution.exceptionalCurves_finite_of_actualMap.fintype
    letI : DecidableEq (ActualExceptionalIncidence.Vertices π) := Classical.decEq _
    letI : DecidableRel (ActualExceptionalIncidence.graph π).Adj := Classical.decRel _
    let M := NullCurveIntersectionMatrix.intersectionMatrix S hmin.regular
      (fun C : ActualExceptionalIncidence.Vertices π => C.val)
    let w := fun i => -M i i
    let B := KltDP.LinearAlgebra.graphWeightMatrix (ActualExceptionalIncidence.graph π) w
    (∀ i, 2 ≤ w i) ∧ B.PosDef ∧
      ∃ a : ActualExceptionalIncidence.Vertices π → ℚ,
        (∀ i, 0 ≤ a i ∧ a i < 1) ∧ Matrix.mulVec B a = fun i => w i - 2 := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  exact hmin.exists_weighted_canonical_graph_coefficients hklt
    (hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt hklt)

/-- The reduced Cartier sum of all original exceptional primes is SNC;
curve smoothness and the local crossings are both derived. -/
theorem IsMinimalResolution.reduced_exceptional_cartier_snc_from_klt
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X) :
    letI : IsProper π := hmin.toIsResolution.isProper
    let hbir : IsBirationalScheme π :=
      (isBirational_iff_isBirationalScheme π).mp hmin.birational
    letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
      (exceptionalCurves_finite_of_proper_birational π hbir).fintype
    letI : IsLocallyNoetherian S.toScheme := S.isLocallyNoetherian
    IsStrictNormalCrossingsCartier S.toScheme
      (∑ C : ActualExceptionalIncidence.Vertices π,
        S.primeCurveCartier hmin.regular C.val) := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  exact hmin.reduced_exceptional_cartier_snc_of_klt hklt
    (hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt hklt)

end KltDP.Geometry

#check @KltDP.Geometry.IsMinimalResolution.exceptional_forest_and_singular_count_from_klt
#print axioms KltDP.Geometry.IsMinimalResolution.exceptional_forest_and_singular_count_from_klt
#print axioms KltDP.Geometry.IsMinimalResolution.exists_weighted_canonical_graph_coefficients_of_klt
#print axioms KltDP.Geometry.IsMinimalResolution.reduced_exceptional_cartier_snc_from_klt
