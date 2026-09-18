import KltDP.LinearAlgebra.CanonicalRowForest
import KltDP.Geometry.ActualExceptionalNegativeDefinite
import KltDP.Geometry.ActualExceptionalIncidence
import KltDP.Geometry.CurveIncidencePairing

/-!
# The original exceptional graph is a forest from actual discrepancy rows

The actual proper birational map supplies negative quadratic values.
Distinct original primes supply nonnegative off-diagonal intersections,
and an actual graph edge has positive integral intersection, hence at least
one. The canonical-row argument therefore proves graph acyclicity and
intersection at most one for distinct actual contracted curves.

The remaining inputs are the actual rational-adjunction rows and the klt
discrepancy interval for the original matrix. No graph, matrix-sign, forest,
or intersection bound is supplied. The all-prime endpoint constructs the
finite family from the original morphism itself. This proves the incidence
forest; rationality and local transverse intersection remain separate.

The negative-quadratic producer retains the selected isolated Hodge
dependency. The finite algebra argument itself uses no literature axiom.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix

universe u v

namespace KltDP.Geometry.ActualExceptionalForest

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hbir : IsBirationalScheme π)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
  {I : Type v} [Fintype I]
  (C : I → S.PrimeCurve) (hinj : Function.Injective C)
  (hcontracted : ∀ i, IsExceptionalCurve π (C i))

include hinj in
private theorem matrix_offDiagonal_nonneg (i j : I) (hij : i ≠ j) :
    0 ≤ NullCurveIntersectionMatrix.intersectionMatrix S hregular C i j := by
  have h := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg
    S hregular (C i) (C j) (fun heq => hij (hinj heq))
  change (0 : ℚ) ≤ (S.intersectionPairing hregular
    (S.primeCurveCartier hregular (C i)) (S.primeCurveCartier hregular (C j)) : ℚ)
  exact_mod_cast h

include hπ hbir hinj hcontracted in
/-- Actual canonical discrepancy rows make the original incidence graph
acyclic and bound every original distinct-prime intersection by one. -/
theorem forest_and_intersection_le_one (d : I → ℚ)
    (hlower : ∀ i, -1 < d i) (hupper : ∀ i, d i ≤ 0)
    (hrow : NullCurveIntersectionMatrix.intersectionMatrix S hregular C *ᵥ d =
      fun i => -NullCurveIntersectionMatrix.intersectionMatrix S hregular C i i - 2) :
    (NormalProjectiveSurface.curveIncidenceGraph C).IsAcyclic ∧
      ∀ i j, i ≠ j → S.intersectionPairing hregular
        (S.primeCurveCartier hregular (C i))
        (S.primeCurveCartier hregular (C j)) ≤ 1 := by
  classical
  let M := NullCurveIntersectionMatrix.intersectionMatrix S hregular C
  have hoff : ∀ i j, i ≠ j → 0 ≤ M i j :=
    matrix_offDiagonal_nonneg hregular C hinj
  have hnegative : ∀ a : I → ℚ, a ≠ 0 → dotProduct a (M *ᵥ a) < 0 :=
    ActualExceptionalNegativeDefinite.quadraticForm_neg
      π hπ hbir hregular C hinj hcontracted
  refine ⟨?_, ?_⟩
  · apply KltDP.LinearAlgebra.CanonicalRowForest.isAcyclic M hoff hnegative
      d hlower hupper hrow (NormalProjectiveSurface.curveIncidenceGraph C)
    intro i j hij
    have hpos := ((S.curveIncidenceGraph_adj_iff_pairing_pos hregular C hinj).mp hij).2
    have hone : (1 : ℤ) ≤ S.intersectionPairing hregular
        (S.primeCurveCartier hregular (C i))
        (S.primeCurveCartier hregular (C j)) := by omega
    change (1 : ℚ) ≤ (S.intersectionPairing hregular
      (S.primeCurveCartier hregular (C i)) (S.primeCurveCartier hregular (C j)) : ℚ)
    exact_mod_cast hone
  · intro i j hij
    have hsymm : ∀ i j, M i j = M j i := by
      intro i j
      change (S.intersectionPairing hregular
        (S.primeCurveCartier hregular (C i))
        (S.primeCurveCartier hregular (C j)) : ℚ) =
          (S.intersectionPairing hregular
            (S.primeCurveCartier hregular (C j))
            (S.primeCurveCartier hregular (C i)) : ℚ)
      rw [S.intersectionPairing_symm hregular]
    have hlt := KltDP.LinearAlgebra.CanonicalRowForest.offDiagonal_lt_two
      M hsymm hoff hnegative d hlower hupper hrow i j hij
    change (S.intersectionPairing hregular
      (S.primeCurveCartier hregular (C i)) (S.primeCurveCartier hregular (C j)) : ℚ) < 2 at hlt
    have hltZ : S.intersectionPairing hregular
        (S.primeCurveCartier hregular (C i))
        (S.primeCurveCartier hregular (C j)) < 2 := by exact_mod_cast hlt
    omega

include hπ in
/-- The endpoint uses all actual contracted primes and derives their finite
indexing from the actual map. The original graph is a forest; no forest or
chosen exceptional list enters the hypotheses. -/
theorem actual_graph_forest_and_intersection_le_one
    (d : ActualExceptionalIncidence.Vertices π → ℚ)
    (hlower : ∀ i, -1 < d i) (hupper : ∀ i, d i ≤ 0) :
    letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
      (exceptionalCurves_finite_of_proper_birational π hbir).fintype
    let M := NullCurveIntersectionMatrix.intersectionMatrix S hregular
      (fun C : ActualExceptionalIncidence.Vertices π => C.val)
    (M *ᵥ d = fun i => -M i i - 2) →
      (ActualExceptionalIncidence.graph π).IsAcyclic ∧
        ∀ i j : ActualExceptionalIncidence.Vertices π, i ≠ j →
          S.intersectionPairing hregular
            (S.primeCurveCartier hregular i.val)
            (S.primeCurveCartier hregular j.val) ≤ 1 := by
  classical
  letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
    (exceptionalCurves_finite_of_proper_birational π hbir).fintype
  dsimp only
  intro hrow
  exact forest_and_intersection_le_one π hπ hbir hregular
    Subtype.val Subtype.val_injective (fun C => C.property) d hlower hupper hrow

end KltDP.Geometry.ActualExceptionalForest

#print axioms KltDP.Geometry.ActualExceptionalForest.actual_graph_forest_and_intersection_le_one
