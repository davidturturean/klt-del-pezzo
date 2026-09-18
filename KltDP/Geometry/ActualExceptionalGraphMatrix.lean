import KltDP.Geometry.ActualExceptionalForest
import KltDP.LinearAlgebra.WeightedPathTransport

/-!
# The original exceptional matrix is the actual weighted graph matrix

Strict klt canonical rows force every distinct original intersection to
be zero or one. The actual positive-intersection incidence criterion then
identifies the original negative matrix with the existing classifier's
diagonal-minus-adjacency construction, using the actual negative diagonal
as its weights. The coefficients `-d` satisfy its original canonical row.
No matrix identification or graph realization is supplied as a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix

universe u v

namespace KltDP.Geometry.ActualExceptionalGraphMatrix

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hbir : IsBirationalScheme π)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
  {I : Type v} [Fintype I] [DecidableEq I]
  (C : I → S.PrimeCurve) (hinj : Function.Injective C)
  (hcontracted : ∀ i, IsExceptionalCurve π (C i))
  [DecidableRel (NormalProjectiveSurface.curveIncidenceGraph C).Adj]

include hπ hbir hinj hcontracted in
/-- The classifier matrix is the negative of the original intersection
matrix, with the original graph and actual negative diagonal weights. -/
theorem negativeIntersectionMatrix_eq_graphWeightMatrix (d : I → ℚ)
    (hlower : ∀ i, -1 < d i) (hupper : ∀ i, d i ≤ 0)
    (hrow : NullCurveIntersectionMatrix.intersectionMatrix S hregular C *ᵥ d =
      fun i => -NullCurveIntersectionMatrix.intersectionMatrix S hregular C i i - 2) :
    -NullCurveIntersectionMatrix.intersectionMatrix S hregular C =
      KltDP.LinearAlgebra.graphWeightMatrix
        (NormalProjectiveSurface.curveIncidenceGraph C)
        (fun i => -NullCurveIntersectionMatrix.intersectionMatrix S hregular C i i) := by
  have hbound := (ActualExceptionalForest.forest_and_intersection_le_one
    π hπ hbir hregular C hinj hcontracted d hlower hupper hrow).2
  ext i j
  rw [KltDP.LinearAlgebra.graphWeightMatrix_apply]
  by_cases hij : i = j
  · subst j
    simp
  · rw [if_neg hij]
    by_cases hadj : (NormalProjectiveSurface.curveIncidenceGraph C).Adj i j
    · rw [if_pos hadj]
      have hpos := ((S.curveIncidenceGraph_adj_iff_pairing_pos hregular C hinj).mp hadj).2
      have hone : S.intersectionPairing hregular
          (S.primeCurveCartier hregular (C i))
          (S.primeCurveCartier hregular (C j)) = 1 := by
        have hle := hbound i j hij
        omega
      change -(S.intersectionPairing hregular
        (S.primeCurveCartier hregular (C i))
        (S.primeCurveCartier hregular (C j)) : ℚ) = -1
      rw [hone]
      norm_num
    · rw [if_neg hadj]
      have hnonneg := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg
        S hregular (C i) (C j) (fun heq => hij (hinj heq))
      have hnotpos : ¬ 0 < S.intersectionPairing hregular
          (S.primeCurveCartier hregular (C i))
          (S.primeCurveCartier hregular (C j)) := by
        intro hpos
        exact hadj ((S.curveIncidenceGraph_adj_iff_pairing_pos hregular C hinj).mpr ⟨hij, hpos⟩)
      have hzero : S.intersectionPairing hregular
          (S.primeCurveCartier hregular (C i))
          (S.primeCurveCartier hregular (C j)) = 0 := by omega
      change -(S.intersectionPairing hregular
        (S.primeCurveCartier hregular (C i))
        (S.primeCurveCartier hregular (C j)) : ℚ) = 0
      rw [hzero]
      norm_num

include hπ hbir hinj hcontracted in
/-- The original negative discrepancy vector satisfies the actual
weighted graph's canonical equation. -/
theorem graphWeightMatrix_canonical_row (d : I → ℚ)
    (hlower : ∀ i, -1 < d i) (hupper : ∀ i, d i ≤ 0)
    (hrow : NullCurveIntersectionMatrix.intersectionMatrix S hregular C *ᵥ d =
      fun i => -NullCurveIntersectionMatrix.intersectionMatrix S hregular C i i - 2) :
    KltDP.LinearAlgebra.graphWeightMatrix
        (NormalProjectiveSurface.curveIncidenceGraph C)
        (fun i => -NullCurveIntersectionMatrix.intersectionMatrix S hregular C i i) *ᵥ (-d) =
      fun i => -NullCurveIntersectionMatrix.intersectionMatrix S hregular C i i - 2 := by
  rw [← negativeIntersectionMatrix_eq_graphWeightMatrix
    π hπ hbir hregular C hinj hcontracted d hlower hupper hrow,
    Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg]
  exact hrow

end KltDP.Geometry.ActualExceptionalGraphMatrix

#print axioms KltDP.Geometry.ActualExceptionalGraphMatrix.negativeIntersectionMatrix_eq_graphWeightMatrix
