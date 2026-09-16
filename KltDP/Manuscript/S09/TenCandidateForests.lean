import KltDP.Manuscript.S09.TenForestInvariantClassification
import KltDP.LinearAlgebra.TenForestMatrixRealization

/-!
# Lemma 9.2: the ten candidate weighted forests

This module assembles the original finite weighted-forest classifier,
its unique row label, the actual marked weighted graph isomorphism, the
actual matrix and inverse-source transport, and every displayed invariant.
The hypotheses are the original rational graph hypotheses of
`lem:ten-forests` in the frozen manuscript, lines 2514--2578.

`TenCandidateForestData` is used only as a conclusion. Its remaining
matrix is the actual induced complement of witnessed fixed components
in the original graph. All transports use one actual vertex equivalence.
No geometric realization is asserted. This source is staged until its
VM compilation, elaborated-type review and axiom audit are recorded.
-/

namespace KltDP.Manuscript.S09

open Matrix SimpleGraph KltDP.LinearAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete row conclusion for the candidate-forest lemma.
The row is selected by the theorem; this predicate is never an input to
that theorem. It retains the actual graph witnesses as well as the
marked model isomorphism and all entries of the two invariant tables. -/
def TenCandidateForestData (row : TenForestRow) (G : SimpleGraph V)
    [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ) (C B D : V) (β : ℕ) : Prop :=
  let A := graphWeightMatrix G (fun v => (weight v : ℚ))
  let q := fun v => (weight v : ℚ) - 2
  let p : V → ℚ := threeMarkedSource C B D
  let delta := A.det * (dotProduct p (A⁻¹ *ᵥ p) - 1)
  row.Realized G weight coeff C B D β ∧
    β = row.beta ∧
    1 - dotProduct p coeff = row.length ∧
    2 - (β : ℚ) + dotProduct q coeff = row.volume ∧
    dotProduct p (A⁻¹ *ᵥ p) = row.green ∧
    A.det = row.exceptionalDet ∧
    (borderedGram A p (-1)).det = row.borderedDet ∧
    (∃ f : row.modelGraph ≃g G,
      f row.modelC = C ∧ f row.modelB = B ∧ f row.modelD = D ∧
      (∀ v, weight (f v) = row.modelWeight v) ∧
      A.submatrix f f = row.modelMatrix ∧
      A⁻¹.submatrix f f = row.modelMatrix⁻¹ ∧
      (A⁻¹ *ᵥ q) ∘ f = row.modelMatrix⁻¹ *ᵥ row.modelCanonicalSource ∧
      coeff ∘ f = row.modelMatrix⁻¹ *ᵥ row.modelCanonicalSource ∧
      p ∘ f = row.modelMarkedSource ∧
      A.det = row.modelMatrix.det ∧
      dotProduct p (A⁻¹ *ᵥ p) =
        dotProduct row.modelMarkedSource (row.modelMatrix⁻¹ *ᵥ row.modelMarkedSource)) ∧
    (∃ fixed : Finset V, TenForestRemainingVertices row G weight coeff C B D fixed ∧
      (let AZ := graphWeightMatrix (G.induce {v | v ∉ fixed})
         (fun v => (weight v.val : ℚ))
       AZ.det = row.remainingDet ∧ 0 < AZ.det ∧
         delta = row.deltaFactor * AZ.det ∧ delta / AZ.det = row.deltaFactor ∧
         |(borderedGram A p (-1)).det| = delta))

/-- **Lemma 9.2 (`lem:ten-forests`).** Every finite weighted forest under
the original hypotheses has exactly one displayed row, with an actual
marked weighted isomorphism and all scalar, full-lattice and remaining
forest invariants. In particular beta cannot be five. -/
theorem tenCandidateForests
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (β : ℕ)
    (hβ : β = 3 ∨ β = 4 ∨ β = 5) (hcard : Fintype.card V = β + 7)
    (hG : G.IsAcyclic)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = β)
    (hother : ∀ v, v ≠ C → v ≠ B → v ≠ D → weight v = 2 ∨ weight v = 3)
    (hextraCard : (candidateExtraVertices weight C B D).card ≤ 2)
    (hnadjCB : ¬ G.Adj C B) (hnadjCD : ¬ G.Adj C D) (hnadjBD : ¬ G.Adj B D)
    (hseparate : ¬ G.Reachable B D)
    (hdegreeC : G.degree C ≤ 1) (hdegree : ∀ v, G.degree v ≤ 3)
    (hedges : G.edgeFinset.card ≤ β - 1)
    (hboundary : ∃ v, G.Adj C v ∨ G.Adj B v ∨ G.Adj D v)
    (hA : (graphWeightMatrix G (fun v => (weight v : ℚ))).PosDef)
    (hsolve : coeff = (graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
      (fun v => (weight v : ℚ) - 2))
    (hcoeffBounds : ∀ v, 0 ≤ coeff v ∧ coeff v < 1)
    (hvolume : 0 < 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff)
    (hbudget : 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
            threeMarkedSource C B D) - 1) =
        (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    β ≠ 5 ∧ ∃! row : TenForestRow,
      TenCandidateForestData row G weight coeff C B D β := by
  classical
  obtain ⟨row, ⟨hreal, hbeta, hell, hvol, hgreen, hdet, hborder, hremaining⟩, _⟩ :=
    tenForestInvariantClassification G weight coeff C B D β hβ hcard hG
      hC hB hD hother hextraCard hnadjCB hnadjCD hnadjBD hseparate hdegreeC hdegree
      hedges hboundary hA hsolve hcoeffBounds hvolume hbudget hprojection
  have hnotfive : β ≠ 5 := by
    rw [hbeta]
    cases row <;> norm_num [TenForestRow.beta]
  have hBD : B ≠ D := by
    intro h
    subst D
    exact hseparate (.refl B)
  obtain ⟨f, hfC, hfB, hfD, hw, hm, hi, hcanonical, hp, hmodeldet, hmodelgreen⟩ :=
    hreal.matrix_realization hcard hC hB hD hBD
  have hcoeff : coeff ∘ f = row.modelMatrix⁻¹ *ᵥ row.modelCanonicalSource := by
    rw [hsolve]
    exact hcanonical
  refine ⟨hnotfive, row, ?_, ?_⟩
  · exact ⟨hreal, hbeta, hell, hvol, hgreen, hdet, hborder,
      ⟨f, hfC, hfB, hfD, hw, hm, hi, hcanonical, hcoeff, hp, hmodeldet, hmodelgreen⟩,
      hremaining⟩
  · intro other hotherRow
    exact hotherRow.1.unique hreal

end KltDP.Manuscript.S09
