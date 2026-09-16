import KltDP.LinearAlgebra.ABDeterminants

/-!
# The reachable single-extra branch of the candidate-forest theorem

For beta three and one additional weight-three vertex T, an actual
connection from C to T gives precisely A1, A2, or B. The statements below
combine the actual graph allocation, source values, and exceptional and
bordered determinants. Neither a component shape nor an inverse entry nor
a numerical table row is a hypothesis.

The second entry point uses the manuscript's actual definition lambda=A^-1 q
and derives the row equation required by the first entry point.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [StarRing 𝕜] [TrivialStar 𝕜]

/-- The three complete graph rows in the beta-three, single-extra branch
where C actually reaches T. Positivity and the original volume budget
force the shapes and all displayed values; a projection identity is not
needed for this branch. The bordered determinants have their actual sign. -/
theorem beta_three_reachable_extra_source_rows
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (coeff : V → 𝕜) (C B D T : V) (hcard : Fintype.card V = 10)
    (hweight : ∀ i, 2 ≤ weight i) (hC : weight C = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hTB : T ≠ B) (hTD : T ≠ D)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2)
    (hseparate : ¬ G.Reachable B D) (hreach : G.Reachable C T)
    (hedges : G.edgeFinset.card ≤ 2)
    (hA : (graphWeightMatrix G (fun i => (weight i : 𝕜))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hlength : 0 < 1 - dotProduct (threeMarkedSource C B D) coeff)
    (hbudget : -1 + dotProduct (fun i => (weight i : 𝕜) - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff) :
    let A := graphWeightMatrix G (fun i => (weight i : 𝕜))
    let p := threeMarkedSource C B D
    let ell := 1 - dotProduct p coeff
    let vol := -1 + dotProduct (fun i => (weight i : 𝕜) - 2) coeff
    let green := dotProduct p (A⁻¹ *ᵥ p)
    (∀ u, ¬ G.Adj B u) ∧ (∀ u, ¬ G.Adj D u) ∧
    ((G.edgeFinset = {s(C, T)} ∧
      (Finset.univ \ ({C, T, B, D} : Finset V)).card = 6 ∧
      (∀ v ∈ Finset.univ \ ({C, T, B, D} : Finset V),
        weight v = 2 ∧ ∀ u, ¬ G.Adj v u) ∧
      ell = 2 / 15 ∧ vol = 1 / 15 ∧ green = 19 / 15 ∧
      A.det = 2880 ∧ (borderedGram A p (-1)).det = 768) ∨
    (∃ u v, u ≠ v ∧ u ∉ ({C, T, B, D} : Finset V) ∧
      v ∉ ({C, T, B, D} : Finset V) ∧ weight u = 2 ∧ weight v = 2 ∧
      G.edgeFinset = {s(C, T), s(u, v)} ∧
      (Finset.univ \ ({u, v, C, T, B, D} : Finset V)).card = 4 ∧
      (∀ w ∈ Finset.univ \ ({u, v, C, T, B, D} : Finset V),
        weight w = 2 ∧ ∀ z, ¬ G.Adj w z) ∧
      ell = 2 / 15 ∧ vol = 1 / 15 ∧ green = 19 / 15 ∧
      A.det = 2160 ∧ (borderedGram A p (-1)).det = 576) ∨
    (∃ M, weight M = 2 ∧ G.Adj C M ∧ G.Adj M T ∧
      G.edgeFinset = {s(C, M), s(M, T)} ∧
      (Finset.univ \ ({C, M, T, B, D} : Finset V)).card = 5 ∧
      (∀ v ∈ Finset.univ \ ({C, M, T, B, D} : Finset V),
        weight v = 2 ∧ ∀ u, ¬ G.Adj v u) ∧
      ell = 4 / 21 ∧ vol = 2 / 21 ∧ green = 29 / 21 ∧
      A.det = 2016 ∧ (borderedGram A p (-1)).det = 768)) := by
  classical
  dsimp only
  have hell : 0 < 1 - coeff C - coeff B - coeff D := by
    rw [threeMarkedSource_dotProduct] at hlength
    linarith only [hlength]
  have hv : -1 + dotProduct (fun i => (weight i : 𝕜) - 2) coeff ≤
      1 - coeff C - coeff B - coeff D := by
    rw [threeMarkedSource_dotProduct] at hbudget
    linarith only [hbudget]
  by_cases hCT : G.Adj C T
  · obtain ⟨_, hBiso, hDiso, he, hv', hg⟩ :=
      beta_three_adjacent_extra_data G weight coeff C B D T hweight hC hB hD hT
        hTB hTD hother hseparate hCT hedges hA hrow hcoeff hell hv
    refine ⟨hBiso, hDiso, ?_⟩
    rcases beta_three_adjacent_extra_determinants G weight coeff C B D T hcard
      hweight hC hB hD hT hTB hTD hother hseparate hCT hedges hA hrow hcoeff hell hv with
      ⟨hedge, hcount, hremaining, hdet, hborder⟩ |
      ⟨u, v, huv, hu, hvout, hu2, hv2, hedge, hcount, hremaining, hdet, hborder⟩
    · exact Or.inl ⟨hedge, hcount, hremaining, he, hv', hg, hdet, hborder⟩
    · exact Or.inr (Or.inl
        ⟨u, v, huv, hu, hvout, hu2, hv2, hedge, hcount, hremaining,
          he, hv', hg, hdet, hborder⟩)
  · have hBD : B ≠ D := by
      intro h
      subst D
      exact hseparate (SimpleGraph.Reachable.refl B)
    obtain ⟨M, hM, hCM, hMT, hedge, hBiso, hDiso, he, hv', hg⟩ :=
      beta_three_nonadjacent_extra_data G weight coeff C B D T hweight hC hB hD hT
        hTB hTD hother hseparate hreach hCT hedges hA hrow hcoeff hell hv
    obtain ⟨hcount, hremaining⟩ := familyB_remaining_vertices G weight C M T B D hcard
      hC hM hT hB hD hTB hTD hBD hCM hMT hedge hother
    have hdet := familyB_exceptional_det (𝕜 := 𝕜) G weight C M T B D hcard
      hC hM hT hB hD hTB hTD hBD hCM hMT hedge hother
    have hborder :
        (borderedGram (graphWeightMatrix G (fun i => (weight i : 𝕜)))
          (threeMarkedSource C B D) (-1)).det = 768 := by
      rw [bordered_det_of_ten_vertices _ _ (isUnit_of_posDef hA) hcard, hdet, hg]
      norm_num
    exact ⟨hBiso, hDiso, Or.inr (Or.inr
      ⟨M, hM, hCM, hMT, hedge, hcount, hremaining, he, hv', hg, hdet, hborder⟩)⟩

/-- The same complete A1/A2/B conclusion starting from the manuscript's
inverse-defined canonical vector. Its full row equation follows from
positive definiteness, rather than being another premise. -/
theorem beta_three_reachable_extra_inverse_source_rows
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (C B D T : V) (hcard : Fintype.card V = 10)
    (hweight : ∀ i, 2 ≤ weight i) (hC : weight C = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hTB : T ≠ B) (hTD : T ≠ D)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2)
    (hseparate : ¬ G.Reachable B D) (hreach : G.Reachable C T)
    (hedges : G.edgeFinset.card ≤ 2)
    (hA : (graphWeightMatrix G (fun i => (weight i : 𝕜))).PosDef) :
    let A := graphWeightMatrix G (fun i => (weight i : 𝕜))
    let q := fun i => (weight i : 𝕜) - 2
    let coeff := A⁻¹ *ᵥ q
    let p := threeMarkedSource C B D
    let ell := 1 - dotProduct p coeff
    let vol := -1 + dotProduct q coeff
    let green := dotProduct p (A⁻¹ *ᵥ p)
    (∀ i, 0 ≤ coeff i) → 0 < ell → vol ≤ ell →
    (∀ u, ¬ G.Adj B u) ∧ (∀ u, ¬ G.Adj D u) ∧
    ((G.edgeFinset = {s(C, T)} ∧
      (Finset.univ \ ({C, T, B, D} : Finset V)).card = 6 ∧
      (∀ v ∈ Finset.univ \ ({C, T, B, D} : Finset V),
        weight v = 2 ∧ ∀ u, ¬ G.Adj v u) ∧
      ell = 2 / 15 ∧ vol = 1 / 15 ∧ green = 19 / 15 ∧
      A.det = 2880 ∧ (borderedGram A p (-1)).det = 768) ∨
    (∃ u v, u ≠ v ∧ u ∉ ({C, T, B, D} : Finset V) ∧
      v ∉ ({C, T, B, D} : Finset V) ∧ weight u = 2 ∧ weight v = 2 ∧
      G.edgeFinset = {s(C, T), s(u, v)} ∧
      (Finset.univ \ ({u, v, C, T, B, D} : Finset V)).card = 4 ∧
      (∀ w ∈ Finset.univ \ ({u, v, C, T, B, D} : Finset V),
        weight w = 2 ∧ ∀ z, ¬ G.Adj w z) ∧
      ell = 2 / 15 ∧ vol = 1 / 15 ∧ green = 19 / 15 ∧
      A.det = 2160 ∧ (borderedGram A p (-1)).det = 576) ∨
    (∃ M, weight M = 2 ∧ G.Adj C M ∧ G.Adj M T ∧
      G.edgeFinset = {s(C, M), s(M, T)} ∧
      (Finset.univ \ ({C, M, T, B, D} : Finset V)).card = 5 ∧
      (∀ v ∈ Finset.univ \ ({C, M, T, B, D} : Finset V),
        weight v = 2 ∧ ∀ u, ¬ G.Adj v u) ∧
      ell = 4 / 21 ∧ vol = 2 / 21 ∧ green = 29 / 21 ∧
      A.det = 2016 ∧ (borderedGram A p (-1)).det = 768)) := by
  classical
  dsimp only
  intro hcoeff hlength hbudget
  let A := graphWeightMatrix G (fun i => (weight i : 𝕜))
  let q := fun i => (weight i : 𝕜) - 2
  letI : Invertible A := (isUnit_of_posDef hA).invertible
  have hrow : A *ᵥ (A⁻¹ *ᵥ q) = q := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  exact beta_three_reachable_extra_source_rows G weight (A⁻¹ *ᵥ q) C B D T hcard
    hweight hC hB hD hT hTB hTD hother hseparate hreach hedges hA hrow
    hcoeff hlength hbudget

end KltDP.LinearAlgebra
