import KltDP.LinearAlgebra.FamilyEDeterminants

/-!
# The four family-E shapes paired with their actual determinants

This preserves the actual edge witnesses, isolation and leftover counts
of each E1--E4 completion together with its own exceptional and signed
bordered determinants. The graph classification and Green energy are
obtained from the actual source row and projection equations. No table
membership, block determinant or Green value is an input.

The reused determinant helpers compute each actual canonical edge pattern,
and the fixed graph block contributes 360. Eleven exceptional vertices
account for the negative sign of every full bordered determinant.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An output relation retaining the actual E1--E4 edge and isolation
witnesses alongside the determinant pair for that very same completion. -/
def FiveVertexForestShapeDet (G : SimpleGraph V) [DecidableRel G.Adj]
    (exceptional bordered : ℚ) : Prop :=
  (G.edgeFinset = ∅ ∧ exceptional = 11520 ∧ bordered = -1728) ∨
  (∃ x y, x ≠ y ∧ G.edgeFinset = {s(x, y)} ∧
    (Finset.univ \ ({x, y} : Finset V)).card = 3 ∧
    (∀ v ∉ ({x, y} : Finset V), ∀ w, ¬ G.Adj v w) ∧
    exceptional = 8640 ∧ bordered = -1296) ∨
  (∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ G.edgeFinset = {s(x, y), s(y, z)} ∧
    (Finset.univ \ ({x, y, z} : Finset V)).card = 2 ∧
    (∀ v ∉ ({x, y, z} : Finset V), ∀ w, ¬ G.Adj v w) ∧
    exceptional = 5760 ∧ bordered = -864) ∨
  (∃ x y z w, x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧
    G.edgeFinset = {s(x, y), s(z, w)} ∧
    (Finset.univ \ ({x, y, z, w} : Finset V)).card = 1 ∧
    (∀ v ∉ ({x, y, z, w} : Finset V), ∀ u, ¬ G.Adj v u) ∧
    exceptional = 6480 ∧ bordered = -972)

/-- The complete family-E source conclusion, retaining the exact pairing
between each actual leftover forest and its two actual determinants. -/
theorem familyE_source_rows
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G.Reachable]
    (weight coeff : V → ℚ) (C B D T U : V)
    (hcard : Fintype.card V = 11)
    (hA : IsUnit (graphWeightMatrix G weight)) (hG : G.IsAcyclic)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hedges : G.edgeFinset.card ≤ 3)
    (hB : weight B = 3) (hD : weight D = 4) (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hcanonical : ∀ v, G.Reachable C v → weight v = 2)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2)
    (hTsingle : ∀ v, G.Reachable T v → v ≠ T → weight v = 2)
    (hUsingle : ∀ v, G.Reachable U v → v ≠ U → weight v = 2)
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2)
    (hvolume : 0 < -2 + dotProduct (fun i => weight i - 2) coeff)
    (hbudget : -2 + dotProduct (fun i => weight i - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (-2 + dotProduct (fun i => weight i - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) - 1) =
      (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    ∃ M, weight M = 2 ∧ G.Adj B M ∧ G.neighborFinset B = {M} ∧
      G.neighborFinset M = {B} ∧
      (∀ v, G.Reachable B v ↔ v = B ∨ v = M) ∧
      (∀ v, ¬ G.Adj C v) ∧ (∀ v, ¬ G.Adj D v) ∧
      (∀ v, ¬ G.Adj T v) ∧ (∀ v, ¬ G.Adj U v) ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 10 ∧
      -2 + dotProduct (fun i => weight i - 2) coeff = 1 / 15 ∧
      dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) = 23 / 20 ∧
      (let fixed : Finset V := {C, B, M, D, T, U}
       let Z := G.induce {v | v ∉ fixed}
       fixed.card = 6 ∧ Fintype.card {v | v ∉ fixed} = 5 ∧
         (∀ v : {v | v ∉ fixed}, weight v.val = 2) ∧
         Z.edgeFinset.card = G.edgeFinset.card - 1 ∧ FiveVertexForestShapeDet Z
           (graphWeightMatrix G weight).det
           (borderedGram (graphWeightMatrix G weight) (threeMarkedSource C B D) (-1)).det) := by
  classical
  obtain ⟨M, hM, hBM, hnB, hnM, hreach, hCiso, hDiso, hTiso, hUiso, hell, hvol, hg,
      hremaining⟩ := familyE_complete_forest G weight coeff C B D T U hcard hA hG hrow
    hedges hB hD hT hU hTB hTD hUB hUD hTU hcanonical hBsingle hDsingle hTsingle
    hUsingle hother hvolume hbudget hprojection
  let fixed : Finset V := {C, B, M, D, T, U}
  let Z := G.induce {v | v ∉ fixed}
  obtain ⟨hfixedCard, hZcard, hZweights, hcount, hshape⟩ := hremaining
  have hfactor := familyE_fixed_det_factor G weight C B M D T U
    (hcanonical C (.refl C)) hB hM hD hT hU hTB hUB hTU hBM hnB hnM
    hCiso hDiso hTiso hUiso
  have hweights : (fun v : {v | v ∉ fixed} => weight v.val) = fun _ => (2 : ℚ) :=
    funext hZweights
  change (graphWeightMatrix G weight).det = 360 *
    (graphWeightMatrix Z (fun v => weight v.val)).det at hfactor
  rw [hweights] at hfactor
  have hb := det_minusOne_borderedGram hA (threeMarkedSource C B D)
  rw [hcard, hg] at hb
  norm_num at hb
  refine ⟨M, hM, hBM, hnB, hnM, hreach, hCiso, hDiso, hTiso, hUiso, hell, hvol, hg,
    hfixedCard, hZcard, hZweights, hcount, ?_⟩
  rcases hshape with he | ⟨x, y, hxy, he, hout, hiso⟩ |
    ⟨x, y, z, hxy, hxz, hyz, he, hout, hiso⟩ |
    ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, he, hout, hiso⟩
  · have hz := canonical_empty_det Z he
    rw [hZcard] at hz
    norm_num at hz
    exact Or.inl ⟨he, by linarith only [hfactor, hz], by linarith only [hfactor, hz, hb]⟩
  · have hz := canonical_single_edge_det Z x y hxy he
    rw [hZcard] at hz
    norm_num at hz
    exact Or.inr (Or.inl ⟨x, y, hxy, he, hout, hiso,
      by linarith only [hfactor, hz], by linarith only [hfactor, hz, hb]⟩)
  · have hz := canonical_two_path_det Z x y z hxy hxz hyz he
    rw [hZcard] at hz
    norm_num at hz
    exact Or.inr (Or.inr (Or.inl ⟨x, y, z, hxy, hxz, hyz, he, hout, hiso,
      by linarith only [hfactor, hz], by linarith only [hfactor, hz, hb]⟩))
  · have hz := canonical_disjoint_edges_det Z x y z w hxy hxz hxw hyz hyw hzw he
    rw [hZcard] at hz
    norm_num at hz
    exact Or.inr (Or.inr (Or.inr ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, he, hout, hiso,
      by linarith only [hfactor, hz], by linarith only [hfactor, hz, hb]⟩))

end KltDP.LinearAlgebra
