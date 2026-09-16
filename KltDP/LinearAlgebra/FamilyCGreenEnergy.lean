import KltDP.LinearAlgebra.FamilyCDeterminants

/-!
# Actual marked Green energy for family C

The full inverse applied to the actual three-marked source solves its
matrix equation. On the isolated canonical marked vertex and the two
closed weight-(3,2) edges, those actual rows determine the marked solution
coordinates as 1/2, 2/5, and 2/5. Their sum is the actual Green energy 13/10.
No inverse entry or energy is assumed.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The actual family-C marked Green energy, derived from the full inverse
equation and actual component adjacency. No hypothesis concerns unmarked
components, except invertibility of the full actual matrix. -/
theorem familyC_marked_green_energy
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜)
    (C B L D M : V)
    (hA : IsUnit (graphWeightMatrix G weight))
    (hC : weight C = 2) (hB : weight B = 3) (hL : weight L = 2)
    (hD : weight D = 3) (hM : weight M = 2) (hBD : B ≠ D)
    (hCiso : ∀ v, ¬ G.Adj C v)
    (hBL : G.Adj B L) (hDM : G.Adj D M)
    (hnB : G.neighborFinset B = {L}) (hnL : G.neighborFinset L = {B})
    (hnD : G.neighborFinset D = {M}) (hnM : G.neighborFinset M = {D}) :
    dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) = 13 / 10 := by
  letI : Invertible (graphWeightMatrix G weight) := hA.invertible
  let x := (graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D
  have hrow : graphWeightMatrix G weight *ᵥ x = threeMarkedSource C B D := by
    dsimp only [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hCB : C ≠ B := by intro h; have := congrArg weight h; linarith
  have hCD : C ≠ D := by intro h; have := congrArg weight h; linarith
  have hLB : L ≠ B := Ne.symm hBL.ne
  have hLD : L ≠ D := by intro h; have := congrArg weight h; linarith
  have hMB : M ≠ B := by intro h; have := congrArg weight h; linarith
  have hMD : M ≠ D := Ne.symm hDM.ne
  have hLC : L ≠ C := by intro h; subst L; exact hCiso B hBL.symm
  have hMC : M ≠ C := by intro h; subst M; exact hCiso D hDM.symm
  have hpC : threeMarkedSource (𝕜 := 𝕜) C B D C = 1 := by
    simp [threeMarkedSource, hCB, hCD]
  have hpB : threeMarkedSource (𝕜 := 𝕜) C B D B = 1 := by
    simp [threeMarkedSource, Ne.symm hCB, hBD]
  have hpD : threeMarkedSource (𝕜 := 𝕜) C B D D = 1 := by
    simp [threeMarkedSource, Ne.symm hCD, Ne.symm hBD]
  have hpL : threeMarkedSource (𝕜 := 𝕜) C B D L = 0 := by
    simp [threeMarkedSource, hLC, hLB, hLD]
  have hpM : threeMarkedSource (𝕜 := 𝕜) C B D M = 0 := by
    simp [threeMarkedSource, hMC, hMB, hMD]
  have hc := graph_isolated_row G weight x (threeMarkedSource C B D) hrow C hCiso
  rw [hC, hpC] at hc
  have hb := congrFun hrow B
  have hl := congrFun hrow L
  have hd := congrFun hrow D
  have hm := congrFun hrow M
  rw [graphWeightMatrix_mulVec_apply, hnB, Finset.sum_singleton, hB, hpB] at hb
  rw [graphWeightMatrix_mulVec_apply, hnL, Finset.sum_singleton, hL, hpL] at hl
  rw [graphWeightMatrix_mulVec_apply, hnD, Finset.sum_singleton, hD, hpD] at hd
  rw [graphWeightMatrix_mulVec_apply, hnM, Finset.sum_singleton, hM, hpM] at hm
  have hc' : x C = 1 / 2 := by linarith only [hc]
  have hb' : x B = 2 / 5 := by linarith only [hb, hl]
  have hd' : x D = 2 / 5 := by linarith only [hd, hm]
  change dotProduct (threeMarkedSource C B D) x = _
  rw [threeMarkedSource_dotProduct, hc', hb', hd']
  norm_num

/-- The original full source equations and projection identity imply the
beta-three, one-extra scalar identity for the actual diagonal Green entries.
All scalar substitutions are conclusions of the existing component lemma. -/
theorem beta_three_one_extra_source_scalar_identity
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight coeff : V → 𝕜)
    (C B D T : V)
    (hA : IsUnit (graphWeightMatrix G weight))
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hTB : T ≠ B) (hTD : T ≠ D)
    (hCB : ¬ G.Reachable C B) (hCD : ¬ G.Reachable C D)
    (hBD : ¬ G.Reachable B D)
    (hcanonical : ∀ v, G.Reachable C v → weight v = 2)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2)
    (hTsingle : ∀ v, G.Reachable T v → v ≠ T → weight v = 2)
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2)
    (hprojection :
      (-1 + dotProduct (fun i => weight i - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) - 1) =
        (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    ((graphWeightMatrix G weight)⁻¹ B B + (graphWeightMatrix G weight)⁻¹ D D - 2 / 3) *
        ((graphWeightMatrix G weight)⁻¹ C C + 1 / 3) +
      ((graphWeightMatrix G weight)⁻¹ T T - 1 / 3) *
        ((graphWeightMatrix G weight)⁻¹ C C - 1 / 3 +
          ((graphWeightMatrix G weight)⁻¹ B B +
            (graphWeightMatrix G weight)⁻¹ D D - 2 / 3)) = 1 / 9 := by
  obtain ⟨hl, hv, hg⟩ := separated_graph_block_identities G weight coeff C B D {T} 3
    hA hrow hB hD (by norm_num) hCB hCD hBD hcanonical hBsingle hDsingle
    (fun t ht => by
      have heq := Finset.mem_singleton.mp ht
      subst t
      exact ⟨hTB, hTD, hT⟩)
    (fun t ht => by
      have heq := Finset.mem_singleton.mp ht
      subst t
      exact hTsingle)
    (fun i hiB hiD hiT => hother i hiB hiD
      (by simpa only [Finset.mem_singleton] using hiT))
  simp only [Finset.sum_singleton] at hv
  norm_num at hl hv hg
  rw [hl, hv, hg] at hprojection
  nlinarith only [hprojection]

/-- The entire family-C graph and all of its scalar/determinant row values
follow from the original full matrix equation and projection identity,
after the actual component separation has been established. This theorem
assumes neither a component shape nor a Green entry nor a determinant. -/
theorem beta_three_one_extra_source_familyC
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G.Reachable]
    (weight coeff : V → ℚ) (C B D T : V)
    (hcard : Fintype.card V = 10)
    (hA : IsUnit (graphWeightMatrix G weight)) (hG : G.IsAcyclic)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcanonical : ∀ v, G.Reachable C v → weight v = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2)
    (hTsingle : ∀ v, G.Reachable T v → v ≠ T → weight v = 2)
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2)
    (hseparate : ∀ i j : Fin 4, i ≠ j →
      ¬ G.Reachable (![C, B, D, T] i) (![C, B, D, T] j))
    (hedges : G.edgeFinset.card ≤ 2)
    (hprojection :
      (-1 + dotProduct (fun i => weight i - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) - 1) =
        (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    ∃ L M, weight L = 2 ∧ weight M = 2 ∧
      (∀ v, ¬ G.Adj C v) ∧ (∀ v, ¬ G.Adj T v) ∧
      G.Adj B L ∧ G.Adj D M ∧
      G.neighborFinset B = {L} ∧ G.neighborFinset L = {B} ∧
      G.neighborFinset D = {M} ∧ G.neighborFinset M = {D} ∧
      G.edgeFinset = {s(B, L), s(D, M)} ∧
      (Finset.univ \ ({C, B, L, D, M, T} : Finset V)).card = 4 ∧
      (∀ v ∈ Finset.univ \ ({C, B, L, D, M, T} : Finset V),
        weight v = 2 ∧ ∀ w, ¬ G.Adj v w) ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 5 ∧
      -1 + dotProduct (fun i => weight i - 2) coeff = 2 / 15 ∧
      dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) = 13 / 10 ∧
      (graphWeightMatrix G weight).det = 2400 ∧
      (borderedGram (graphWeightMatrix G weight)
        (threeMarkedSource C B D) (-1)).det = 720 := by
  have hCB : ¬ G.Reachable C B := by simpa using hseparate 0 1 (by decide)
  have hCD : ¬ G.Reachable C D := by simpa using hseparate 0 2 (by decide)
  have hBD : ¬ G.Reachable B D := by simpa using hseparate 1 2 (by decide)
  have hTB : ¬ G.Reachable T B := by simpa using hseparate 3 1 (by decide)
  have hTD : ¬ G.Reachable T D := by simpa using hseparate 3 2 (by decide)
  have hBD' : B ≠ D := by intro h; subst D; exact hBD (SimpleGraph.Reachable.refl B)
  have hTB' : T ≠ B := by intro h; subst T; exact hTB (SimpleGraph.Reachable.refl B)
  have hTD' : T ≠ D := by intro h; subst T; exact hTD (SimpleGraph.Reachable.refl D)
  have hidentity := beta_three_one_extra_source_scalar_identity G weight coeff C B D T
    hA hrow hB hD hT hTB' hTD' hCB hCD hBD hcanonical hBsingle hDsingle hTsingle
    hother hprojection
  obtain ⟨hCiso, hTiso, L, M, hL, hM, hBL, hDM, hnB, hnL, hnD, hnM, _, _⟩ :=
    beta_three_one_extra_forest_fixed_components G weight C B D T hA hG hcanonical
      hB hD hT hBsingle hDsingle hTsingle hseparate hedges hidentity
  have hC := hcanonical C (SimpleGraph.Reachable.refl C)
  obtain ⟨heq, hremainingcard, hremaining⟩ :=
    familyC_remaining_vertices G weight C B L D M T hcard hC hL hM hB hD hT
      hCiso hTiso hBL hDM hBD hedges hother
  have hLM : L ≠ M := by
    intro h
    subst M
    exact hBD (hBL.reachable.trans hDM.reachable.symm)
  have hg := familyC_marked_green_energy G weight C B L D M hA hC hB hL hD hM
    hBD' hCiso hBL hDM hnB hnL hnD hnM
  obtain ⟨hdet, hborder⟩ := familyC_bordered_det G weight C B L D M T hcard
    hB hL hD hM hT hBD' hLM hTB' hTD' hBL hDM heq hother hA hg
  obtain ⟨_, _, _, _, _, _, hell, hvol⟩ :=
    familyC_source_row_values G weight coeff C B L D M T hrow hC hB hL hD hM hT
      hBD' hTB' hTD' hCiso hTiso hnB hnL hnD hnM hother
  exact ⟨L, M, hL, hM, hCiso, hTiso, hBL, hDM, hnB, hnL, hnD, hnM,
    heq, hremainingcard, hremaining, hell, hvol, hg, hdet, hborder⟩

end KltDP.LinearAlgebra
