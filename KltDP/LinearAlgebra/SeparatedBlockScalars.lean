import KltDP.LinearAlgebra.GraphGreenComponents
import Mathlib.Tactic

/-!
# Scalar identities from the actual separated graph components

This is the graph-to-scalar step before families C, D and E in
`lem:ten-forests`. Canonical components and the at-most-one-source property
are expressed on actual reachable vertices. The three scalar identities
and the cap are conclusions from the actual row equation and inverse.

The final rigidity theorem addresses beta three with two extras: the cap
forces both core Green excesses to vanish and the extra sum to equal 2/3.
The graph conclusions follow from the proved diagonal equality
criterion, rather than from membership in a candidate table.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Exact source mass at a finite set of actual extra weight-three vertices.
All other noncore source terms vanish because their actual weight is two. -/
theorem canonical_source_sum_extras
    (weight coeff : V → 𝕜) (B D : V) (extras : Finset V) (β : 𝕜)
    (hBD : B ≠ D) (hB : weight B = 3) (hD : weight D = β)
    (hextras : ∀ t ∈ extras, t ≠ B ∧ t ≠ D ∧ weight t = 3)
    (hother : ∀ i, i ≠ B → i ≠ D → i ∉ extras → weight i = 2) :
    dotProduct (fun i => weight i - 2) coeff =
      coeff B + (β - 2) * coeff D + ∑ t ∈ extras, coeff t := by
  rw [canonical_source_sum_split weight coeff B D hBD, hB, hD]
  have hsubset : extras ⊆ (Finset.univ.erase B).erase D := by
    intro t ht
    obtain ⟨htB, htD, _⟩ := hextras t ht
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨htD, htB⟩
  have hmass : noncoreSourceMass weight coeff B D = ∑ t ∈ extras, coeff t := by
    unfold noncoreSourceMass
    calc
      _ = ∑ t ∈ extras, (weight t - 2) * coeff t := by
        symm
        apply Finset.sum_subset hsubset
        intro t ht hnot
        have htD := (Finset.mem_erase.mp ht).1
        have htB := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
        rw [hother t htB htD hnot, sub_self, zero_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [(hextras t ht).2.2]
        ring
  rw [hmass]
  ring

/-- All three manuscript block identities are derived simultaneously from
the full row equation, actual component separation and actual vertex weights.
The extra set may have any finite cardinality at this algebraic stage. -/
theorem separated_graph_block_identities
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight coeff : V → 𝕜)
    (C B D : V) (extras : Finset V) (β : 𝕜)
    (hA : IsUnit (graphWeightMatrix G weight))
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hB : weight B = 3) (hD : weight D = β) (hβ : β ≠ 0)
    (hCB : ¬ G.Reachable C B) (hCD : ¬ G.Reachable C D)
    (hBD : ¬ G.Reachable B D)
    (hcanonical : ∀ i, G.Reachable C i → weight i = 2)
    (hBsingle : ∀ i, G.Reachable B i → i ≠ B → weight i = 2)
    (hDsingle : ∀ i, G.Reachable D i → i ≠ D → weight i = 2)
    (hextras : ∀ t ∈ extras, t ≠ B ∧ t ≠ D ∧ weight t = 3)
    (hsingle : ∀ t ∈ extras, ∀ i, G.Reachable t i → i ≠ t → weight i = 2)
    (hother : ∀ i, i ≠ B → i ≠ D → i ∉ extras → weight i = 2) :
    let A := graphWeightMatrix G weight
    let x := A⁻¹ B B - 1 / 3
    let y := A⁻¹ D D - 1 / β
    let z := A⁻¹ C C
    let tau := ∑ t ∈ extras, A⁻¹ t t
    (1 - dotProduct (threeMarkedSource C B D) coeff =
      2 / β - 1 / 3 - x - (β - 2) * y) ∧
    (2 - β + dotProduct (fun i => weight i - 2) coeff =
      -5 / 3 + 4 / β + x + (β - 2)^2 * y + tau) ∧
    (dotProduct (threeMarkedSource C B D) (A⁻¹ *ᵥ threeMarkedSource C B D) =
      z + 1 / 3 + 1 / β + x + y) := by
  dsimp only
  have hne : B ≠ D := by
    intro h
    subst D
    exact hBD (SimpleGraph.Reachable.refl B)
  have hc := graph_canonical_component_coefficient_zero G weight coeff hA hrow C hcanonical
  have hb := graph_single_source_coefficient G weight coeff hA hrow B hBsingle
  have hd := graph_single_source_coefficient G weight coeff hA hrow D hDsingle
  rw [hB] at hb
  rw [hD] at hd
  have ht : ∑ t ∈ extras, coeff t =
      ∑ t ∈ extras, (graphWeightMatrix G weight)⁻¹ t t := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [graph_single_source_coefficient G weight coeff hA hrow t (hsingle t ht),
      (hextras t ht).2.2]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [threeMarkedSource_dotProduct, hc, hb, hd]
    field_simp [hβ]; ring
  · rw [canonical_source_sum_extras weight coeff B D extras β hne hB hD hextras hother,
      hb, hd, ht]
    field_simp [hβ]; ring
  · rw [graph_separated_marked_energy G weight hA C B D hCB hCD hBD]
    ring

/-- The source inequality v ≤ ell is exactly the stated block cap once
the two identities have been proved. This lemma performs only the final
ordered-field rearrangement. -/
theorem separated_block_cap_iff
    (β x y tau : 𝕜) :
    -5 / 3 + 4 / β + x + (β - 2)^2 * y + tau ≤
        2 / β - 1 / 3 - x - (β - 2) * y ↔
      tau + 2 * x + (β - 2) * (β - 1) * y ≤ 4 / 3 - 2 / β := by
  have hdiff :
      (-5 / 3 + 4 / β + x + (β - 2)^2 * y + tau) -
          (2 / β - 1 / 3 - x - (β - 2) * y) =
        (tau + 2 * x + (β - 2) * (β - 1) * y) - (4 / 3 - 2 / β) := by
    ring
  constructor
  · intro h
    apply sub_nonpos.mp
    rw [← hdiff]
    exact sub_nonpos.mpr h
  · intro h
    apply sub_nonpos.mp
    rw [hdiff]
    exact sub_nonpos.mpr h

/-- The beta-three, two-extra cap forces the lower bounds to be equalities.
This is a scalar consequence, with every sign premise stated explicitly. -/
theorem beta_three_two_extra_cap_rigidity
    (x y tau : 𝕜) (hx : 0 ≤ x) (hy : 0 ≤ y) (htau : 2 / 3 ≤ tau)
    (hcap : tau + 2 * x + 2 * y ≤ 2 / 3) :
    x = 0 ∧ y = 0 ∧ tau = 2 / 3 := by
  constructor
  · linarith
  constructor <;> linarith

/-- In the beta-three, one-extra case the actual block identities have
ell = 1/3-s, v = s+u and g = z+2/3+s. Substitution into the projection
identity is equivalent to the manuscript's scalar equation. -/
theorem beta_three_one_extra_projection_iff (s u z : 𝕜) :
    (s + u) * (z + 2 / 3 + s - 1) = (1 / 3 - s)^2 ↔
      s * (z + 1 / 3) + u * (z - 1 / 3 + s) = 1 / 9 := by
  constructor <;> intro h <;> nlinarith only [h]

section OrderedGreen

variable [StarRing 𝕜] [TrivialStar 𝕜]

/-- Applying cap rigidity to actual inverse entries proves that all four
weight-three vertices in the beta-three, two-extra case are isolated.
The cap is the previous source identity's actual Green specialization. -/
theorem beta_three_two_extra_isolated_of_green_cap
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜)
    (hA : (graphWeightMatrix G weight).PosDef) (B D T U : V)
    (hB : weight B = 3) (hD : weight D = 3)
    (hT : weight T = 3) (hU : weight U = 3)
    (hcap :
      (graphWeightMatrix G weight)⁻¹ T T + (graphWeightMatrix G weight)⁻¹ U U +
        2 * ((graphWeightMatrix G weight)⁻¹ B B - 1 / 3) +
        2 * ((graphWeightMatrix G weight)⁻¹ D D - 1 / 3) ≤ 2 / 3) :
    (∀ v, ¬ G.Adj B v) ∧ (∀ v, ¬ G.Adj D v) ∧
      (∀ v, ¬ G.Adj T v) ∧ (∀ v, ¬ G.Adj U v) := by
  have hb := graph_inverse_diagonal_lower_bound G weight hA B (by rw [hB]; norm_num)
  have hd := graph_inverse_diagonal_lower_bound G weight hA D (by rw [hD]; norm_num)
  have ht := graph_inverse_diagonal_lower_bound G weight hA T (by rw [hT]; norm_num)
  have hu := graph_inverse_diagonal_lower_bound G weight hA U (by rw [hU]; norm_num)
  rw [hB] at hb
  rw [hD] at hd
  rw [hT] at ht
  rw [hU] at hu
  obtain ⟨hx, hy, htau⟩ := beta_three_two_extra_cap_rigidity
    ((graphWeightMatrix G weight)⁻¹ B B - 1 / 3)
    ((graphWeightMatrix G weight)⁻¹ D D - 1 / 3)
    ((graphWeightMatrix G weight)⁻¹ T T + (graphWeightMatrix G weight)⁻¹ U U)
    (by linarith) (by linarith) (by linarith) hcap
  have hb' : (graphWeightMatrix G weight)⁻¹ B B = 1 / weight B := by rw [hB]; linarith
  have hd' : (graphWeightMatrix G weight)⁻¹ D D = 1 / weight D := by rw [hD]; linarith
  have ht' : (graphWeightMatrix G weight)⁻¹ T T = 1 / weight T := by rw [hT]; linarith
  have hu' : (graphWeightMatrix G weight)⁻¹ U U = 1 / weight U := by rw [hU]; linarith
  exact ⟨(graph_inverse_diagonal_eq_iff_isolated G weight hA B
      (by rw [hB]; norm_num)).mp hb',
    (graph_inverse_diagonal_eq_iff_isolated G weight hA D
      (by rw [hD]; norm_num)).mp hd',
    (graph_inverse_diagonal_eq_iff_isolated G weight hA T
      (by rw [hT]; norm_num)).mp ht',
    (graph_inverse_diagonal_eq_iff_isolated G weight hA U
      (by rw [hU]; norm_num)).mp hu'⟩

/-- Source-facing beginning of family D. With a canonical C-component and
one source in each higher-weight component, the original v ≤ ell and
projection identity force four actual isolated vertices, ell = v = 1/3,
and the actual C Green entry = 2/3. No scalar cap or isolation is assumed. -/
theorem beta_three_two_extra_source_rigidity
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight coeff : V → 𝕜)
    (C B D T U : V)
    (hA : (graphWeightMatrix G weight).PosDef)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hB : weight B = 3) (hD : weight D = 3)
    (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hCB : ¬ G.Reachable C B) (hCD : ¬ G.Reachable C D)
    (hBD : ¬ G.Reachable B D)
    (hcanonical : ∀ i, G.Reachable C i → weight i = 2)
    (hBsingle : ∀ i, G.Reachable B i → i ≠ B → weight i = 2)
    (hDsingle : ∀ i, G.Reachable D i → i ≠ D → weight i = 2)
    (hTsingle : ∀ i, G.Reachable T i → i ≠ T → weight i = 2)
    (hUsingle : ∀ i, G.Reachable U i → i ≠ U → weight i = 2)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → i ≠ U → weight i = 2)
    (hbudget : -1 + dotProduct (fun i => weight i - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (-1 + dotProduct (fun i => weight i - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) - 1) =
      (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    (∀ v, ¬ G.Adj B v) ∧ (∀ v, ¬ G.Adj D v) ∧
      (∀ v, ¬ G.Adj T v) ∧ (∀ v, ¬ G.Adj U v) ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 3 ∧
      -1 + dotProduct (fun i => weight i - 2) coeff = 1 / 3 ∧
      (graphWeightMatrix G weight)⁻¹ C C = 2 / 3 := by
  have hextras : ∀ t ∈ ({T, U} : Finset V), t ≠ B ∧ t ≠ D ∧ weight t = 3 := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ⟨hTB, hTD, hT⟩
    · have htU := Finset.mem_singleton.mp ht
      subst t
      exact ⟨hUB, hUD, hU⟩
  have hsingle : ∀ t ∈ ({T, U} : Finset V),
      ∀ i, G.Reachable t i → i ≠ t → weight i = 2 := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hTsingle
    · have htU := Finset.mem_singleton.mp ht
      subst t
      exact hUsingle
  have hother' : ∀ i, i ≠ B → i ≠ D → i ∉ ({T, U} : Finset V) → weight i = 2 := by
    intro i hiB hiD hi
    have hiT : i ≠ T := by intro h; subst i; simp at hi
    have hiU : i ≠ U := by intro h; subst i; simp at hi
    exact hother i hiB hiD hiT hiU
  obtain ⟨hl, hv, hg⟩ := separated_graph_block_identities G weight coeff C B D {T, U}
    (3 : 𝕜) (isUnit_of_posDef hA) hrow hB hD (by norm_num) hCB hCD hBD
    hcanonical hBsingle hDsingle hextras hsingle hother'
  simp only [Finset.sum_insert (by simp [hTU] : T ∉ ({U} : Finset V)),
    Finset.sum_singleton] at hv
  norm_num at hl hv hg
  have hcap :
      (graphWeightMatrix G weight)⁻¹ T T + (graphWeightMatrix G weight)⁻¹ U U +
        2 * ((graphWeightMatrix G weight)⁻¹ B B - 1 / 3) +
        2 * ((graphWeightMatrix G weight)⁻¹ D D - 1 / 3) ≤ 2 / 3 := by
    linarith only [hbudget, hl, hv]
  obtain ⟨hBi, hDi, hTi, hUi⟩ :=
    beta_three_two_extra_isolated_of_green_cap G weight hA B D T U hB hD hT hU hcap
  have hb := (graph_inverse_diagonal_eq_iff_isolated G weight hA B
    (by rw [hB]; norm_num)).mpr hBi
  have hd := (graph_inverse_diagonal_eq_iff_isolated G weight hA D
    (by rw [hD]; norm_num)).mpr hDi
  have ht := (graph_inverse_diagonal_eq_iff_isolated G weight hA T
    (by rw [hT]; norm_num)).mpr hTi
  have hu := (graph_inverse_diagonal_eq_iff_isolated G weight hA U
    (by rw [hU]; norm_num)).mpr hUi
  rw [hB] at hb
  rw [hD] at hd
  rw [hT] at ht
  rw [hU] at hu
  have hell : 1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 3 := by
    linarith only [hl, hb, hd]
  have hvol : -1 + dotProduct (fun i => weight i - 2) coeff = 1 / 3 := by
    linarith only [hv, hb, hd, ht, hu]
  refine ⟨hBi, hDi, hTi, hUi, hell, hvol, ?_⟩
  rw [hell, hvol] at hprojection
  nlinarith only [hprojection, hg, hb, hd]

end OrderedGreen

end KltDP.LinearAlgebra
