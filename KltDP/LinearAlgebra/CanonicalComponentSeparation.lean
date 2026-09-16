import KltDP.LinearAlgebra.HeavyVertexSeparation
import Mathlib.Tactic

/-!
# Canonical-path bounds for the distinguished component

This module continues `lem:ten-forests` after higher-weight separation.
Actual shortest paths in a component with at most one higher-weight vertex
have weight two away from that vertex. The full row equations therefore
supply the canonical path endpoint bounds. The source charge budgets exclude
the specified connections of the distinguished vertex C.

The beta-four one-extra case requiring the leaf-row concavity argument and
the beta-three one-extra small-graph cases remain separate obligations.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [StarRing 𝕜] [TrivialStar 𝕜]

/-- The actual canonical path bounds follow from full graph positivity and
row equations. The principal matrix and its comparison are derived here. -/
theorem graph_shortest_canonical_lower_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight coeff : V → 𝕜)
    (hA : (graphWeightMatrix G weight).PosDef)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) {root target : V} (p : G.Walk root target)
    (hp : p.length = G.dist root target) (β : 𝕜) (hβ : 3 ≤ β)
    (hfirst : weight root = β)
    (hrest : ∀ i : ℕ, 0 < i → i ≤ p.length → weight (p.getVert i) = 2) :
    canonicalEndFirst β (p.length : 𝕜) ≤ coeff root ∧
      canonicalEndLast β (p.length : 𝕜) ≤ coeff target := by
  let e := walkVertexMap p
  have he : Function.Injective e := walkVertexMap_injective (p.isPath_of_length_eq_dist hp)
  have hmatrix : (graphWeightMatrix G weight).submatrix e e =
      canonicalEndPath p.length β :=
    shortest_path_matrix_canonicalEnd G weight p hp β hfirst hrest
  have hprincipal := posDef_principal_submatrix hA e he
  rw [hmatrix] at hprincipal
  have hsource : (fun i => weight (e i) - 2) = canonicalEndSource p.length β := by
    have hdiag := congrArg (fun M : Matrix (Fin (p.length + 1)) (Fin (p.length + 1)) 𝕜 =>
      fun i => M i i - 2) hmatrix
    simpa only [Matrix.submatrix_apply, graphWeightMatrix_diagonal,
      canonicalEndPath_diagonal_source] using hdiag
  have hrows := source_le_principal_mulVec (graphWeightMatrix G weight) e he coeff
    (fun i => weight i - 2) hcoeff (graphWeightMatrix_offDiagonal G weight) hrow
  rw [hmatrix] at hrows
  have hrows' : ∀ i, canonicalEndSource p.length β i ≤
      (canonicalEndPath p.length β *ᵥ (coeff ∘ e)) i := by
    intro i
    rw [← hsource]
    exact hrows i
  have hE := canonicalEndDenominator_pos hβ (Nat.cast_nonneg p.length : (0 : 𝕜) ≤ p.length)
  have hb := canonicalEndPath_endpoint_lower_bounds p.length β
    (ne_of_gt hE) hprincipal (coeff ∘ e) hrows'
  simpa only [Function.comp_apply, e, walkVertexMap_zero, walkVertexMap_last] using hb

omit [Fintype V] [DecidableEq V] in
/-- Higher-weight uniqueness in the actual connected component forces all
noninitial vertices of a shortest path from its higher-weight vertex to
have weight two. This is a proved path pattern, not an assumed list. -/
theorem shortest_path_weights_two_of_heavy_unique (G : SimpleGraph V)
    (weight : V → ℕ) (hweight : ∀ i, 2 ≤ weight i)
    (hunique : ∀ x y, 2 < weight x → 2 < weight y → G.Reachable x y → x = y)
    {root target : V} (p : G.Walk root target)
    (hp : p.length = G.dist root target) (hroot : 2 < weight root)
    (i : ℕ) (hi : 0 < i) (hilast : i ≤ p.length) : weight (p.getVert i) = 2 := by
  apply Nat.le_antisymm ?_ (hweight _)
  by_contra! hhigher
  have heq := hunique root (p.getVert i) hroot hhigher (p.take i).reachable
  have hzero := ((p.isPath_of_length_eq_dist hp).getVert_eq_start_iff hilast).mp heq.symm
  omega

/-- Reachability from the unique higher-weight vertex gives the actual
canonical endpoint lower bounds, evaluated at the actual graph distance. -/
theorem graph_reachable_canonical_lower_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → 𝕜) (hweight : ∀ i, 2 ≤ weight i)
    (hunique : ∀ x y, 2 < weight x → 2 < weight y → G.Reachable x y → x = y)
    (hA : (graphWeightMatrix G (fun i => (weight i : 𝕜))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) {root target : V}
    (hroot : 2 < weight root) (hreach : G.Reachable root target) :
    canonicalEndFirst (weight root : 𝕜) (G.dist root target : 𝕜) ≤ coeff root ∧
      canonicalEndLast (weight root : 𝕜) (G.dist root target : 𝕜) ≤ coeff target := by
  obtain ⟨p, _, hp⟩ := hreach.exists_path_of_dist
  have hb := graph_shortest_canonical_lower_bounds G (fun i => (weight i : 𝕜)) coeff
    hA hrow hcoeff p hp (weight root : 𝕜)
    (by exact_mod_cast (show 3 ≤ weight root from hroot)) rfl
    (fun i hi hj => by
      change (weight (p.getVert i) : 𝕜) = 2
      exact_mod_cast shortest_path_weights_two_of_heavy_unique G weight hweight hunique p hp hroot i hi hj)
  simpa only [hp] using hb

omit [DecidableEq V] in
/-- The standard trail edge bound applies to the actual metric shortest
path. No acyclicity hypothesis or auxiliary list of edges is needed. -/
theorem reachable_dist_le_edgeFinset_card (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (hreach : G.Reachable u v) : G.dist u v ≤ G.edgeFinset.card := by
  obtain ⟨p, hp, hlength⟩ := hreach.exists_path_of_dist
  rw [← hlength]
  exact hp.isTrail.length_le_card_edgeFinset

omit [Fintype V] [DecidableEq V] in
/-- Absence of a reachable higher-weight vertex makes the whole actual
component weight two, since every weight is assumed at least two. -/
theorem reachable_weights_two_of_no_heavy (G : SimpleGraph V) (weight : V → ℕ)
    (hweight : ∀ i, 2 ≤ weight i) (C : V)
    (hno : ∀ t, 2 < weight t → ¬ G.Reachable C t) :
    ∀ t, G.Reachable C t → weight t = 2 := by
  intro t ht
  apply Nat.le_antisymm ?_ (hweight t)
  by_contra! hhigher
  exact hno t hhigher ht

omit [StarRing 𝕜] [TrivialStar 𝕜] in
/-- The source's full dot-product budget gives its exact charge inequality
with the C coefficient retained. This term is needed for canonical paths. -/
theorem graph_full_charge_of_source_budget (weight coeff : V → 𝕜)
    (C B₁ B₂ : V) (β : 𝕜) (hB : B₁ ≠ B₂)
    (hB₁ : weight B₁ = 3) (hB₂ : weight B₂ = β)
    (hv : 2 - β + dotProduct (fun i => weight i - 2) coeff ≤
      1 - coeff C - coeff B₁ - coeff B₂) :
    1 - β + coeff C + 2 * coeff B₁ + (β - 1) * coeff B₂ +
      noncoreSourceMass weight coeff B₁ B₂ ≤ 0 := by
  have hs := canonical_source_sum_split weight coeff B₁ B₂ hB
  rw [hB₁, hB₂] at hs
  norm_num at hs
  nlinarith only [hs, hv]

/-- Three structural exclusions for the actual component of C, directly
from the source graph and matrix hypotheses:

* for beta four or five it cannot meet either core component;
* for beta five it contains no higher-weight vertex;
* with two distinct extra weight-three vertices it contains no higher-weight
  vertex, for all three allowed beta values.

The edge bound is used only for the beta-five extra-vertex case. This does
not assert the remaining beta-three or beta-four one-extra classifications. -/
theorem canonical_component_exclusions_of_source_budgets
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → 𝕜) (C B₁ B₂ : V) (β : ℕ)
    (hβ : β = 3 ∨ β = 4 ∨ β = 5)
    (hweight : ∀ i, 2 ≤ weight i) (hB₁ : weight B₁ = 3) (hB₂ : weight B₂ = β)
    (hother : ∀ i, i ≠ B₁ → i ≠ B₂ → weight i = 2 ∨ weight i = 3)
    (hseparate : ¬ G.Reachable B₁ B₂) (hedges : G.edgeFinset.card ≤ β - 1)
    (hA : (graphWeightMatrix G (fun i => (weight i : 𝕜))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hell : 0 < 1 - coeff C - coeff B₁ - coeff B₂)
    (hv : 2 - (β : 𝕜) + dotProduct (fun i => (weight i : 𝕜) - 2) coeff ≤
      1 - coeff C - coeff B₁ - coeff B₂) :
    (4 ≤ β → ¬ G.Reachable C B₁ ∧ ¬ G.Reachable C B₂) ∧
      (β = 5 → ∀ t, G.Reachable C t → weight t = 2) ∧
      ((∃ t u, t ≠ u ∧ t ≠ B₁ ∧ t ≠ B₂ ∧ u ≠ B₁ ∧ u ≠ B₂ ∧
        weight t = 3 ∧ weight u = 3) →
        ∀ t, G.Reachable C t → weight t = 2) := by
  have hB : B₁ ≠ B₂ := by
    intro h
    subst B₂
    exact hseparate (SimpleGraph.Reachable.refl B₁)
  have hβnat : 3 ≤ β := by rcases hβ with rfl | rfl | rfl <;> omega
  have hβfield : (3 : 𝕜) ≤ β := by exact_mod_cast hβnat
  have hweight' : ∀ i, (2 : 𝕜) ≤ weight i := fun i => by exact_mod_cast hweight i
  obtain ⟨hcore, hcharge⟩ := graph_charge_budgets_of_source_budgets
    (fun i => (weight i : 𝕜)) coeff C B₁ B₂ (β : 𝕜) hB
    (by change (weight B₁ : 𝕜) = 3; exact_mod_cast hB₁)
    (by change (weight B₂ : 𝕜) = (β : 𝕜); exact_mod_cast hB₂) (hcoeff C) hell hv
  have hfull := graph_full_charge_of_source_budget
    (fun i => (weight i : 𝕜)) coeff C B₁ B₂ (β : 𝕜) hB
    (by change (weight B₁ : 𝕜) = 3; exact_mod_cast hB₁)
    (by change (weight B₂ : 𝕜) = (β : 𝕜); exact_mod_cast hB₂) hv
  have hunique := heavy_vertices_eq_of_graph_charge G weight coeff B₁ B₂ β hβ hweight
    hB₁ hB₂ hother hseparate hA hrow hcoeff hcore hcharge
  have hcanon (root target : V) (hroot : 2 < weight root) (hr : G.Reachable root target) :
      canonicalEndFirst (weight root : 𝕜) (G.dist root target : 𝕜) ≤ coeff root ∧
        canonicalEndLast (weight root : 𝕜) (G.dist root target : 𝕜) ≤ coeff target :=
    graph_reachable_canonical_lower_bounds G weight coeff hweight hunique hA hrow hcoeff hroot hr
  have hthird (t : V) (ht : weight t = 3) : (1 : 𝕜) / 3 ≤ coeff t := by
    have h := graph_coefficient_lower_bound G (fun i => (weight i : 𝕜)) coeff hrow hcoeff t
      (by change (0 : 𝕜) < (weight t : 𝕜); rw [ht]; norm_num)
    norm_num [ht] at h
    exact h
  have ha := hthird B₁ hB₁
  have hb : ((β : 𝕜) - 2) / (β : 𝕜) ≤ coeff B₂ := by
    have h := graph_coefficient_lower_bound G (fun i => (weight i : 𝕜)) coeff hrow hcoeff B₂
      (by change (0 : 𝕜) < (weight B₂ : 𝕜); rw [hB₂]; linarith only [hβfield])
    simpa only [hB₂] using h
  have hthree (t : V) (ht₁ : t ≠ B₁) (ht₂ : t ≠ B₂) (ht : 2 < weight t) : weight t = 3 := by
    rcases hother t ht₁ ht₂ with h | h
    · omega
    · exact h
  have hsumThree (t : V) (ht : weight t = 3) (hr : G.Reachable C t) :
      (1 : 𝕜) / 2 < coeff C + coeff t := by
    have hpath := hcanon t C (by rw [ht]; omega : 2 < weight t) hr.symm
    rw [ht] at hpath
    norm_num only [Nat.cast_ofNat] at hpath
    have hsum := canonicalEnd_three_sum_gt_half (Nat.cast_nonneg (G.dist t C) : (0 : 𝕜) ≤ G.dist t C)
    linarith [hpath.1, hpath.2]
  have hcoreExclusion : 4 ≤ β → ¬ G.Reachable C B₁ ∧ ¬ G.Reachable C B₂ := by
    intro hfour
    have hfour' : (4 : 𝕜) ≤ β := by exact_mod_cast hfour
    have hbhalf : (1 : 𝕜) / 2 ≤ coeff B₂ := by
      apply le_trans _ hb
      apply (le_div_iff₀ (by linarith only [hfour'] : (0 : 𝕜) < β)).mpr
      linarith
    constructor
    · intro hr
      have hsum := hsumThree B₁ hB₁ hr
      linarith
    · intro hr
      have hpath := hcanon B₂ C (by rw [hB₂]; omega : 2 < weight B₂) hr.symm
      rw [hB₂] at hpath
      have hsum := canonicalEnd_sum_gt_two_thirds hfour'
        (Nat.cast_nonneg (G.dist B₂ C) : (0 : 𝕜) ≤ G.dist B₂ C)
      linarith [hpath.1, hpath.2]
  have hfive : β = 5 → ∀ t, G.Reachable C t → weight t = 2 := by
    intro h5
    apply reachable_weights_two_of_no_heavy G weight hweight C
    intro t ht hr
    have hcore5 := hcoreExclusion (by omega)
    have ht₁ : t ≠ B₁ := by intro h; subst t; exact hcore5.1 hr
    have ht₂ : t ≠ B₂ := by intro h; subst t; exact hcore5.2 hr
    have ht3 := hthree t ht₁ ht₂ ht
    have hpath := hcanon t C ht hr.symm
    rw [ht3] at hpath
    norm_num only [Nat.cast_ofNat] at hpath
    have hdist : G.dist t C ≤ 4 := by
      have h := reachable_dist_le_edgeFinset_card G hr.symm
      omega
    have hlast := canonicalEnd_three_last_ge_eleventh
      (Nat.cast_nonneg (G.dist t C) : (0 : 𝕜) ≤ G.dist t C)
      (by exact_mod_cast hdist : (G.dist t C : 𝕜) ≤ 4)
    rw [h5] at hb
    norm_num at hb
    linarith [hpath.2]
  refine ⟨hcoreExclusion, hfive, ?_⟩
  rintro ⟨s, u, hsu, hs₁, hs₂, hu₁, hu₂, hs3, hu3⟩
  by_cases h5 : β = 5
  · exact hfive h5
  have hβ34 : β = 3 ∨ β = 4 := by rcases hβ with h | h | h <;> tauto
  have hsThird := hthird s hs3
  have huThird := hthird u hu3
  have hmass := pair_le_noncoreSourceMass (fun i => (weight i : 𝕜)) coeff B₁ B₂ s u
    hweight' hcoeff hs₁ hs₂ hu₁ hu₂ hsu
    (by change (weight s : 𝕜) = 3; exact_mod_cast hs3)
    (by change (weight u : 𝕜) = 3; exact_mod_cast hu3)
  have hcoreBoth : ¬ G.Reachable C B₁ ∧ ¬ G.Reachable C B₂ := by
    rcases hβ34 with h3 | h4
    · have hb3 := hb
      rw [h3] at hb3
      norm_num at hb3
      have hfull3 := hfull
      rw [h3] at hfull3
      norm_num at hfull3
      constructor
      · intro hr
        have hsum := hsumThree B₁ hB₁ hr
        linarith
      · intro hr
        have hB₂3 : weight B₂ = 3 := hB₂.trans h3
        have hsum := hsumThree B₂ hB₂3 hr
        linarith
    · exact hcoreExclusion (by omega)
  apply reachable_weights_two_of_no_heavy G weight hweight C
  intro t ht hr
  have ht₁ : t ≠ B₁ := by intro h; subst t; exact hcoreBoth.1 hr
  have ht₂ : t ≠ B₂ := by intro h; subst t; exact hcoreBoth.2 hr
  have ht3 := hthree t ht₁ ht₂ ht
  have hsum := hsumThree t ht3 hr
  obtain ⟨z, hz₁, hz₂, hz3, htz⟩ :
      ∃ z, z ≠ B₁ ∧ z ≠ B₂ ∧ weight z = 3 ∧ t ≠ z := by
    by_cases hts : t = s
    · exact ⟨u, hu₁, hu₂, hu3, by simpa only [hts] using hsu⟩
    · exact ⟨s, hs₁, hs₂, hs3, hts⟩
  have hzThird := hthird z hz3
  have hmass' := pair_le_noncoreSourceMass (fun i => (weight i : 𝕜)) coeff B₁ B₂ t z
    hweight' hcoeff ht₁ ht₂ hz₁ hz₂ htz
    (by change (weight t : 𝕜) = 3; exact_mod_cast ht3)
    (by change (weight z : 𝕜) = 3; exact_mod_cast hz3)
  rcases hβ34 with h3 | h4
  · rw [h3] at hb hfull
    norm_num at hb hfull
    linarith
  · rw [h4] at hb hfull
    norm_num at hb hfull
    linarith

end KltDP.LinearAlgebra
