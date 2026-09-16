import KltDP.LinearAlgebra.WeightedPathTransport
import KltDP.LinearAlgebra.PrincipalSubmatrixComparison
import KltDP.LinearAlgebra.Discrepancy
import Mathlib.Tactic

/-!
# Separation of higher-weight vertices by the canonical charge budget

This is the first component-separation step of manuscript `lem:ten-forests`.
The matrix is the actual diagonal-minus-adjacency matrix of a finite graph.
Its full canonical row equation gives lower bounds along actual shortest
paths. Those bounds contradict the stated charge inequalities whenever a
component has two vertices of weight greater than two.

No forest, edge-count, valency, or geometric realization is assumed. Those
hypotheses belong to later steps of the source classification. The two core
vertices are assumed to lie in distinct components, as in the source;
separation from every other higher-weight vertex is proved here.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [Fintype V] in
/-- The actual off-diagonal graph entries have the sign required by the
Stieltjes comparison theorem. -/
theorem graphWeightMatrix_offDiagonal (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → 𝕜) :
    ∀ i j, i ≠ j → graphWeightMatrix G weight i j ≤ 0 := by
  intro i j hij
  rw [graphWeightMatrix_apply, if_neg hij]
  split_ifs <;> norm_num

/-- Elementary discrepancy lower bound for an actual weighted-graph row
system. The diagonal identity is proved by `graphWeightMatrix_diagonal`. -/
theorem graph_coefficient_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight coeff : V → 𝕜)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) (i : V) (hi : 0 < weight i) :
    (weight i - 2) / weight i ≤ coeff i := by
  have hrow' : graphWeightMatrix G weight *ᵥ coeff =
      fun j => graphWeightMatrix G weight j j - 2 := by
    simpa only [graphWeightMatrix_diagonal] using hrow
  have h := elementary_discrepancy_bound hrow'
    (graphWeightMatrix_offDiagonal G weight) hcoeff i
    (by simpa only [graphWeightMatrix_diagonal] using hi)
  simpa only [graphWeightMatrix_diagonal] using h

/-- Actual canonical-source mass away from the two distinguished core
vertices. Zero-weight sources contribute zero without selecting a list of
higher-weight vertices in advance. -/
def noncoreSourceMass (weight coeff : V → 𝕜) (B₁ B₂ : V) : 𝕜 :=
  ∑ i ∈ (Finset.univ.erase B₁).erase B₂, (weight i - 2) * coeff i

/-- Splitting the actual finite source sum at two distinct core coordinates. -/
theorem canonical_source_sum_split (weight coeff : V → 𝕜) (B₁ B₂ : V)
    (hne : B₁ ≠ B₂) :
    dotProduct (fun i => weight i - 2) coeff =
      (weight B₁ - 2) * coeff B₁ + (weight B₂ - 2) * coeff B₂ +
        noncoreSourceMass weight coeff B₁ B₂ := by
  let f : V → 𝕜 := fun i => (weight i - 2) * coeff i
  have hfirst := Finset.sum_erase_add Finset.univ f (Finset.mem_univ B₁)
  have hlast := Finset.sum_erase_add (Finset.univ.erase B₁) f
    (by simp [Ne.symm hne] : B₂ ∈ Finset.univ.erase B₁)
  change ∑ i, f i = f B₁ + f B₂ + ∑ i ∈ (Finset.univ.erase B₁).erase B₂, f i
  linarith only [hfirst, hlast]

/-- One actual noncore weight-three vertex contributes its coefficient to
the source mass; all omitted terms have proved nonnegative sign. -/
theorem coefficient_le_noncoreSourceMass (weight coeff : V → 𝕜) (B₁ B₂ t : V)
    (hweight : ∀ i, 2 ≤ weight i) (hcoeff : ∀ i, 0 ≤ coeff i)
    (ht₁ : t ≠ B₁) (ht₂ : t ≠ B₂) (ht : weight t = 3) :
    coeff t ≤ noncoreSourceMass weight coeff B₁ B₂ := by
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ.erase B₁).erase B₂) =>
      mul_nonneg (sub_nonneg.mpr (hweight i)) (hcoeff i))
    (by simp [ht₁, ht₂] : t ∈ (Finset.univ.erase B₁).erase B₂)
  simpa only [ht, show (3 : 𝕜) - 2 = 1 by norm_num, one_mul] using h

/-- Two distinct actual noncore weight-three vertices contribute the sum
of their coefficients to the source mass. -/
theorem pair_le_noncoreSourceMass (weight coeff : V → 𝕜) (B₁ B₂ t u : V)
    (hweight : ∀ i, 2 ≤ weight i) (hcoeff : ∀ i, 0 ≤ coeff i)
    (ht₁ : t ≠ B₁) (ht₂ : t ≠ B₂) (hu₁ : u ≠ B₁) (hu₂ : u ≠ B₂)
    (htu : t ≠ u) (ht : weight t = 3) (hu : weight u = 3) :
    coeff t + coeff u ≤ noncoreSourceMass weight coeff B₁ B₂ := by
  have hsub : ({t, u} : Finset V) ⊆ (Finset.univ.erase B₁).erase B₂ := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp [ht₁, ht₂]
    · have hi' : i = u := Finset.mem_singleton.mp hi
      subst i
      simp [hu₁, hu₂]
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => mul_nonneg (sub_nonneg.mpr (hweight i)) (hcoeff i))
  have hsum : ∑ i ∈ ({t, u} : Finset V), (weight i - 2) * coeff i =
      coeff t + coeff u := by norm_num [htu, ht, hu]
  rw [hsum] at h
  exact h

section Matrix

variable [StarRing 𝕜] [TrivialStar 𝕜]

/-- Full graph equations imply the explicit two-end lower bounds on an
actual shortest path. Principal positivity, matrix identification, and the
restricted-row inequality are all derived rather than supplied as premises. -/
theorem graph_shortest_twoEnd_lower_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight coeff : V → 𝕜)
    (hA : (graphWeightMatrix G weight).PosDef)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) {root target : V} (p : G.Walk root target)
    (hp : p.length = G.dist root target) (hpos : 0 < p.length) (β : 𝕜)
    (hβ : 3 ≤ β) (hfirst : weight root = β) (hlast : weight target = 3)
    (hinterior : ∀ i : ℕ, 0 < i → i < p.length → weight (p.getVert i) = 2) :
    twoEndFirst β (p.length : 𝕜) ≤ coeff root ∧
      twoEndLast β (p.length : 𝕜) ≤ coeff target := by
  let e := walkVertexMap p
  have he : Function.Injective e := walkVertexMap_injective (p.isPath_of_length_eq_dist hp)
  have hmatrix : (graphWeightMatrix G weight).submatrix e e =
      weightedTwoEndPath p.length β :=
    shortest_path_matrix_twoEnd G weight p hp hpos β hfirst hlast hinterior
  have hprincipal := posDef_principal_submatrix hA e he
  rw [hmatrix] at hprincipal
  have hsource : (fun i => weight (e i) - 2) = twoEndSource p.length β := by
    have hdiag := congrArg (fun M : Matrix (Fin (p.length + 1)) (Fin (p.length + 1)) 𝕜 =>
      fun i => M i i - 2) hmatrix
    simpa only [Matrix.submatrix_apply, graphWeightMatrix_diagonal,
      weightedTwoEndPath_diagonal_source] using hdiag
  have hrows := source_le_principal_mulVec (graphWeightMatrix G weight) e he coeff
    (fun i => weight i - 2) hcoeff (graphWeightMatrix_offDiagonal G weight) hrow
  rw [hmatrix] at hrows
  have hrows' : ∀ i, twoEndSource p.length β i ≤
      (weightedTwoEndPath p.length β *ᵥ (coeff ∘ e)) i := by
    intro i
    rw [← hsource]
    exact hrows i
  have hd : (1 : 𝕜) ≤ p.length := by
    exact_mod_cast (show 1 ≤ p.length from hpos)
  have hb := weightedTwoEndPath_endpoint_lower_bounds p.length β
    (ne_of_gt (twoEndDenominator_pos hβ hd)) hprincipal (coeff ∘ e) hrows'
  simpa only [Function.comp_apply, e, walkVertexMap_zero, walkVertexMap_last] using hb

/-- Specializing the actual two-end comparison to weight three at both
ends gives one-half lower bounds, independently of the length. -/
theorem graph_shortest_three_three_lower_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight coeff : V → 𝕜)
    (hA : (graphWeightMatrix G weight).PosDef)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) {root target : V} (p : G.Walk root target)
    (hp : p.length = G.dist root target) (hpos : 0 < p.length)
    (hfirst : weight root = 3) (hlast : weight target = 3)
    (hinterior : ∀ i : ℕ, 0 < i → i < p.length → weight (p.getVert i) = 2) :
    1 / 2 ≤ coeff root ∧ 1 / 2 ≤ coeff target := by
  have h := graph_shortest_twoEnd_lower_bounds G weight coeff hA hrow hcoeff p hp hpos
    3 (by norm_num) hfirst hlast hinterior
  have hd : (1 : 𝕜) ≤ p.length := by
    exact_mod_cast (show 1 ≤ p.length from hpos)
  obtain ⟨hf, hl⟩ := twoEnd_three (p.length : 𝕜)
    (ne_of_gt (twoEndDenominator_pos (by norm_num : (3 : 𝕜) ≤ 3) hd))
  simpa only [hf, hl] using h

/-- The actual source charge separates every higher-weight vertex from every
other one in its connected component. The only component separation assumed
is that of the two distinguished core vertices, exactly as in the source.
The conclusion imposes no forest or edge-count hypothesis. -/
theorem heavy_vertices_eq_of_graph_charge (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → 𝕜) (B₁ B₂ : V) (β : ℕ)
    (hβ : β = 3 ∨ β = 4 ∨ β = 5)
    (hweight : ∀ i, 2 ≤ weight i) (hB₁ : weight B₁ = 3) (hB₂ : weight B₂ = β)
    (hother : ∀ i, i ≠ B₁ → i ≠ B₂ → weight i = 2 ∨ weight i = 3)
    (hseparate : ¬ G.Reachable B₁ B₂)
    (hA : (graphWeightMatrix G (fun i => (weight i : 𝕜))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) (hcore : coeff B₁ + coeff B₂ < 1)
    (hcharge : 1 - (β : 𝕜) + 2 * coeff B₁ + ((β : 𝕜) - 1) * coeff B₂ +
      noncoreSourceMass (fun i => (weight i : 𝕜)) coeff B₁ B₂ ≤ 0) :
    ∀ x y, 2 < weight x → 2 < weight y → G.Reachable x y → x = y := by
  have hβnat : 3 ≤ β := by rcases hβ with rfl | rfl | rfl <;> omega
  have hβfield : (3 : 𝕜) ≤ β := by exact_mod_cast hβnat
  have hweight' : ∀ i, (2 : 𝕜) ≤ weight i := fun i => by exact_mod_cast hweight i
  have ha : (1 : 𝕜) / 3 ≤ coeff B₁ := by
    have h := graph_coefficient_lower_bound G (fun i => (weight i : 𝕜)) coeff hrow hcoeff B₁
      (by change (0 : 𝕜) < (weight B₁ : 𝕜); rw [hB₁]; norm_num)
    norm_num [hB₁] at h
    exact h
  have hb : ((β : 𝕜) - 2) / (β : 𝕜) ≤ coeff B₂ := by
    have h := graph_coefficient_lower_bound G (fun i => (weight i : 𝕜)) coeff hrow hcoeff B₂
      (by change (0 : 𝕜) < (weight B₂ : 𝕜); rw [hB₂]; linarith only [hβfield])
    simpa only [hB₂] using h
  have hthree (t : V) (ht₁ : t ≠ B₁) (ht₂ : t ≠ B₂) (ht : 2 < weight t) :
      weight t = 3 := by
    rcases hother t ht₁ ht₂ with hw | hw
    · omega
    · exact hw
  have hchargeOne (t : V) (ht₁ : t ≠ B₁) (ht₂ : t ≠ B₂) (ht : weight t = 3) :
      1 - (β : 𝕜) + 2 * coeff B₁ + ((β : 𝕜) - 1) * coeff B₂ + coeff t ≤ 0 := by
    have hs := coefficient_le_noncoreSourceMass (fun i => (weight i : 𝕜)) coeff B₁ B₂ t
      hweight' hcoeff ht₁ ht₂ (by change (weight t : 𝕜) = 3; exact_mod_cast ht)
    linarith
  have hsep₁ : ∀ t, t ≠ B₁ → 2 < weight t → ¬ G.Reachable B₁ t := by
    intro t ht hwt hreach
    obtain ⟨z, hz₁, hzw, hzr, hzmin⟩ :=
      exists_nearest_higher_vertex G weight B₁ ⟨t, ht, hwt, hreach⟩
    have hz₂ : z ≠ B₂ := by intro h; subst z; exact hseparate hzr
    have hz3 := hthree z hz₁ hz₂ hzw
    obtain ⟨p, _, hp⟩ := hzr.exists_path_of_dist
    have hpos : 0 < p.length := by rw [hp]; exact hzr.pos_dist_of_ne (Ne.symm hz₁)
    have hinside := nearest_higher_path_internal_weight weight hweight p hp hzmin
    obtain ⟨hhalf, hzhalf⟩ := graph_shortest_three_three_lower_bounds G
      (fun i => (weight i : 𝕜)) coeff hA hrow hcoeff p hp hpos
      (by change (weight B₁ : 𝕜) = 3; exact_mod_cast hB₁) (by change (weight z : 𝕜) = 3; exact_mod_cast hz3)
      (fun i hi hj => by
        change (weight (p.getVert i) : 𝕜) = 2
        exact_mod_cast hinside i hi hj)
    have hβ3 : β = 3 := by
      rcases hβ with h3 | h4 | h5
      · exact h3
      · have hb4 := hb
        rw [h4] at hb4
        norm_num at hb4
        exfalso
        linarith only [hhalf, hcore, hb4]
      · have hb5 := hb
        rw [h5] at hb5
        norm_num at hb5
        exfalso
        linarith only [hhalf, hcore, hb5]
    have hbad := hchargeOne z hz₁ hz₂ hz3
    rw [hβ3] at hb hbad
    norm_num at hb hbad
    linarith
  have hsep₂ : ∀ t, t ≠ B₂ → 2 < weight t → ¬ G.Reachable B₂ t := by
    intro t ht hwt hreach
    obtain ⟨z, hz₂, hzw, hzr, hzmin⟩ :=
      exists_nearest_higher_vertex G weight B₂ ⟨t, ht, hwt, hreach⟩
    have hz₁ : z ≠ B₁ := by intro h; subst z; exact hseparate hzr.symm
    have hz3 := hthree z hz₁ hz₂ hzw
    obtain ⟨p, _, hp⟩ := hzr.exists_path_of_dist
    have hpos : 0 < p.length := by rw [hp]; exact hzr.pos_dist_of_ne (Ne.symm hz₂)
    have hinside := nearest_higher_path_internal_weight weight hweight p hp hzmin
    obtain ⟨hfirst, hlast⟩ := graph_shortest_twoEnd_lower_bounds G
      (fun i => (weight i : 𝕜)) coeff hA hrow hcoeff p hp hpos (β : 𝕜) hβfield
      (by change (weight B₂ : 𝕜) = (β : 𝕜); exact_mod_cast hB₂) (by change (weight z : 𝕜) = 3; exact_mod_cast hz3)
      (fun i hi hj => by
        change (weight (p.getVert i) : 𝕜) = 2
        exact_mod_cast hinside i hi hj)
    have hd : (1 : 𝕜) ≤ p.length := by
      exact_mod_cast (show 1 ≤ p.length from hpos)
    have hpositive := twoEnd_excludes_nonpositive_charge hβfield hd ha hfirst hlast
      (show (0 : 𝕜) ≤ 0 by norm_num)
    have hbad := hchargeOne z hz₁ hz₂ hz3
    linarith
  intro x y hx hy hxy
  apply Classical.byContradiction
  intro hne
  have hx₁ : x ≠ B₁ := by
    intro h
    subst x
    exact hsep₁ y (Ne.symm hne) hy hxy
  have hx₂ : x ≠ B₂ := by
    intro h
    subst x
    exact hsep₂ y (Ne.symm hne) hy hxy
  have hx3 := hthree x hx₁ hx₂ hx
  obtain ⟨z, hzx, hzw, hzr, hzmin⟩ :=
    exists_nearest_higher_vertex G weight x ⟨y, Ne.symm hne, hy, hxy⟩
  have hz₁ : z ≠ B₁ := by
    intro h
    subst z
    exact hsep₁ x hx₁ hx hzr.symm
  have hz₂ : z ≠ B₂ := by
    intro h
    subst z
    exact hsep₂ x hx₂ hx hzr.symm
  have hz3 := hthree z hz₁ hz₂ hzw
  obtain ⟨p, _, hp⟩ := hzr.exists_path_of_dist
  have hpos : 0 < p.length := by rw [hp]; exact hzr.pos_dist_of_ne (Ne.symm hzx)
  have hinside := nearest_higher_path_internal_weight weight hweight p hp hzmin
  obtain ⟨hxhalf, hzhalf⟩ := graph_shortest_three_three_lower_bounds G
    (fun i => (weight i : 𝕜)) coeff hA hrow hcoeff p hp hpos
    (by change (weight x : 𝕜) = 3; exact_mod_cast hx3) (by change (weight z : 𝕜) = 3; exact_mod_cast hz3)
    (fun i hi hj => by
        change (weight (p.getVert i) : 𝕜) = 2
        exact_mod_cast hinside i hi hj)
  have hpair := pair_le_noncoreSourceMass (fun i => (weight i : 𝕜)) coeff B₁ B₂ x z
    hweight' hcoeff hx₁ hx₂ hz₁ hz₂ (Ne.symm hzx)
    (by change (weight x : 𝕜) = 3; exact_mod_cast hx3) (by change (weight z : 𝕜) = 3; exact_mod_cast hz3)
  have hbad : 1 - (β : 𝕜) + 2 * coeff B₁ + ((β : 𝕜) - 1) * coeff B₂ +
      coeff x + coeff z ≤ 0 := by linarith
  rcases hβ with h3 | h4 | h5
  · rw [h3] at hb hbad
    norm_num at hb hbad
    linarith
  · rw [h4] at hb hbad
    norm_num at hb hbad
    linarith
  · rw [h5] at hb hbad
    norm_num at hb hbad
    linarith

end Matrix

/-- Exact finite-sum adapter from the manuscript's definitions of `v` and
`ell` to the two weaker budgets used by the separation theorem. -/
theorem graph_charge_budgets_of_source_budgets (weight coeff : V → 𝕜)
    (C B₁ B₂ : V) (β : 𝕜) (hB : B₁ ≠ B₂)
    (hB₁ : weight B₁ = 3) (hB₂ : weight B₂ = β) (hC : 0 ≤ coeff C)
    (hell : 0 < 1 - coeff C - coeff B₁ - coeff B₂)
    (hv : 2 - β + dotProduct (fun i => weight i - 2) coeff ≤
      1 - coeff C - coeff B₁ - coeff B₂) :
    coeff B₁ + coeff B₂ < 1 ∧
      1 - β + 2 * coeff B₁ + (β - 1) * coeff B₂ +
        noncoreSourceMass weight coeff B₁ B₂ ≤ 0 := by
  have hs := canonical_source_sum_split weight coeff B₁ B₂ hB
  rw [hB₁, hB₂] at hs
  norm_num at hs
  constructor
  · linarith
  · nlinarith only [hs, hv, hC]

omit [Fintype V] [DecidableEq V] in
/-- Translating reachable-pair uniqueness into the literal assertion that
an actual connected component contains at most one higher-weight vertex. -/
theorem component_heavy_subsingleton_of_reachable_unique (G : SimpleGraph V)
    (weight : V → ℕ)
    (hunique : ∀ x y, 2 < weight x → 2 < weight y → G.Reachable x y → x = y)
    (component : G.ConnectedComponent) :
    Set.Subsingleton {v | v ∈ component.supp ∧ 3 ≤ weight v} := by
  intro x hx y hy
  have hx' := (SimpleGraph.ConnectedComponent.mem_supp_iff component x).mp hx.1
  have hy' := (SimpleGraph.ConnectedComponent.mem_supp_iff component y).mp hy.1
  exact hunique x y
    (Nat.lt_of_lt_of_le (by decide : 2 < 3) hx.2)
    (Nat.lt_of_lt_of_le (by decide : 2 < 3) hy.2)
    (SimpleGraph.ConnectedComponent.exact (hx'.trans hy'.symm))

/-- Component separation from the exact `ell>0` and `v≤ell` expressions of
the manuscript. The expanded charge inequality is derived from the actual
finite canonical-source sum, and the higher-weight uniqueness is proved
by the graph theorem above. -/
theorem component_heavy_subsingleton_of_source_budgets
    [StarRing 𝕜] [TrivialStar 𝕜]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → 𝕜) (C B₁ B₂ : V) (β : ℕ)
    (hβ : β = 3 ∨ β = 4 ∨ β = 5)
    (hweight : ∀ i, 2 ≤ weight i) (hB₁ : weight B₁ = 3) (hB₂ : weight B₂ = β)
    (hother : ∀ i, i ≠ B₁ → i ≠ B₂ → weight i = 2 ∨ weight i = 3)
    (hseparate : ¬ G.Reachable B₁ B₂)
    (hA : (graphWeightMatrix G (fun i => (weight i : 𝕜))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hell : 0 < 1 - coeff C - coeff B₁ - coeff B₂)
    (hv : 2 - (β : 𝕜) + dotProduct (fun i => (weight i : 𝕜) - 2) coeff ≤
      1 - coeff C - coeff B₁ - coeff B₂)
    (component : G.ConnectedComponent) :
    Set.Subsingleton {v | v ∈ component.supp ∧ 3 ≤ weight v} := by
  have hne : B₁ ≠ B₂ := by
    intro h
    subst B₂
    exact hseparate (SimpleGraph.Reachable.refl B₁)
  obtain ⟨hcore, hcharge⟩ := graph_charge_budgets_of_source_budgets
    (fun i => (weight i : 𝕜)) coeff C B₁ B₂ (β : 𝕜) hne
    (by change (weight B₁ : 𝕜) = 3; exact_mod_cast hB₁) (by change (weight B₂ : 𝕜) = (β : 𝕜); exact_mod_cast hB₂) (hcoeff C) hell hv
  exact component_heavy_subsingleton_of_reachable_unique G weight
    (heavy_vertices_eq_of_graph_charge G weight coeff B₁ B₂ β hβ hweight hB₁ hB₂
      hother hseparate hA hrow hcoeff hcore hcharge) component

end KltDP.LinearAlgebra
