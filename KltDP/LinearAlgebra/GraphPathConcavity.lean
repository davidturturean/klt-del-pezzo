import KltDP.LinearAlgebra.HeavyVertexSeparation
import KltDP.LinearAlgebra.DiscretePathConcavity
import Mathlib.Tactic

/-!
# Canonical graph rows, path concavity, and the beta-four one-extra case

At a weight-two vertex, the actual canonical row equation says that twice
its coefficient is the sum of all neighboring coefficients. Nonnegative
coefficients therefore imply the first and interior inequalities required
by the proved discrete path concavity theorem.

This argument does not require the initial vertex to have degree one:
additional neighboring terms strengthen the inequalities. The final source
application excludes a connection from C to the sole extra weight-three
vertex when beta is four, using the actual edge bound and v>0.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Row action of the actual diagonal-minus-adjacency matrix, using the
existing Mathlib adjacency-matrix neighbor-sum theorem. -/
theorem graphWeightMatrix_mulVec_apply (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight coeff : V → 𝕜) (v : V) :
    (graphWeightMatrix G weight *ᵥ coeff) v =
      weight v * coeff v - ∑ u ∈ G.neighborFinset v, coeff u := by
  simp only [graphWeightMatrix, Matrix.sub_mulVec, Pi.sub_apply,
    Matrix.mulVec_diagonal, SimpleGraph.adjMatrix_mulVec_apply]

/-- The actual canonical equation at a weight-two vertex. -/
theorem graph_canonical_neighbor_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight coeff : V → 𝕜)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (v : V) (hv : weight v = 2) :
    ∑ u ∈ G.neighborFinset v, coeff u = 2 * coeff v := by
  have h := congrFun hrow v
  rw [graphWeightMatrix_mulVec_apply] at h
  change weight v * coeff v - (∑ u ∈ G.neighborFinset v, coeff u) = weight v - 2 at h
  rw [hv] at h
  linarith

/-- A neighboring coefficient is at most twice the coefficient at a
canonical vertex. No leaf assumption is necessary. -/
theorem graph_neighbor_le_twice (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight coeff : V → 𝕜)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) (v u : V) (hv : weight v = 2) (hvu : G.Adj v u) :
    coeff u ≤ 2 * coeff v := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ G.neighborFinset v) => hcoeff i)
    ((G.mem_neighborFinset v u).mpr hvu)
  rw [graph_canonical_neighbor_sum G weight coeff hrow v hv] at h
  exact h

/-- Two distinct neighboring coefficients have sum at most twice the
coefficient at a canonical vertex. Omitted neighbors have nonnegative terms. -/
theorem graph_neighbors_add_le_twice (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight coeff : V → 𝕜)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) (v u w : V) (hv : weight v = 2)
    (hvu : G.Adj v u) (hvw : G.Adj v w) (hne : u ≠ w) :
    coeff u + coeff w ≤ 2 * coeff v := by
  have h := Finset.add_le_sum (fun i (_ : i ∈ G.neighborFinset v) => hcoeff i)
    ((G.mem_neighborFinset v u).mpr hvu) ((G.mem_neighborFinset v w).mpr hvw) hne
  rw [graph_canonical_neighbor_sum G weight coeff hrow v hv] at h
  exact h

/-- Any actual injectively indexed path with canonical nonterminal vertices
satisfies the length-times-start upper bound. Consecutive adjacency is enough;
inducedness, positive definiteness, acyclicity and degree bounds are not needed. -/
theorem graph_path_endpoint_upper_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight coeff : V → 𝕜)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) (d : ℕ) (e : Fin (d + 1) → V)
    (he : Function.Injective e)
    (hstep : ∀ i : Fin d, G.Adj (e i.castSucc) (e i.succ))
    (hweight : ∀ i : Fin (d + 1), i.val < d → weight (e i) = 2) :
    coeff (e (Fin.last d)) ≤ ((d + 1 : ℕ) : 𝕜) * coeff (e 0) := by
  cases d with
  | zero => simp
  | succ n =>
    let x : Fin (n + 2) → 𝕜 := fun i => coeff (e i)
    have hleaf : x (0 : Fin (n + 1)).succ ≤ 2 * x 0 := by
      exact graph_neighbor_le_twice G weight coeff hrow hcoeff (e 0)
        (e (0 : Fin (n + 1)).succ) (hweight 0 (by simp)) (hstep 0)
    let branch : Fin n → 𝕜 := fun i =>
      2 * x i.castSucc.succ - x i.castSucc.castSucc - x i.succ.succ
    have hbranch : ∀ i, 0 ≤ branch i := by
      intro i
      have hmid : weight (e i.castSucc.succ) = 2 :=
        hweight i.castSucc.succ (by change i.val + 1 < n + 1; have := i.isLt; omega)
      have hleft : G.Adj (e i.castSucc.succ) (e i.castSucc.castSucc) :=
        (hstep i.castSucc).symm
      have hright : G.Adj (e i.castSucc.succ) (e i.succ.succ) := hstep i.succ
      have hne : e i.castSucc.castSucc ≠ e i.succ.succ := by
        intro h
        have hval := congrArg Fin.val (he h)
        change i.val = i.val + 1 + 1 at hval
        omega
      have hsum := graph_neighbors_add_le_twice G weight coeff hrow hcoeff
        (e i.castSucc.succ) (e i.castSucc.castSucc) (e i.succ.succ) hmid hleft hright hne
      dsimp only [branch, x]
      linarith only [hsum]
    have hanti := pathIncrement_antitone_of_rows x branch hbranch (fun _ => rfl)
    exact path_endpoint_le_of_antitone x hanti hleaf

/-- The same bound for an actual graph path, with its actual vertex map. -/
theorem graph_walk_endpoint_upper_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight coeff : V → 𝕜)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) {root target : V} (p : G.Walk root target)
    (hp : p.IsPath) (hweight : ∀ i : ℕ, i < p.length → weight (p.getVert i) = 2) :
    coeff target ≤ ((p.length + 1 : ℕ) : 𝕜) * coeff root := by
  have h := graph_path_endpoint_upper_bound G weight coeff hrow hcoeff p.length
    (walkVertexMap p) (walkVertexMap_injective hp)
    (fun i => by
      change G.Adj (p.getVert i.val) (p.getVert (i.val + 1))
      exact p.adj_getVert_succ i.isLt)
    (fun i hi => hweight i.val hi)
  simpa only [walkVertexMap_zero, walkVertexMap_last] using h

omit [Fintype V] [DecidableEq V] in
/-- If the terminal vertex is the unique higher-weight vertex in its
component, every strictly preterminal path vertex has weight two. -/
theorem path_preterminal_weights_two_of_heavy_unique (G : SimpleGraph V)
    (weight : V → ℕ) (hweight : ∀ i, 2 ≤ weight i)
    (hunique : ∀ x y, 2 < weight x → 2 < weight y → G.Reachable x y → x = y)
    {root target : V} (p : G.Walk root target) (hp : p.IsPath)
    (htarget : 2 < weight target) (i : ℕ) (hi : i < p.length) :
    weight (p.getVert i) = 2 := by
  apply Nat.le_antisymm ?_ (hweight _)
  by_contra! hhigher
  have heq := hunique (p.getVert i) target hhigher htarget (p.drop i).reachable
  have hend := (hp.getVert_eq_end_iff (Nat.le_of_lt hi)).mp heq
  omega

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Exact canonical source mass with one actual noncore noncanonical vertex.
All other noncore contributions vanish by their actual weight-two values. -/
theorem noncoreSourceMass_eq_single_extra (weight coeff : V → 𝕜) (B₁ B₂ T : V)
    (hT₁ : T ≠ B₁) (hT₂ : T ≠ B₂) (hT : weight T = 3)
    (hother : ∀ i, i ≠ B₁ → i ≠ B₂ → i ≠ T → weight i = 2) :
    noncoreSourceMass weight coeff B₁ B₂ = coeff T := by
  have hmem : T ∈ (Finset.univ.erase B₁).erase B₂ := by simp [hT₁, hT₂]
  have hzero : ∀ i ∈ (Finset.univ.erase B₁).erase B₂, i ≠ T →
      (weight i - 2) * coeff i = 0 := by
    intro i hi hiT
    have hi₂ : i ≠ B₂ := (Finset.mem_erase.mp hi).1
    have hi₁ : i ≠ B₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    rw [hother i hi₁ hi₂ hiT]
    simp
  unfold noncoreSourceMass
  rw [Finset.sum_eq_single T hzero (fun h => (h hmem).elim), hT]
  norm_num

/-- The beta-four, one-extra source case: C cannot be connected to the sole
extra weight-three vertex. The positive-v premise is essential and explicit.
The leaf-degree assumption in the manuscript is unnecessary for this argument. -/
theorem beta_four_single_extra_not_reachable
    [StarRing 𝕜] [TrivialStar 𝕜]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → 𝕜) (C B₁ B₂ T : V)
    (hweight : ∀ i, 2 ≤ weight i) (hB₁ : weight B₁ = 3) (hB₂ : weight B₂ = 4)
    (hT₁ : T ≠ B₁) (hT₂ : T ≠ B₂) (hT : weight T = 3)
    (hother : ∀ i, i ≠ B₁ → i ≠ B₂ → i ≠ T → weight i = 2)
    (hseparate : ¬ G.Reachable B₁ B₂) (hedges : G.edgeFinset.card ≤ 3)
    (hA : (graphWeightMatrix G (fun i => (weight i : 𝕜))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hell : 0 < 1 - coeff C - coeff B₁ - coeff B₂)
    (hv : 2 - (4 : 𝕜) + dotProduct (fun i => (weight i : 𝕜) - 2) coeff ≤
      1 - coeff C - coeff B₁ - coeff B₂)
    (hvpos : 0 < 2 - (4 : 𝕜) + dotProduct (fun i => (weight i : 𝕜) - 2) coeff) :
    ¬ G.Reachable C T := by
  have hB : B₁ ≠ B₂ := by
    intro h
    subst B₂
    exact hseparate (SimpleGraph.Reachable.refl B₁)
  have hother' : ∀ i, i ≠ B₁ → i ≠ B₂ → weight i = 2 ∨ weight i = 3 := by
    intro i hi₁ hi₂
    by_cases hiT : i = T
    · exact Or.inr (by simpa only [hiT] using hT)
    · exact Or.inl (hother i hi₁ hi₂ hiT)
  obtain ⟨hcore, hcharge⟩ := graph_charge_budgets_of_source_budgets
    (fun i => (weight i : 𝕜)) coeff C B₁ B₂ (4 : 𝕜) hB
    (by change (weight B₁ : 𝕜) = 3; exact_mod_cast hB₁)
    (by change (weight B₂ : 𝕜) = 4; exact_mod_cast hB₂) (hcoeff C) hell hv
  have hunique := heavy_vertices_eq_of_graph_charge G weight coeff B₁ B₂ 4
    (Or.inr (Or.inl rfl)) hweight hB₁ hB₂ hother' hseparate hA hrow hcoeff hcore hcharge
  intro hreach
  obtain ⟨p, hp, _⟩ := hreach.exists_path_of_dist
  have hpre := path_preterminal_weights_two_of_heavy_unique G weight hweight hunique p hp
    (by rw [hT]; omega : 2 < weight T)
  have hupper := graph_walk_endpoint_upper_bound G (fun i => (weight i : 𝕜)) coeff hrow hcoeff p hp
    (fun i hi => by
      change (weight (p.getVert i) : 𝕜) = 2
      exact_mod_cast hpre i hi)
  have hlength : p.length ≤ 3 := hp.isTrail.length_le_card_edgeFinset.trans hedges
  have hconstant : ((p.length + 1 : ℕ) : 𝕜) ≤ 4 := by
    exact_mod_cast (show p.length + 1 ≤ 4 by omega)
  have hfour : coeff T ≤ 4 * coeff C :=
    hupper.trans (mul_le_mul_of_nonneg_right hconstant (hcoeff C))
  have ha : (1 : 𝕜) / 3 ≤ coeff B₁ := by
    have h := graph_coefficient_lower_bound G (fun i => (weight i : 𝕜)) coeff hrow hcoeff B₁
      (by change (0 : 𝕜) < (weight B₁ : 𝕜); rw [hB₁]; norm_num)
    norm_num [hB₁] at h
    exact h
  have hb : (1 : 𝕜) / 2 ≤ coeff B₂ := by
    have h := graph_coefficient_lower_bound G (fun i => (weight i : 𝕜)) coeff hrow hcoeff B₂
      (by change (0 : 𝕜) < (weight B₂ : 𝕜); rw [hB₂]; norm_num)
    norm_num [hB₂] at h
    exact h
  have hmass := noncoreSourceMass_eq_single_extra (fun i => (weight i : 𝕜)) coeff B₁ B₂ T
    hT₁ hT₂ (by change (weight T : 𝕜) = 3; exact_mod_cast hT)
    (fun i hi₁ hi₂ hiT => by
      change (weight i : 𝕜) = 2
      exact_mod_cast hother i hi₁ hi₂ hiT)
  have hsource := canonical_source_sum_split (fun i => (weight i : 𝕜)) coeff B₁ B₂ hB
  dsimp only at hsource
  rw [hB₁, hB₂, hmass] at hsource
  norm_num at hsource
  rw [hsource] at hvpos
  norm_num at hvpos
  linarith only [hvpos, hell, hfour, ha, hb]

end KltDP.LinearAlgebra
