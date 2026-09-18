import KltDP.Manuscript.Datum.AnticanonicalClass
import KltDP.LinearAlgebra.Discrepancy
import KltDP.LinearAlgebra.WeightedPathTransport

/-!
# Section 4 discrepancy lemmas

Manuscript `source/manuscript.tex`, Section 4 (lines 824–953):

* `lem:elementary-discrepancy` (Lemma 4.1, lines 844–866): `λ_i ≥ (b-2)/b` for `b = b_i ≥ 3`.
* `lem:discrepancy-separation` (Lemma 4.3, lines 903–938): two distinct higher-weight
  vertices in one connected component of the exceptional graph satisfy `λ_{B_0} + λ_{B_n} ≥ 1`.
* `lem:exceptional-valency` (Lemma 4.4, lines 939–953): every vertex of the exceptional
  dual graph has valency at most three.

All three are derived from the discrepancy row equations `A λ = q` of the resolution datum
(`ResolutionDatum.A_mulVec_lam`), written in graph form
`b_v λ_v - ∑_{u ~ v} λ_u = b_v - 2` via `ResolutionDatum.A_eq_graphWeightMatrix`, together
with `0 ≤ λ < 1`, `b ≥ 2`, and (for the valency bound) positive definiteness of `A`.

For Lemma 4.3 we use the following elementary form of the manuscript's path argument.
Along a path `v_0 — v_1 — ⋯ — v_n` the row equations give, at every interior vertex,
`λ_{v_{t-1}} + λ_{v_{t+1}} ≤ 2 λ_{v_t}` (discrete concavity of `λ`, equivalently discrete
convexity of `1 - λ`), and at a higher-weight endpoint `1 + λ_{v_1} ≤ 3 λ_{v_0}`; chaining
these along the path yields `λ_{v_0} + λ_{v_n} ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open KltDP.Manuscript

universe u

namespace KltDP.Manuscript.S04

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-! ### The row equations in graph form -/

/-- A row of `A = diag(b) - Adj` applied to a vector. -/
theorem A_mulVec_apply [DecidableRel R.graph.Adj] (x : R.Vertices → ℚ) (v : R.Vertices) :
    (R.A *ᵥ x) v = R.w v * x v - ∑ u ∈ R.graph.neighborFinset v, x u := by
  classical
  rw [R.A_eq_graphWeightMatrix]
  simp only [KltDP.LinearAlgebra.graphWeightMatrix, Matrix.sub_mulVec, Pi.sub_apply,
    Matrix.mulVec_diagonal, SimpleGraph.adjMatrix_mulVec_apply]

/-- The discrepancy equation at a vertex: `b_v λ_v - ∑_{u ~ v} λ_u = b_v - 2`. -/
theorem row_equation [DecidableRel R.graph.Adj] (v : R.Vertices) :
    R.w v * R.lam v - ∑ u ∈ R.graph.neighborFinset v, R.lam u = R.w v - 2 := by
  have h := congrFun R.A_mulVec_lam v
  rw [A_mulVec_apply R R.lam v] at h
  exact h

/-- `∑_{u ~ v} λ_u = b_v λ_v - b_v + 2`. -/
theorem sum_lam_neighbors [DecidableRel R.graph.Adj] (v : R.Vertices) :
    ∑ u ∈ R.graph.neighborFinset v, R.lam u = R.w v * R.lam v - R.w v + 2 := by
  have := row_equation R v
  linarith

/-- One neighbour: `λ_u ≤ b_v λ_v - b_v + 2` (the manuscript's `b_j λ_j ≥ b_j - 2 + λ`). -/
theorem lam_le_of_adj {v u : R.Vertices} (h : R.graph.Adj v u) :
    R.lam u ≤ R.w v * R.lam v - R.w v + 2 := by
  classical
  rw [← sum_lam_neighbors R v]
  exact Finset.single_le_sum (fun j _ => R.lam_nonneg j) ((R.graph.mem_neighborFinset v u).2 h)

/-- Two distinct neighbours: `λ_u + λ_{u'} ≤ b_v λ_v - b_v + 2`. -/
theorem two_lam_le_of_adj {v u u' : R.Vertices} (h : R.graph.Adj v u) (h' : R.graph.Adj v u')
    (hne : u ≠ u') : R.lam u + R.lam u' ≤ R.w v * R.lam v - R.w v + 2 := by
  classical
  rw [← sum_lam_neighbors R v]
  exact Finset.add_le_sum (fun j _ => R.lam_nonneg j)
    ((R.graph.mem_neighborFinset v u).2 h) ((R.graph.mem_neighborFinset v u').2 h') hne

/-- Endpoint inequality at a higher-weight vertex: `1 + λ_u ≤ 3 λ_v` for `u ~ v`, `b_v ≥ 3`
(uses `λ_v < 1`). -/
theorem endpoint_bound {v u : R.Vertices} (hv : 3 ≤ R.w v) (h : R.graph.Adj v u) :
    1 + R.lam u ≤ 3 * R.lam v := by
  have h1 := lam_le_of_adj R h
  nlinarith [mul_nonneg (sub_nonneg.2 hv) (sub_nonneg.2 (R.lam_lt_one v).le)]

/-- Discrete concavity of `λ` at a vertex with two distinct neighbours:
`λ_u + λ_{u'} ≤ 2 λ_v` (uses `b_v ≥ 2` and `λ_v < 1`). -/
theorem convexity_bound {v u u' : R.Vertices} (h : R.graph.Adj v u) (h' : R.graph.Adj v u')
    (hne : u ≠ u') : R.lam u + R.lam u' ≤ 2 * R.lam v := by
  have h1 := two_lam_le_of_adj R h h' hne
  nlinarith [mul_nonneg (sub_nonneg.2 (R.two_le_w v)) (sub_nonneg.2 (R.lam_lt_one v).le)]

/-! ### Lemma 4.1: the elementary discrepancy bound -/

/-- Manuscript Lemma 4.1 (`lem:elementary-discrepancy`, lines 844–866):
if `D_i² = -b` with `b ≥ 3` then `λ_i ≥ (b - 2) / b`. -/
theorem elementaryDiscrepancyBound (i : R.Vertices) (hb : 3 ≤ R.w i) :
    (R.w i - 2) / R.w i ≤ R.lam i := by
  have hrow : R.A *ᵥ R.lam = fun j => R.A j j - 2 := R.A_mulVec_lam
  have hdiag : 0 < R.A i i := by
    rw [R.A_diag]
    linarith
  exact KltDP.LinearAlgebra.elementary_discrepancy_bound hrow R.A_offDiag_nonpos R.lam_nonneg
    i hdiag

/-! ### Lemma 4.3: discrepancy separation along a path -/

/-- The path invariant: for a path `x — a — ⋯ — b` (given as `x ~ a` followed by a path
`q : a → b` avoiding `x`) with `b_b ≥ 3`, one has `λ_x + 1 ≤ λ_a + 2 λ_b`.
Induction along `q`, using `convexity_bound` at interior vertices and `endpoint_bound` at `b`. -/
theorem path_key {a b : R.Vertices} (q : R.graph.Walk a b) :
    ∀ x : R.Vertices, R.graph.Adj x a → x ∉ q.support → q.IsPath → 3 ≤ R.w b →
      R.lam x + 1 ≤ R.lam a + 2 * R.lam b := by
  induction q with
  | nil =>
    intro x hxa _ _ hb
    have := endpoint_bound R hb hxa.symm
    linarith
  | @cons a c b h q' ih =>
    intro x hxa hxs hpath hb
    rw [SimpleGraph.Walk.cons_isPath_iff] at hpath
    have hxc : x ≠ c := by
      intro hxc
      apply hxs
      rw [SimpleGraph.Walk.support_cons, hxc]
      exact List.mem_cons_of_mem _ q'.start_mem_support
    have h1 := ih a h hpath.2 hpath.1 hb
    have h2 := convexity_bound R hxa.symm h hxc
    linarith

/-- Manuscript Lemma 4.3 (`lem:discrepancy-separation`, lines 903–938): two distinct
higher-weight vertices in one connected component of the exceptional graph satisfy
`λ_{B_0} + λ_{B_n} ≥ 1`. -/
theorem discrepancySeparation [DecidableRel R.graph.Adj] (i j : R.Vertices) (hne : i ≠ j)
    (hi : 3 ≤ R.w i) (hj : 3 ≤ R.w j) (hreach : R.graph.Reachable i j) :
    1 ≤ R.lam i + R.lam j := by
  classical
  obtain ⟨p⟩ := hreach
  obtain ⟨q, hq⟩ : ∃ q : R.graph.Walk i j, q.IsPath := ⟨p.bypass, p.bypass_isPath⟩
  cases q with
  | nil => exact absurd rfl hne
  | @cons _ c _ h q' =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hq
    have h1 := path_key R q' i h hq.2 hq.1 hj
    have h2 := endpoint_bound R hi h
    linarith

/-! ### Lemma 4.4: valency at most three -/

/-- Positive definiteness of `A` at the test vector `e_v + ∑_{u ~ v} b_u⁻¹ e_u` gives the
manuscript's `u := ∑_{j} 1/b_j < b` at every vertex (the "principal star is negative
definite" step). -/
theorem sum_inv_w_neighbors_lt [DecidableRel R.graph.Adj] (i : R.Vertices) :
    ∑ j ∈ R.graph.neighborFinset i, 1 / R.w j < R.w i := by
  classical
  have hw_pos : ∀ j, 0 < R.w j := fun j => by linarith [R.two_le_w j]
  obtain ⟨u, hu⟩ : ∃ u : ℚ, u = ∑ j ∈ R.graph.neighborFinset i, 1 / R.w j := ⟨_, rfl⟩
  rw [← hu]
  obtain ⟨x, hx⟩ : ∃ x : R.Vertices → ℚ,
      x = fun v => if v = i then 1 else if R.graph.Adj i v then 1 / R.w v else 0 := ⟨_, rfl⟩
  have hxi : x i = 1 := by
    rw [hx]
    simp
  have hxadj : ∀ v, R.graph.Adj i v → x v = 1 / R.w v := by
    intro v hv
    have hvi : v ≠ i := (R.graph.ne_of_adj hv).symm
    rw [hx]
    simp [hvi, hv]
  have hxother : ∀ v, v ≠ i → ¬ R.graph.Adj i v → x v = 0 := by
    intro v hvi hv
    rw [hx]
    simp [hvi, hv]
  have hxnn : ∀ v, 0 ≤ x v := by
    intro v
    rw [hx]
    dsimp only
    split_ifs
    · exact zero_le_one
    · exact div_nonneg zero_le_one (hw_pos v).le
    · exact le_rfl
  have hx0 : x ≠ 0 := by
    intro h
    have := congrFun h i
    simp only [hxi, Pi.zero_apply] at this
    exact one_ne_zero this
  have hpos : 0 < dotProduct x (R.A *ᵥ x) := by
    simpa only [star_trivial] using R.A_posDef.2 x hx0
  have hterm : ∀ v, x v * (R.A *ᵥ x) v ≤ if v = i then R.w i - u else 0 := by
    intro v
    rw [A_mulVec_apply R x v]
    by_cases hvi : v = i
    · rw [if_pos hvi, hvi, hxi]
      have hsum : ∑ u' ∈ R.graph.neighborFinset i, x u' = u := by
        rw [hu]
        exact Finset.sum_congr rfl
          (fun u' hu' => hxadj u' ((R.graph.mem_neighborFinset i u').1 hu'))
      rw [hsum]
      exact le_of_eq (by ring)
    · rw [if_neg hvi]
      by_cases hadj : R.graph.Adj i v
      · have hxv : x v = 1 / R.w v := hxadj v hadj
        have hle : x i ≤ ∑ u' ∈ R.graph.neighborFinset v, x u' :=
          Finset.single_le_sum (fun j _ => hxnn j)
            ((R.graph.mem_neighborFinset v i).2 hadj.symm)
        have hAx : R.w v * x v - ∑ u' ∈ R.graph.neighborFinset v, x u' ≤ 0 := by
          have h1 : R.w v * x v = 1 := by
            rw [hxv]
            exact mul_one_div_cancel (hw_pos v).ne'
          rw [hxi] at hle
          linarith
        have := mul_le_mul_of_nonneg_left hAx (hxnn v)
        simpa using this
      · rw [hxother v hvi hadj]
        simp
  have hle : dotProduct x (R.A *ᵥ x) ≤ R.w i - u := by
    calc dotProduct x (R.A *ᵥ x) = ∑ v, x v * (R.A *ᵥ x) v := rfl
      _ ≤ ∑ v, (if v = i then R.w i - u else 0) := Finset.sum_le_sum (fun v _ => hterm v)
      _ = R.w i - u := by simp
  linarith

/-- Manuscript Lemma 4.4 (`lem:exceptional-valency`, lines 939–953): every vertex of the
exceptional dual graph has valency at most three. -/
theorem exceptionalValencyAtMostThree [DecidableRel R.graph.Adj] (i : R.Vertices) :
    R.graph.degree i ≤ 3 := by
  classical
  have hw_pos : ∀ j, 0 < R.w j := fun j => by linarith [R.two_le_w j]
  obtain ⟨u, hu⟩ : ∃ u : ℚ, u = ∑ j ∈ R.graph.neighborFinset i, 1 / R.w j := ⟨_, rfl⟩
  -- (4) `u < b_i` from positive definiteness
  have hu_lt : u < R.w i := by
    rw [hu]
    exact sum_inv_w_neighbors_lt R i
  -- (1) the row equation at `i`
  have hsum : ∑ j ∈ R.graph.neighborFinset i, R.lam j = R.w i * R.lam i - R.w i + 2 :=
    sum_lam_neighbors R i
  -- (2)+(3) neighbours' row equations, summed: `∑_j (1 - λ_j) ≤ (2 - λ_i) u`
  have hnb : ∑ j ∈ R.graph.neighborFinset i, (1 - R.lam j) ≤ (2 - R.lam i) * u := by
    rw [hu, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hadj : R.graph.Adj i j := (R.graph.mem_neighborFinset i j).1 hj
    have h2 := lam_le_of_adj R hadj.symm
    rw [mul_one_div, le_div_iff₀ (hw_pos j)]
    nlinarith
  have hsplit : ∑ j ∈ R.graph.neighborFinset i, (1 - R.lam j)
      = ((R.graph.neighborFinset i).card : ℚ) - ∑ j ∈ R.graph.neighborFinset i, R.lam j := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- (5) `u ≤ d / 2`
  have hu_le : u ≤ ((R.graph.neighborFinset i).card : ℚ) * (1 / 2) := by
    rw [hu]
    calc ∑ j ∈ R.graph.neighborFinset i, 1 / R.w j
        ≤ ∑ j ∈ R.graph.neighborFinset i, (1 / 2 : ℚ) :=
          Finset.sum_le_sum (fun j _ => one_div_le_one_div_of_le (by norm_num) (R.two_le_w j))
      _ = ((R.graph.neighborFinset i).card : ℚ) * (1 / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hd : ((R.graph.neighborFinset i).card : ℚ) = (R.graph.degree i : ℚ) := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
  have hlam := R.lam_lt_one i
  -- (6) `λ_i < 1` and `b_i - u > 0` force `d < 4`
  have hkey : (R.graph.degree i : ℚ) < 4 := by
    rw [← hd]
    nlinarith [mul_pos (sub_pos.2 hu_lt) (sub_pos.2 hlam), hnb, hsplit, hsum, hu_le]
  have : R.graph.degree i < 4 := by exact_mod_cast hkey
  omega

end KltDP.Manuscript.S04

#print axioms KltDP.Manuscript.S04.elementaryDiscrepancyBound
#print axioms KltDP.Manuscript.S04.discrepancySeparation
#print axioms KltDP.Manuscript.S04.exceptionalValencyAtMostThree
