import KltDP.Manuscript.S04.OneComponentReplacement
import KltDP.Manuscript.S07.Interfaces

/-!
# Manuscript Theorem 4.6: the isolated-`A₁` exchange with its two-curve contraction

Source: `source/manuscript.tex`, lines 1112–1219 (`thm:isolated-node-exchange`).

Fix a resolution datum `R`, an isolated exceptional `(-2)`-curve `W` (`R.w W = 2`, no neighbour in
the exceptional dual graph) and an exterior `(-1)`-curve `P` meeting `W` once and one vertex `B` of
another exceptional component once, with no other contact (`Config`). In the higher-weight case
`b = -B² ≥ 3` this module proves, in the manuscript's order:

* (i) the numerics (lines 1146–1170): with `h = eᵀA⁻¹e = (A⁻¹)_{BB}` and `η = eᵀA⁻¹q = λ_B` —
  realised here as the Schur inverse `g = Replacement.gC R B` and `Replacement.muC R B` of the
  block decomposition of `A` at `B` — the projection identity `pᵀA⁻¹p = 1/2 + h` (`energy`), hence
  `h > 1/2` (`half_lt_gC`); `η < 1`; `B² = -3` (`w_B_eq_three`); `h ≤ η` (`gC_le_muC`);
  `s = aᵀλ₀ = η/h - 1 ∈ [0, 1)` (`muC_eq_gC_mul_one_add`, `s_nonneg`, `s_lt_one`); the valency of
  `B` is positive (`one_le_degree`); the new coefficients `λ₀ = θ = A₀⁻¹q₀` lie in `[0, 1)`.
* (ii) the exchange contraction (lines 1171–1193), performed on `S` itself: the retained family is
  `G = (D − B) ∪ {P}` (`Replacement.famG R B P`, of cardinality `ρ(S) − 1`) with coefficients
  `(θ − e_W, −2)` (`lamX`): the coefficients `−1` on `W` and `−2` on `P` are the discrepancies of the
  composite `S → T → X₀` along the two contracted curves (`K_S = f^*K_T + W + 2P`), and `θ` is
  `λ₀ = A₀⁻¹q₀` on `Δ − B`, unchanged on the other components. The null equations hold
  (`negIntersectionMatrix_famG_mulVec_lamX`), `H₀ = −(K_S + Σ λ_j G_j)` has square
  `L² + 2 − η²/h > 0` (`LsqX_sub_Lsq`), degree `1 − s = 2 − η/h > 0` on `B` (`degree_B`), is nef
  with null locus exactly `G` (`degree_LnumX_eq_zero_iff`), `G` is an SNC forest
  (`famG_acyclic`, `pair_famG'`), and Theorem 2.6 (`anticanonicalContraction`) contracts `G` to a
  rank-one klt del Pezzo surface `X₀` (`anticanonicalContraction_exchange`); a minimal resolution
  of `X₀` has strictly smaller Picard number (`isolatedNodeExchange_datum'`).
* (iii) the singular-point count (lines 1190–1193): the images of the retained components
  `D − W − B` are singular points of `X₀`, `f(W) = f(P)`, and the incidence graph of `G` has
  `#π₀(D) + d − 1` components (`d` the valency of `B`), so
  `#Sing(X) + d − 2 ≤ #Sing(X₀) ≤ #Sing(X) + d − 1` (`singularPoints_card_bounds`). The exact
  value `#Sing(X₀) − #Sing(X) = d − 2` is equivalent to the regularity of the point `f(W) = f(P)`
  of `X₀` (`singularPoints_card_eq_of_regular`); that regularity (the two Castelnuovo blowdowns
  `S → T`, manuscript lines 1176–1182) needs the self-intersection of the image of `W` under the
  contraction of `P`, which the compiled union does not provide (the strict-transform multiplicity
  identification is recorded as open in `Geometry/PointBlowupPullbackWeil`). The lower bound is
  what Theorem 7.1 (lines 2400–2402) consumes.

Main statement for the consumer: `isolatedNodeExchange_datum` (`d ≥ 2`): a resolution datum `R₁`
with `ρ(R₁.S) < ρ(R.S)` and `#Sing(R.X) ≤ #Sing(R₁.X)`.

* (iv) The terminal case `d = 1` (lines 1194–1219) requires blowing up the point `B_T ∩ C_T` of
  `T`; the union supports point blowups only through literals, so the geometric part is **not**
  delivered. Its scalar content is: `terminal_epsilon_eq`, `terminal_epsilon_pos`,
  `terminal_epsilon_lt_muC`, `terminal_rankOne_identity` (the new discrepancy vector
  `λ₀† = λ₀ + ε u` solves `(A₀ + a aᵀ) λ₀† = q₀ + a`, eq:isolated-mixed-new-discrepancy), and
  `terminal_gain_pos` (eq:isolated-mixed-terminal-gain).

The weight-two case (`b = 2`: `W + 2P + B` is a complete rational fibre) is recorded numerically in
`fiberClass_square`, `fiberClass_canonical_degree`, `fiberClass_nef`.

The characteristic hypotheses `(p : ℕ) [CharP k p] (hp : 0 < p)` enter through Lemma 2.8, Theorem
2.6 and the Picard-rank formula, exactly as in `OneComponentReplacement`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix TopologicalSpace
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript KltDP.Manuscript.S02 KltDP.Manuscript.S04.Replacement

universe u

namespace KltDP.Manuscript.S04

/-! ### Graph theory: attaching a leaf to a forest -/

section LeafGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A walk from `a` to `v` with `a ≠ v` uses an edge at `v`. -/
theorem exists_edge_at_end {a v : V} (p : G.Walk a v) :
    a ≠ v → ∃ b, G.Adj v b ∧ s(v, b) ∈ p.edges := by
  induction p with
  | nil => intro h; exact absurd rfl h
  | @cons a c v h q ih =>
    intro _
    by_cases hcv : c = v
    · subst hcv
      refine ⟨a, h.symm, ?_⟩
      rw [SimpleGraph.Walk.edges_cons]
      exact List.mem_cons.mpr (Or.inl Sym2.eq_swap)
    · obtain ⟨b, hb, hmem⟩ := ih hcv
      refine ⟨b, hb, ?_⟩
      rw [SimpleGraph.Walk.edges_cons]
      exact List.mem_cons_of_mem _ hmem

/-- Attaching a leaf to a forest: if every neighbour of `v` is `w`, and every edge of `G` avoiding
`v` is an edge of the acyclic graph `H` (on the same vertex set), then `G` is acyclic. -/
theorem isAcyclic_of_leaf (v w : V) (hleaf : ∀ u, G.Adj v u → u = w)
    (H : SimpleGraph V) (hH : ∀ a b, G.Adj a b → a ≠ v → b ≠ v → H.Adj a b)
    (hHac : H.IsAcyclic) : G.IsAcyclic := by
  classical
  intro u c hc
  by_cases hv : v ∈ c.support
  · have hc' := hc.rotate hv
    generalize c.rotate hv = c' at hc'
    cases c' with
    | nil => exact SimpleGraph.Walk.IsCycle.not_of_nil hc'
    | @cons _ a _ h p =>
      have hav : a ≠ v := (G.ne_of_adj h).symm
      obtain ⟨b, hb, hmem⟩ := exists_edge_at_end p hav
      have ha := hleaf _ h
      have hb' := hleaf _ hb
      have hnodup := hc'.isCircuit.isTrail.edges_nodup
      rw [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
      apply hnodup.1
      rw [show s(v, a) = s(v, b) from by rw [ha, hb']]
      exact hmem
  · have hedges : ∀ e ∈ c.edges, e ∈ H.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        have hab : G.Adj a b := c.edges_subset_edgeSet he
        have ha : a ≠ v := fun h => hv (h ▸ c.fst_mem_support_of_mem_edges he)
        have hb : b ≠ v := fun h => hv (h ▸ c.snd_mem_support_of_mem_edges he)
        exact hH a b hab ha hb
    exact hHac (c.transfer H hedges) (hc.transfer hedges)

end LeafGraph

namespace IsolatedNodeExchange

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k) [DecidableEq R.Vertices]
  (W B : R.Vertices) (P : R.S.PrimeCurve)

/-- The configuration of Theorem 4.6 (manuscript lines 1114–1117, higher-weight case): `P` is an
exterior `(-1)`-curve, `W` is an isolated `(-2)`-curve, `P` meets `W` and `B` once each and no
other exceptional curve, and `B` has weight at least three. -/
structure Config : Prop where
  hP : R.IsExteriorMinusOne P
  hW2 : R.w W = 2
  hWiso : ∀ y : R.Vertices, ¬ R.graph.Adj W y
  hWB : W ≠ B
  hPW : R.contact P W = 1
  hPB : R.contact P B = 1
  hP0 : ∀ i : R.Vertices, i ≠ W → i ≠ B → R.contact P i = 0
  hB3 : 3 ≤ R.w B

/-- `W` as a member of `D − B`. -/
abbrev Wd (hc : Config R W B P) : D0 R B := ⟨W, hc.hWB⟩

/-! ### (i) Isolation of `W` in the matrices -/

/-- Column `W` of `A`: `A_{iW} = 2 δ_{iW}`. -/
theorem A_apply_W (hc : Config R W B P) (i : R.Vertices) :
    R.A i W = if i = W then 2 else 0 := by
  classical
  rw [R.A_eq_graphWeightMatrix, KltDP.LinearAlgebra.graphWeightMatrix_apply]
  by_cases h : i = W
  · rw [if_pos h, if_pos h, h, hc.hW2]
  · rw [if_neg h, if_neg h, if_neg (fun hadj => hc.hWiso i hadj.symm)]

theorem A_W_apply (hc : Config R W B P) (i : R.Vertices) :
    R.A W i = if i = W then 2 else 0 := by
  rw [A_symm R W i, A_apply_W R W B P hc i]

/-- Column `W` of the block `A₀ = M`. -/
theorem Mblock_apply_Wd (hc : Config R W B P) (i : D0 R B) :
    Mblock R B i (Wd R W B P hc) = if i = Wd R W B P hc then 2 else 0 := by
  show R.A i.1 W = _
  rw [A_apply_W R W B P hc i.1]
  by_cases h : i = Wd R W B P hc
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'))]

/-- Row `W` of `A₀ x` is `2 x_W`. -/
theorem Mblock_mulVec_apply_Wd (hc : Config R W B P) (x : D0 R B → ℚ) :
    (Mblock R B *ᵥ x) (Wd R W B P hc) = 2 * x (Wd R W B P hc) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Wd R W B P hc)]
  · rw [Mblock_symm R B, Mblock_apply_Wd R W B P hc, if_pos rfl]
  · intro j _ hj
    rw [Mblock_symm R B, Mblock_apply_Wd R W B P hc, if_neg hj, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem q0_Wd (hc : Config R W B P) : q0 R B (Wd R W B P hc) = 0 := by
  show R.w W - 2 = 0
  rw [hc.hW2]
  norm_num

theorem vvec_Wd (hc : Config R W B P) : vvec R B (Wd R W B P hc) = 0 := by
  show -R.A B W = 0
  rw [A_apply_W R W B P hc B, if_neg (Ne.symm hc.hWB)]
  norm_num

/-- `θ_W = 0`: the new coefficient of the isolated `(-2)`-curve vanishes. -/
theorem theta_Wd (hc : Config R W B P) : theta R B (Wd R W B P hc) = 0 := by
  have h := Mblock_mulVec_apply_Wd R W B P hc (theta R B)
  rw [Mblock_mulVec_theta R B, q0_Wd R W B P hc] at h
  linarith

/-- `u_W = 0`. -/
theorem wv_Wd (hc : Config R W B P) : wv R B (Wd R W B P hc) = 0 := by
  have h := Mblock_mulVec_apply_Wd R W B P hc (wv R B)
  rw [Mblock_mulVec_wv R B, vvec_Wd R W B P hc] at h
  linarith

/-- `λ_W = 0`. -/
theorem lam_W (hc : Config R W B P) : R.lam W = 0 := by
  have h := congrFun (lam0_eq R B) (Wd R W B P hc)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, theta_Wd R W B P hc, wv_Wd R W B P hc,
    mul_zero, add_zero] at h
  exact h

/-! ### (i) The contact vector and the projection identity `pᵀA⁻¹p = 1/2 + h` -/

/-- `p = e_W + e_B`. -/
theorem contactVector_eq_single (hc : Config R W B P) :
    contactVector R P = Pi.single W (1 : ℚ) + Pi.single B 1 := by
  funext i
  rw [Pi.add_apply, contactVector_eq R P i]
  by_cases hiW : i = W
  · rw [hiW, Pi.single_eq_same, Pi.single_eq_of_ne hc.hWB, hc.hPW]
    norm_num
  · by_cases hiB : i = B
    · rw [hiB, Pi.single_eq_of_ne (Ne.symm hc.hWB), Pi.single_eq_same, hc.hPB]
      norm_num
    · rw [Pi.single_eq_of_ne hiW, Pi.single_eq_of_ne hiB, hc.hP0 i hiW hiB]
      norm_num

theorem A_inv_mulVec_of_mulVec {x y : R.Vertices → ℚ} (h : R.A *ᵥ x = y) : R.A⁻¹ *ᵥ y = x := by
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (A_det_isUnit R), Matrix.one_mulVec]

/-- `A ((1/2) e_W) = e_W`. -/
theorem A_mulVec_half_single_W (hc : Config R W B P) :
    R.A *ᵥ ((1 / 2 : ℚ) • (Pi.single W (1 : ℚ) : R.Vertices → ℚ)) = Pi.single W 1 := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
  funext i
  rw [Pi.smul_apply, Matrix.transpose_apply, A_apply_W R W B P hc i, smul_eq_mul, Pi.single_apply]
  split_ifs <;> norm_num

/-- The solution `z = (g, g u)` of `A z = e_B`, so `(A⁻¹)_{BB} = g = h`. -/
def zB : R.Vertices → ℚ := ext R B (gC R B) (gC R B • wv R B)

theorem A_mulVec_zB : R.A *ᵥ zB R B = Pi.single B 1 := by
  funext i
  by_cases h : i = B
  · rw [h, Pi.single_eq_same]
    unfold zB
    rw [mulVec_ext_C, dotProduct_smul, smul_eq_mul]
    have hg := gC_mul_schur R B
    unfold schur at hg
    linear_combination hg
  · rw [Pi.single_eq_of_ne h]
    have hi : i = (⟨i, h⟩ : D0 R B).1 := rfl
    rw [hi]
    unfold zB
    rw [mulVec_ext_val, Matrix.mulVec_smul, Mblock_mulVec_wv]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Manuscript line 1152, the projection quadratic form: `pᵀA⁻¹p = 1/2 + h`. -/
theorem energy (hc : Config R W B P) :
    contactVector R P ⬝ᵥ (R.A⁻¹ *ᵥ contactVector R P) = 1 / 2 + gC R B := by
  rw [contactVector_eq_single R W B P hc, Matrix.mulVec_add,
    A_inv_mulVec_of_mulVec R (A_mulVec_half_single_W R W B P hc),
    A_inv_mulVec_of_mulVec R (A_mulVec_zB R B)]
  rw [add_dotProduct, dotProduct_add, dotProduct_add, single_dotProduct, single_dotProduct,
    single_dotProduct, single_dotProduct]
  simp only [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hc.hWB), smul_eq_mul]
  unfold zB
  rw [ext_C, ext_apply_of_ne R B _ _ hc.hWB]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [wv_Wd R W B P hc]
  ring

/-- Manuscript line 1152: `1/2 + h > 1`, i.e. `h > 1/2` (Lemma 2.8). -/
theorem half_lt_gC (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) : 1 / 2 < gC R B := by
  have h := rankOneProjection_green_gt_one R p hp P hc.hP
  rw [energy R W B P hc] at h
  linarith

/-- `η = λ_B < 1` (the discrepancy sum, manuscript line 1152). -/
theorem muC_lt_one : muC R B < 1 := R.lam_lt_one B

theorem muC_nonneg' : 0 ≤ muC R B := R.lam_nonneg B

/-- `s = aᵀλ₀ ≥ 0`. -/
theorem s_nonneg : 0 ≤ vvec R B ⬝ᵥ theta R B :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (vvec_nonneg R B i) (theta_nonneg R B i))

/-- Manuscript lines 1153–1154: `η ≥ (b - 2) h` forces `b = 3`. -/
theorem w_B_eq_three (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) : R.w B = 3 := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, R.w B = (n : ℚ) := ⟨_, w_eq_intCast R B⟩
  have hmu := muC_eq R B
  have hg := half_lt_gC R W B P p hp hc
  have hη := muC_lt_one R B
  have hs := s_nonneg R B
  have hgpos := gC_pos R B
  have hb3 := hc.hB3
  have h1 : gC R B * (R.w B - 2) ≤ muC R B := by
    rw [hmu]
    unfold bC
    nlinarith [mul_nonneg hgpos.le hs]
  have hlt : R.w B < 4 := by
    by_contra hcon
    push_neg at hcon
    have h2 := mul_nonneg hgpos.le (sub_nonneg.2 hcon)
    have e : gC R B * (R.w B - 2) = 2 * gC R B + gC R B * (R.w B - 4) := by ring
    linarith
  rw [hn] at hlt hb3
  have hn4 : n < 4 := by exact_mod_cast hlt
  have hn3 : (3 : ℤ) ≤ n := by exact_mod_cast hb3
  have : n = 3 := by omega
  rw [hn, this]
  norm_num

/-- `η = h (1 + s)` (manuscript eq:isolated-mixed-st, `s = η/h - 1`). -/
theorem muC_eq_gC_mul_one_add (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    muC R B = gC R B * (1 + vvec R B ⬝ᵥ theta R B) := by
  rw [muC_eq R B]
  unfold bC
  rw [w_B_eq_three R W B P p hp hc]
  ring

/-- Manuscript line 1154: `h ≤ η`. -/
theorem gC_le_muC (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) : gC R B ≤ muC R B := by
  rw [muC_eq_gC_mul_one_add R W B P p hp hc]
  nlinarith [gC_pos R B, s_nonneg R B]

/-- `s < 1` (equivalently `η < 2h`). -/
theorem s_lt_one (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    vvec R B ⬝ᵥ theta R B < 1 := by
  have h := muC_eq_gC_mul_one_add R W B P p hp hc
  have hg := half_lt_gC R W B P p hp hc
  have hη := muC_lt_one R B
  by_contra hcon
  push_neg at hcon
  have h2 := mul_nonneg (gC_pos R B).le (sub_nonneg.2 hcon)
  have e : gC R B * (1 + vvec R B ⬝ᵥ theta R B) =
      2 * gC R B + gC R B * (vvec R B ⬝ᵥ theta R B - 1) := by ring
  linarith

/-- `t = aᵀu = 3 - 1/h` (manuscript eq:isolated-mixed-st). -/
theorem t_eq (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    vvec R B ⬝ᵥ wv R B = 3 - 1 / gC R B := by
  have h := gC_mul_schur R B
  unfold schur bC at h
  rw [w_B_eq_three R W B P p hp hc] at h
  have hg := (gC_pos R B).ne'
  field_simp
  linarith

/-- `h < 1`. -/
theorem gC_lt_one (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) : gC R B < 1 :=
  lt_of_le_of_lt (gC_le_muC R W B P p hp hc) (muC_lt_one R B)

/-- The new coefficients `λ₀ = θ` lie in `[0, 1)` (manuscript line 1170). -/
theorem theta_lt_one (i : D0 R B) : theta R B i < 1 :=
  lt_of_le_of_lt (theta_le_lam0 R B i) (lam0_lt_one R B i)

/-- Manuscript line 1155: an isolated `B` would have `h = 1/3`, so `d ≥ 1`. -/
theorem one_le_degree [DecidableRel R.graph.Adj] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hc : Config R W B P) : 1 ≤ R.graph.degree B := by
  by_contra hcon
  push_neg at hcon
  have hnoadj : ∀ i, ¬ R.graph.Adj B i := by
    intro i hi
    have := (SimpleGraph.degree_pos_iff_exists_adj (G := R.graph) (v := B)).mpr ⟨i, hi⟩
    omega
  have hv : vvec R B = 0 := by
    funext i
    show -R.A B i.1 = 0
    rw [R.A_eq_graphWeightMatrix, KltDP.LinearAlgebra.graphWeightMatrix_apply,
      if_neg (fun h => i.2 h.symm), if_neg (hnoadj i.1)]
    norm_num
  have hwv : wv R B = 0 := by
    unfold wv
    rw [hv, Matrix.mulVec_zero]
  have hschur : schur R B = 3 := by
    unfold schur
    rw [hwv, dotProduct_zero, sub_zero]
    exact w_B_eq_three R W B P p hp hc
  have hg : gC R B = 1 / 3 := by
    unfold gC
    rw [hschur]
    norm_num
  have := half_lt_gC R W B P p hp hc
  rw [hg] at this
  norm_num at this

/-! ### (ii) The retained family `G = (D − B) ∪ {P}` and its coefficients `(θ − e_W, −2)` -/

/-- The new coefficients on `D − B`: `θ` (that is `λ₀ = A₀⁻¹ q₀` on `Δ − B` and the unchanged `λ`
on the other components) and `−1` on `W` (since `θ_W = 0`). -/
def lamX0 (hc : Config R W B P) : D0 R B → ℚ := theta R B - Pi.single (Wd R W B P hc) 1

/-- The coefficient vector `(θ − e_W, −2)` on the family `(D − B) ∪ {P}` (manuscript lines
1177–1178: `K_S = f^*K_T + W + 2P`). -/
def lamX (hc : Config R W B P) : D0 R B ⊕ Unit → ℚ :=
  Sum.elim (lamX0 R W B P hc) (fun _ => -2)

@[simp] theorem lamX_inl (hc : Config R W B P) (i : D0 R B) :
    lamX R W B P hc (Sum.inl i) = lamX0 R W B P hc i := rfl
@[simp] theorem lamX_inr (hc : Config R W B P) (u : Unit) : lamX R W B P hc (Sum.inr u) = -2 := rfl

theorem lamX0_apply (hc : Config R W B P) (i : D0 R B) :
    lamX0 R W B P hc i = theta R B i - if i = Wd R W B P hc then 1 else 0 := by
  simp only [lamX0, Pi.sub_apply, Pi.single_apply]

theorem lamX0_Wd (hc : Config R W B P) : lamX0 R W B P hc (Wd R W B P hc) = -1 := by
  rw [lamX0_apply, if_pos rfl, theta_Wd R W B P hc]
  norm_num

theorem lamX0_of_ne (hc : Config R W B P) (i : D0 R B) (hi : i ≠ Wd R W B P hc) :
    lamX0 R W B P hc i = theta R B i := by
  rw [lamX0_apply, if_neg hi, sub_zero]

theorem lamX0_le_theta (hc : Config R W B P) (i : D0 R B) : lamX0 R W B P hc i ≤ theta R B i := by
  rw [lamX0_apply]
  split_ifs <;> linarith

theorem lamX0_lt_one (hc : Config R W B P) (i : D0 R B) : lamX0 R W B P hc i < 1 :=
  lt_of_le_of_lt (lamX0_le_theta R W B P hc i) (theta_lt_one R B i)

theorem lamX0_le_lam0 (hc : Config R W B P) (i : D0 R B) : lamX0 R W B P hc i ≤ lam0 R B i :=
  le_trans (lamX0_le_theta R W B P hc i) (theta_le_lam0 R B i)

theorem lamX0_nonneg_of_ne (hc : Config R W B P) (i : D0 R B) (hi : i ≠ Wd R W B P hc) :
    0 ≤ lamX0 R W B P hc i := by
  rw [lamX0_of_ne R W B P hc i hi]
  exact theta_nonneg R B i

theorem lamX_lt_one (hc : Config R W B P) (j : D0 R B ⊕ Unit) : lamX R W B P hc j < 1 := by
  rcases j with i | u
  · exact lamX0_lt_one R W B P hc i
  · show (-2 : ℚ) < 1
    norm_num

/-- The contacts of `P` with `D − B`: `r = e_W`. -/
theorem rvec_eq (hc : Config R W B P) : rvec R B P = Pi.single (Wd R W B P hc) 1 := by
  funext i
  show contactVector R P i.1 = _
  rw [contactVector_eq_single R W B P hc, Pi.add_apply, Pi.single_eq_of_ne i.2, add_zero,
    Pi.single_apply, Pi.single_apply]
  by_cases h : i = Wd R W B P hc
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'))]

theorem rvec_le_one (hc : Config R W B P) (i : D0 R B) : rvec R B P i ≤ 1 := by
  rw [rvec_eq R W B P hc, Pi.single_apply]
  split_ifs <;> norm_num

/-- `A₀ (θ − e_W) = q₀ − 2 e_W`. -/
theorem Mblock_mulVec_lamX0 (hc : Config R W B P) :
    Mblock R B *ᵥ lamX0 R W B P hc = q0 R B - fun i => if i = Wd R W B P hc then 2 else 0 := by
  unfold lamX0
  rw [Matrix.mulVec_sub, Mblock_mulVec_theta, Matrix.mulVec_single_one]
  congr 1
  funext i
  rw [Matrix.transpose_apply, Mblock_apply_Wd R W B P hc i]

/-- The null equations `A_G (θ − e_W, −2) = q_G` for the retained family (manuscript lines
1177–1183). -/
theorem negIntersectionMatrix_famG_mulVec_lamX (hc : Config R W B P) :
    negIntersectionMatrix R.S R.hreg (famG R B P) *ᵥ lamX R W B P hc =
      canonicalDegreeVector R.S (famG R B P) R.KS := by
  have hM := Mblock_mulVec_lamX0 R W B P hc
  have hr := rvec_eq R W B P hc
  funext x
  rcases x with i | u
  · rw [canonicalDegreeVector_famG_inl, mulVec_sum_apply]
    simp only [negIntersectionMatrix_famG_inl_inl, negIntersectionMatrix_famG_inl_inr,
      lamX_inl, lamX_inr]
    have hMi := congrFun hM i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply] at hMi
    rw [hMi, hr, Pi.single_apply]
    split_ifs <;> ring
  · rw [canonicalDegreeVector_famG_inr R B P hc.hP.1, mulVec_sum_apply]
    simp only [negIntersectionMatrix_famG_inr_inl, negIntersectionMatrix_famG_inr_inr R B P hc.hP.1,
      lamX_inl, lamX_inr]
    rw [hr, Finset.sum_eq_single (Wd R W B P hc)]
    · rw [Pi.single_eq_same, lamX0_Wd R W B P hc]
      norm_num
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj]
      ring
    · intro h
      exact absurd (Finset.mem_univ _) h

/-! ### (ii) The class `H₀ = −(K_S + Σ λ_j G_j)`: square and degree on `B` -/

/-- `H₀ ∈ N¹(S)_ℚ`, the pullback of `−K_{X₀}` to `S`. -/
def LnumX (hc : Config R W B P) : R.S.NumericalClassGroup :=
  adjustedClass R.S R.hreg (famG R B P) R.KS (lamX R W B P hc)

/-- `H₀²`. -/
def LsqX (hc : Config R W B P) : ℚ :=
  R.S.numericalIntersectionBilinForm R.hreg (LnumX R W B P hc) (LnumX R W B P hc)

theorem lamX_dot_canonicalDegreeVector (hc : Config R W B P) :
    lamX R W B P hc ⬝ᵥ canonicalDegreeVector R.S (famG R B P) R.KS =
      theta R B ⬝ᵥ q0 R B + 2 := by
  rw [dot_sum R B]
  simp only [lamX_inl, lamX_inr, canonicalDegreeVector_famG_inl,
    canonicalDegreeVector_famG_inr R B P hc.hP.1]
  have : ∑ j : D0 R B, lamX0 R W B P hc j * q0 R B j = lamX0 R W B P hc ⬝ᵥ q0 R B := rfl
  rw [this]
  unfold lamX0
  rw [sub_dotProduct, single_dotProduct, q0_Wd R W B P hc]
  ring

/-- `H₀² = K_S² + θᵀq₀ + 2` (Lemma 2.5). -/
theorem LsqX_eq (hc : Config R W B P) : LsqX R W B P hc = R.Ksq + (theta R B ⬝ᵥ q0 R B + 2) := by
  unfold LsqX LnumX
  rw [square_formula R.S R.hreg (famG R B P) R.KS (lamX R W B P hc)
    (negIntersectionMatrix_famG_mulVec_lamX R W B P hc), lamX_dot_canonicalDegreeVector R W B P hc]
  rfl

/-- `L² = K_S² + θᵀq₀ + η²/h` (the Schur identity `qᵀA⁻¹q = q₀ᵀλ₀ + η²/h`, eq:isolated-mixed-st). -/
theorem Lsq_eq_exchange (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    R.Lsq = R.Ksq + (theta R B ⬝ᵥ q0 R B + muC R B ^ 2 / gC R B) := by
  rw [Lsq_eq_block R B, lam0_eq R B, dotProduct_add, dotProduct_smul, smul_eq_mul, q0_dot_wv R B]
  unfold bC
  rw [w_B_eq_three R W B P p hp hc]
  have hmu := muC_eq_gC_mul_one_add R W B P p hp hc
  have hg := (gC_pos R B).ne'
  have h1 : muC R B / gC R B = 1 + vvec R B ⬝ᵥ theta R B := by
    rw [hmu, mul_div_cancel_left₀ _ hg]
  have h2 : muC R B ^ 2 / gC R B = muC R B * (1 + vvec R B ⬝ᵥ theta R B) := by
    rw [pow_two, mul_div_assoc, h1]
  rw [h2, dotProduct_comm (q0 R B) (theta R B)]
  ring

/-- eq:isolated-mixed-nonterminal-gain: `K_{X₀}² − K_X² = H₀² − L² = 2 − η²/h`. -/
theorem LsqX_sub_Lsq (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    LsqX R W B P hc - R.Lsq = 2 - muC R B ^ 2 / gC R B := by
  rw [LsqX_eq R W B P hc, Lsq_eq_exchange R W B P p hp hc]
  ring

theorem Lsq_lt_LsqX (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    R.Lsq < LsqX R W B P hc := by
  have h := KltDP.LinearAlgebra.isolated_exchange_square_gain_pos (half_lt_gC R W B P p hp hc)
    (gC_le_muC R W B P p hp hc) (muC_lt_one R B)
  have h2 := LsqX_sub_Lsq R W B P p hp hc
  linarith

theorem LsqX_pos (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) : 0 < LsqX R W B P hc :=
  lt_trans R.Lsq_pos (Lsq_lt_LsqX R W B P p hp hc)

/-- Manuscript line 1183: the degree of `H₀` on the deleted curve `B` is `1 − s = 2 − η/h`. -/
theorem degree_B (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    R.S.numericalRestrictionDegree B.1 (LnumX R W B P hc) = 1 - vvec R B ⬝ᵥ theta R B := by
  unfold LnumX
  rw [degree_formula R.S R.hreg (famG R B P) R.KS (lamX R W B P hc) B.1]
  have hK : (B.1.intersectionNumber R.KS : ℚ) = R.w B - 2 := R.Kdeg_exceptional B
  rw [hK, dot_sum R B]
  simp only [famG_inl, famG_inr, lamX_inl, lamX_inr, C_intersectionNumber_val]
  rw [C_intersectionNumber_P R B P]
  have hv : ∑ i : D0 R B, vvec R B i * lamX0 R W B P hc i = vvec R B ⬝ᵥ theta R B := by
    show vvec R B ⬝ᵥ lamX0 R W B P hc = _
    unfold lamX0
    rw [dotProduct_sub, dotProduct_single, vvec_Wd R W B P hc]
    ring
  rw [hv]
  have hm : mC R B P = 1 := by
    show contactVector R P B = 1
    rw [contactVector_eq R P B, hc.hPB]
    norm_num
  rw [hm, w_B_eq_three R W B P p hp hc]
  ring

theorem degree_B_pos (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    0 < R.S.numericalRestrictionDegree B.1 (LnumX R W B P hc) := by
  rw [degree_B R W B P p hp hc]
  linarith [s_lt_one R W B P p hp hc]

/-! ### (ii) `H₀` is nef with null locus exactly `G` -/

/-- `H₀ = L + η B + Σ_{D−B} (λ_i − λ_i^new) D_i + 2P` in `N¹(S)_ℚ` (the analogue of
eq:replacement-effective-difference). -/
theorem LnumX_eq (hc : Config R W B P) :
    LnumX R W B P hc = R.Lnum + muC R B • DisjointNegativeCurvesRank.curveClass R.S R.hreg B.1 +
      ∑ i : D0 R B, (lam0 R B i - lamX0 R W B P hc i) •
        DisjointNegativeCurvesRank.curveClass R.S R.hreg i.1.1 +
      (2 : ℚ) • DisjointNegativeCurvesRank.curveClass R.S R.hreg P := by
  rw [R.Lnum_eq]
  unfold LnumX adjustedClass curveCombination
  rw [Fintype.sum_sum_type, Fintype.sum_unique (fun u : Unit =>
    lamX R W B P hc (Sum.inr u) •
      DisjointNegativeCurvesRank.curveClass R.S R.hreg (famG R B P (Sum.inr u)))]
  rw [sum_split' R B (fun i : R.Vertices =>
    R.lam i • DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val)]
  simp only [famG_inl, famG_inr, lamX_inl, lamX_inr, sub_smul, Finset.sum_sub_distrib, neg_smul]
  unfold muC lam0 ResolutionDatum.Knum
  abel

theorem lam0_sub_lamX0_nonneg (hc : Config R W B P) (i : D0 R B) :
    0 ≤ lam0 R B i - lamX0 R W B P hc i :=
  sub_nonneg.2 (lamX0_le_lam0 R W B P hc i)

/-- The degree of `H₀` on a prime curve `Q`. -/
theorem degree_LnumX (hc : Config R W B P) (Q : R.S.PrimeCurve) :
    R.S.numericalRestrictionDegree Q (LnumX R W B P hc) =
      R.Ldeg Q + muC R B * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg B.1) : ℚ) +
      ∑ i : D0 R B, (lam0 R B i - lamX0 R W B P hc i) *
        (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1.1) : ℚ) +
      2 * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) := by
  rw [LnumX_eq]
  simp only [map_add, map_sum, map_smul, smul_eq_mul, R.numericalRestrictionDegree_Lnum,
    numericalRestrictionDegree_curveClass R.S R.hreg]

/-- `H₀ · Q > 0` for every exterior prime curve `Q ≠ P`. -/
theorem degree_LnumX_pos_of_exterior (hc : Config R W B P) (Q : R.S.PrimeCurve)
    (hQ : ¬ IsExceptionalCurve R.π Q) (hQP : Q ≠ P) :
    0 < R.S.numericalRestrictionDegree Q (LnumX R W B P hc) := by
  rw [degree_LnumX]
  have h1 := Ldeg_pos R Q hQ
  have h2 : 0 ≤ muC R B * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg B.1) : ℚ) :=
    mul_nonneg (muC_nonneg' R B)
      (intersectionNumber_nonneg_of_ne R Q B.1 (fun h => hQ (by rw [h]; exact B.2)))
  have h3 : 0 ≤ ∑ i : D0 R B, (lam0 R B i - lamX0 R W B P hc i) *
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1.1) : ℚ) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (lam0_sub_lamX0_nonneg R W B P hc i)
      (intersectionNumber_nonneg_of_ne R Q i.1.1 (fun h => hQ (by rw [h]; exact i.1.2))))
  have h4 : 0 ≤ 2 * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) :=
    mul_nonneg (by norm_num) (intersectionNumber_nonneg_of_ne R Q P hQP)
  linarith

/-- `H₀ · G_j = 0` for every member of the retained family (the null equations). -/
theorem degree_LnumX_famG (hc : Config R W B P) (j : D0 R B ⊕ Unit) :
    R.S.numericalRestrictionDegree (famG R B P j) (LnumX R W B P hc) = 0 := by
  unfold LnumX
  rw [degree_formula R.S R.hreg (famG R B P) R.KS (lamX R W B P hc) (famG R B P j)]
  have hnull := congrFun (negIntersectionMatrix_famG_mulVec_lamX R W B P hc) j
  have hrow : (fun l => ((famG R B P j).intersectionNumber
      (R.S.primeCurveCartier R.hreg (famG R B P l)) : ℚ)) ⬝ᵥ lamX R W B P hc =
      -(negIntersectionMatrix R.S R.hreg (famG R B P) *ᵥ lamX R W B P hc) j := by
    simp only [Matrix.mulVec, dotProduct, negIntersectionMatrix,
      NullCurveIntersectionMatrix.intersectionMatrix, Matrix.neg_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber]
    ring
  rw [hrow, hnull]
  unfold canonicalDegreeVector
  ring

/-- `H₀` is nef. -/
theorem degree_LnumX_nonneg (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P)
    (Q : R.S.PrimeCurve) : 0 ≤ R.S.numericalRestrictionDegree Q (LnumX R W B P hc) := by
  by_cases hQ : IsExceptionalCurve R.π Q
  · by_cases hQB : Q = B.1
    · rw [hQB]
      exact (degree_B_pos R W B P p hp hc).le
    · have h := degree_LnumX_famG R W B P hc
        (Sum.inl ⟨⟨Q, hQ⟩, fun h => hQB (congrArg Subtype.val h)⟩)
      exact le_of_eq h.symm
  · by_cases hQP : Q = P
    · rw [hQP]
      exact le_of_eq (degree_LnumX_famG R W B P hc (Sum.inr ())).symm
    · exact (degree_LnumX_pos_of_exterior R W B P hc Q hQ hQP).le

/-- The null locus of `H₀` is exactly `G = (D − B) ∪ {P}` (manuscript lines 1184–1186). -/
theorem degree_LnumX_eq_zero_iff (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P)
    (Q : R.S.PrimeCurve) :
    R.S.numericalRestrictionDegree Q (LnumX R W B P hc) = 0 ↔ ∃ j, Q = famG R B P j := by
  constructor
  · intro h0
    by_cases hQ : IsExceptionalCurve R.π Q
    · by_cases hQB : Q = B.1
      · exfalso
        rw [hQB] at h0
        exact (degree_B_pos R W B P p hp hc).ne' h0
      · exact ⟨Sum.inl ⟨⟨Q, hQ⟩, fun h => hQB (congrArg Subtype.val h)⟩, rfl⟩
    · by_cases hQP : Q = P
      · exact ⟨Sum.inr (), hQP⟩
      · exfalso
        exact (degree_LnumX_pos_of_exterior R W B P hc Q hQ hQP).ne' h0
  · rintro ⟨j, rfl⟩
    exact degree_LnumX_famG R W B P hc j

/-! ### (ii) A Cartier multiple of `H₀` -/

/-- Clearing denominators of an arbitrary rational Weil divisor `D` on `S`: an actual Cartier divisor
`Hm` with `Hm = −n D`. -/
theorem exists_cartier_multiple' (D : R.S.RationalWeilDivisor) :
    ∃ (n : ℕ) (Hm : CartierDivisor R.S.toScheme), 0 < n ∧
      R.S.rationalCartierToWeilHom Hm = -((n : ℚ) • D) := by
  obtain ⟨n, hn, A, hA⟩ := R.S.exists_positive_integral_multiple D
  refine ⟨n, (R.S.regularCartierWeilEquiv R.hreg).symm (-A), hn, ?_⟩
  have h1 : R.S.rationalCartierToWeilHom ((R.S.regularCartierWeilEquiv R.hreg).symm (-A)) =
      rationalizeWeilDivisor R.S (-A) := by
    change rationalizeWeilDivisor R.S (R.S.cartierToWeilHom _) = _
    rw [← R.S.regularCartierWeilEquiv_apply R.hreg, AddEquiv.apply_symm_apply]
  rw [h1, map_neg, hA, Nat.cast_smul_eq_nsmul]

/-- The rational Weil divisor `K_S + Σ_j λ_j G_j = −H₀`. -/
def DweilX (hc : Config R W B P) : R.S.RationalWeilDivisor :=
  R.S.rationalCartierToWeilHom R.KS + ∑ j, Finsupp.single (famG R B P j) (lamX R W B P hc j)

theorem rationalWeilNumericalMap_DweilX (hc : Config R W B P) :
    R.S.rationalWeilNumericalMap R.hreg (DweilX R W B P hc) = -(LnumX R W B P hc) := by
  unfold DweilX LnumX adjustedClass curveCombination
  rw [map_add, map_sum, R.rationalWeilNumericalMap_rationalCartier, neg_neg]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finsupp.smul_single_one, map_smul, R.rationalWeilNumericalMap_single]

theorem cartierClass_HmX (hc : Config R W B P) {n : ℕ} {Hm : CartierDivisor R.S.toScheme}
    (hHm : R.S.rationalCartierToWeilHom Hm = -((n : ℚ) • DweilX R W B P hc)) :
    NefNullCurveNegativeSquare.cartierClass R.S Hm = (n : ℚ) • LnumX R W B P hc := by
  rw [← R.rationalWeilNumericalMap_rationalCartier, hHm, map_neg, map_smul,
    rationalWeilNumericalMap_DweilX, smul_neg, neg_neg]

theorem intersectionNumber_HmX (hc : Config R W B P) {n : ℕ} {Hm : CartierDivisor R.S.toScheme}
    (hHm : R.S.rationalCartierToWeilHom Hm = -((n : ℚ) • DweilX R W B P hc)) (Q : R.S.PrimeCurve) :
    (Q.intersectionNumber Hm : ℚ) = (n : ℚ) * R.S.numericalRestrictionDegree Q (LnumX R W B P hc) := by
  rw [← numericalRestrictionDegree_cartierClass R.S R.hreg Q Hm, cartierClass_HmX R W B P hc hHm,
    map_smul, smul_eq_mul]

theorem intersectionPairing_HmX (hc : Config R W B P) {n : ℕ} {Hm : CartierDivisor R.S.toScheme}
    (hHm : R.S.rationalCartierToWeilHom Hm = -((n : ℚ) • DweilX R W B P hc)) :
    (R.S.intersectionPairing R.hreg Hm Hm : ℚ) = (n : ℚ) ^ 2 * LsqX R W B P hc := by
  rw [← NefNullCurveNegativeSquare.cartierClass_pairing R.S R.hreg Hm Hm,
    cartierClass_HmX R W B P hc hHm, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  unfold LsqX
  ring

/-! ### (ii) The retained family is an SNC forest -/

/-- The vertex map `(D − B) ⊕ {P} → D` sending `P` to `B` (a bijection). -/
def toVertices : D0 R B ⊕ Unit → R.Vertices := Sum.elim Subtype.val (fun _ => B)

theorem toVertices_injective : Function.Injective (toVertices R B) := by
  rintro (i | u) (j | w) h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact absurd h i.2
  · exact absurd h.symm j.2
  · cases u
    cases w
    rfl

/-- The incidence graph of `(D − B) ∪ {P}` is a forest (manuscript line 1187): `P` is a leaf
attached to the isolated vertex `W`, and the remaining edges are edges of the exceptional forest
`D`. -/
theorem famG_acyclic (hc : Config R W B P) : (curveIncidenceGraph (famG R B P)).IsAcyclic := by
  have hinj := famG_injective R B P hc.hP.2
  have hRac : R.graph.IsAcyclic :=
    (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.2.1
  refine isAcyclic_of_leaf (Sum.inr ()) (Sum.inl (Wd R W B P hc)) ?_
    (R.graph.comap (toVertices R B)) ?_ ?_
  · rintro (i | u) h
    · have h' := (curveIncidenceGraph_adj_iff_pairing_pos R.S R.hreg (famG R B P) hinj).mp h
      have hpos := h'.2
      simp only [famG_inl, famG_inr] at hpos
      have hr : (0 : ℚ) < rvec R B P i := by
        rw [← pairing_P_val R B P i]
        exact_mod_cast hpos
      rw [rvec_eq R W B P hc, Pi.single_apply] at hr
      by_cases hi : i = Wd R W B P hc
      · rw [hi]
      · rw [if_neg hi] at hr
        exact absurd hr (lt_irrefl 0)
    · cases u
      exact absurd h ((curveIncidenceGraph (famG R B P)).loopless _)
  · rintro (i | u) (j | w) h ha hb
    · have h' : Sum.inl i ≠ Sum.inl j ∧
          ((famG R B P (Sum.inl i) : Set R.S.toScheme) ∩ famG R B P (Sum.inl j)).Nonempty := h
      show R.graph.Adj i.1 j.1
      exact ⟨fun h'' => h'.1 (congrArg Sum.inl (Subtype.ext h'')), h'.2⟩
    · cases w
      exact absurd rfl hb
    · cases u
      exact absurd rfl ha
    · cases u
      exact absurd rfl ha
  · intro u c hcyc
    exact hRac _ (SimpleGraph.Walk.IsCycle.map
      (f := SimpleGraph.Hom.comap (toVertices R B) R.graph) (toVertices_injective R B) hcyc)

/-- Pairwise intersections of the retained family are at most one. -/
theorem pair_famG' (hc : Config R W B P) (a b : D0 R B ⊕ Unit) (hab : a ≠ b) :
    R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg (famG R B P a))
      (R.S.primeCurveCartier R.hreg (famG R B P b)) ≤ 1 := by
  have hforest := R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt
  rcases a with i | u <;> rcases b with j | w
  · exact hforest.2.2.2 i.1 j.1 (fun h => hab (congrArg Sum.inl (Subtype.ext h)))
  · have h := pairing_val_P R B P i
    have : (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg (famG R B P (Sum.inl i)))
        (R.S.primeCurveCartier R.hreg (famG R B P (Sum.inr w))) : ℚ) ≤ 1 := by
      simp only [famG_inl, famG_inr]
      rw [h]
      exact rvec_le_one R W B P hc i
    exact_mod_cast this
  · have h := pairing_P_val R B P j
    have : (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg (famG R B P (Sum.inr u)))
        (R.S.primeCurveCartier R.hreg (famG R B P (Sum.inl j))) : ℚ) ≤ 1 := by
      simp only [famG_inl, famG_inr]
      rw [h]
      exact rvec_le_one R W B P hc j
    exact_mod_cast this
  · exact absurd rfl hab

/-! ### (ii) The exchange contraction (Theorem 2.6) -/

/-- **Theorem 4.6, contraction clause** (manuscript lines 1171–1189), performed on `S`: the family
`(D − B) ∪ {P}` with coefficients `(θ − e_W, −2)` is contracted by a Cartier multiple of `H₀` to a
rank-one klt del Pezzo surface `X₀`, with all the conclusions of Theorem 2.6; in particular
`f^*K_{X₀} = K_S + Σ_{D−B} θ_i D_i − W − 2P`. -/
theorem anticanonicalContraction_exchange (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    ∃ (Y : NormalProjectiveSurface k) (f : R.S.toScheme ⟶ Y.toScheme)
      (hproper : IsProper f) (hbir : IsBirationalScheme f),
      f ≫ Y.structureMorphism = R.S.structureMorphism ∧ IsIso f.c ∧ IsBirational f ∧
      (∀ y : Y.toScheme, IsConnected (f.base ⁻¹' {y})) ∧
      (∀ Q : R.S.PrimeCurve, IsExceptionalCurve f Q ↔ ∃ j, Q = famG R B P j) ∧
      IsKltDelPezzo Y ∧ Y.picardRank = 1 ∧
      letI : IsProper f := hproper
      letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      let KY : Y.WeilDivisor :=
        BirationalWeilPushforward.pushforward f hbir (R.S.cartierToWeilHom R.KS)
      IsKltWithCanonicalDivisor Y KY ∧ Y.QAmple (-rationalizeWeilDivisor Y KY) ∧
      ∃ hK : Y.QCartier (rationalizeWeilDivisor Y KY),
        QCartierPullback.pullback f (rationalizeWeilDivisor Y KY) hK =
          R.S.rationalCartierToWeilHom R.KS +
            ∑ j, Finsupp.single (famG R B P j) (lamX R W B P hc j) := by
  obtain ⟨n, Hm, hn, hHm⟩ := exists_cartier_multiple' R (DweilX R W B P hc)
  have hinj := famG_injective R B P hc.hP.2
  have hrat : ∀ j, ∃ e : (famG R B P j).toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = (famG R B P j).toSpec := by
    rintro (i | u)
    · exact R.exceptional_rational i.1.1 i.1.2
    · exact hc.hP.1.isoProjectiveLine
  have hlam : ∀ j, lamX R W B P hc j < 1 := lamX_lt_one R W B P hc
  have hHm' : R.S.rationalCartierToWeilHom Hm = -((n : ℚ) • (R.S.rationalCartierToWeilHom R.KS +
      ∑ j, Finsupp.single (famG R B P j) (lamX R W B P hc j))) := hHm
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hnef : Positivity.IsNef R.S.structureMorphism
      (cartierDivisorInvertibleSheaf R.S.toScheme Hm) := by
    rw [Positivity.isNef_iff_forall_primeCurve]
    intro Q
    rw [← Q.intersectionNumber_eq_restrictionDegree]
    have h1 := intersectionNumber_HmX R W B P hc hHm Q
    have h2 := degree_LnumX_nonneg R W B P p hp hc Q
    have : (0 : ℚ) ≤ (Q.intersectionNumber Hm : ℚ) := by
      rw [h1]
      exact mul_nonneg hnpos.le h2
    exact_mod_cast this
  have hsq : 0 < R.S.intersectionPairing R.hreg Hm Hm := by
    have h1 := intersectionPairing_HmX R W B P hc hHm
    have h2 := LsqX_pos R W B P p hp hc
    have : (0 : ℚ) < (R.S.intersectionPairing R.hreg Hm Hm : ℚ) := by
      rw [h1]
      exact mul_pos (pow_pos hnpos 2) h2
    exact_mod_cast this
  have hnull : ∀ Q : R.S.PrimeCurve,
      Q.restrictionDegree (cartierDivisorInvertibleSheaf R.S.toScheme Hm) = 0 ↔
        ∃ j, Q = famG R B P j := by
    intro Q
    rw [← Q.intersectionNumber_eq_restrictionDegree,
      ← degree_LnumX_eq_zero_iff R W B P p hp hc Q]
    have h1 := intersectionNumber_HmX R W B P hc hHm Q
    constructor
    · intro h0
      have h2 : (n : ℚ) * R.S.numericalRestrictionDegree Q (LnumX R W B P hc) = 0 := by
        rw [← h1, h0, Int.cast_zero]
      exact (mul_eq_zero.mp h2).resolve_left hnpos.ne'
    · intro h0
      have h2 : (Q.intersectionNumber Hm : ℚ) = 0 := by
        rw [h1, h0, mul_zero]
      exact_mod_cast h2
  exact anticanonicalContraction p hp R.S R.hreg R.KS R.eKS (famG R B P) hinj hrat
    (famG_acyclic R W B P hc) (pair_famG' R W B P hc) (card_famG R B p hp) (lamX R W B P hc) hlam
    n hn Hm hHm' hnef hsq hnull

/-! ### (iii) The singular points of `X₀` -/

/-- `P` meets `D − B` exactly in `W`: the manuscript's `a = 1` contacted component. -/
theorem contactCount_eq_one (hc : Config R W B P) : contactCount R B P = 1 := by
  unfold contactCount
  have : (Finset.univ.filter (fun i : D0 R B => rvec R B P i ≠ 0)) = {Wd R W B P hc} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      rvec_eq R W B P hc, Pi.single_apply]
    by_cases h : i = Wd R W B P hc
    · simp [h]
    · simp [h]
  rw [this, Finset.card_singleton]

section Contraction

variable (hc : Config R W B P)
variable (Y : NormalProjectiveSurface k) (f : R.S.toScheme ⟶ Y.toScheme) [IsProper f]
  (hbir : IsBirationalScheme f) (hf : f ≫ Y.structureMorphism = R.S.structureMorphism)
  (hconn : ∀ y : Y.toScheme, IsConnected (f.base ⁻¹' {y}))
  (hexc : ∀ Q : R.S.PrimeCurve, IsExceptionalCurve f Q ↔ ∃ j, Q = famG R B P j)

include hbir hf hexc in
/-- The image of each retained component `D_i ⊂ D − W − B` is a singular point of `X₀`: its
discrepancy coefficient is `−θ_i ≤ 0` (manuscript lines 1190–1192). -/
theorem image_val_mem_singularPoints'
    (hK : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      Y.QCartier (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (R.S.cartierToWeilHom R.KS))))
    (hpull : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      QCartierPullback.pullback f (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (R.S.cartierToWeilHom R.KS))) hK =
        R.S.rationalCartierToWeilHom R.KS + ∑ j, Finsupp.single (famG R B P j) (lamX R W B P hc j))
    (i : D0 R B) (hi : i ≠ Wd R W B P hc) : f.base i.1.1.genericPoint ∈ Y.singularPoints := by
  letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
  have hexci : IsExceptionalCurve f i.1.1 := exceptional_famG R B P Y f hexc (Sum.inl i)
  have hmem : f.base i.1.1.genericPoint ∈ ActualExceptionalLocus.imagePoints f :=
    ⟨_, (ActualExceptionalLocus.mem_primeSupport f _).mpr ⟨i.1.1, hexci, i.1.1.genericPoint_mem⟩, rfl⟩
  have hclosed : IsClosed ({f.base i.1.1.genericPoint} : Set Y.toScheme) :=
    ActualExceptionalLocus.imagePoint_isClosed f ⟨_, hmem⟩
  have hKYcan := isCanonicalWeilDivisor_pushforward_of_cartier R.S Y f hf hbir R.KS R.eKS
  rw [Y.mem_singularPoints]
  intro hreg
  have hpos := RegularTargetCanonicalDiscrepancy.coefficient_pos_of_regular_closed_image R.S Y f
    hbir hf R.KS R.eKS _ hKYcan hK rfl i.1.1 hclosed hreg
  rw [hpull] at hpos
  have hval : (∑ j, Finsupp.single (famG R B P j) (lamX R W B P hc j)) i.1.1 =
      lamX0 R W B P hc i := by
    have h := sum_single_apply_eq (famG R B P) (famG_injective R B P hc.hP.2) (lamX R W B P hc)
      (Sum.inl i)
    simpa using h
  simp only [Finsupp.sub_apply, Finsupp.add_apply, hval] at hpos
  linarith [lamX0_nonneg_of_ne R W B P hc i hi]

include hc hexc in
/-- `f(W) = f(P)`: the two contracted curves meet. -/
theorem image_W_eq_image_P : f.base W.1.genericPoint = f.base P.genericPoint := by
  have hPexc : IsExceptionalCurve f P := exceptional_famG R B P Y f hexc (Sum.inr ())
  have hWexc : IsExceptionalCurve f W.1 := exceptional_famG R B P Y f hexc (Sum.inl (Wd R W B P hc))
  have hne : P ≠ W.1 := fun h => hc.hP.2 (by rw [h]; exact W.2)
  have hpair : (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg P)
      (R.S.primeCurveCartier R.hreg W.1) : ℚ) = 1 := by
    have h := pairing_P_val R B P (Wd R W B P hc)
    rw [rvec_eq R W B P hc, Pi.single_eq_same] at h
    exact h
  have hint : ((P : Set R.S.toScheme) ∩ W.1).Nonempty := by
    rw [← Set.not_disjoint_iff_nonempty_inter]
    intro hd
    have h0 := (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
      R.S R.hreg P W.1 hne).mpr hd
    rw [h0] at hpair
    norm_num at hpair
  obtain ⟨x, hxP, hxW⟩ := hint
  rw [← image_eq_of_exceptional hPexc hxP, image_eq_of_exceptional hWexc hxW]

include hc hbir hf hconn hexc in
/-- The component bookkeeping of manuscript lines 1191–1193: the exceptional locus of `f` has
`#π₀(D) + d − 1` connected components, hence that many image points (`d` the valency of `B`). -/
theorem imagePoints_ncard_add_one [DecidableRel R.graph.Adj] :
    (ActualExceptionalLocus.imagePoints f).ncard + 1 =
      R.X.singularPoints.card + R.graph.degree B := by
  have hnX : R.X.singularPoints.card = Nat.card R.graph.ConnectedComponent :=
    (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.1
  have hcomp := card_components_famG R B P hc.hP.2 (famG_acyclic R W B P hc)
  rw [contactCount_eq_one R W B P hc] at hcomp
  have himg := ncard_imagePoints R B P Y f hbir hf hconn hexc hc.hP.2
  omega

include hbir hf hconn hexc in
/-- **Theorem 4.6, singular-point count** (manuscript eq:isolated-mixed-nonterminal-gain, lines
1190–1193), two-sided: `#Sing(X) + d − 2 ≤ #Sing(X₀) ≤ #Sing(X) + d − 1`. The lower bound comes
from the singular images of `D − W − B`; the upper bound from `Sing(X₀) ⊆ f(D − B) ∪ {f(P)}` with
`f(W) = f(P)`. -/
theorem singularPoints_card_bounds [DecidableRel R.graph.Adj] [IsIso f.c]
    (hK : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      Y.QCartier (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (R.S.cartierToWeilHom R.KS))))
    (hpull : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      QCartierPullback.pullback f (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (R.S.cartierToWeilHom R.KS))) hK =
        R.S.rationalCartierToWeilHom R.KS + ∑ j, Finsupp.single (famG R B P j) (lamX R W B P hc j)) :
    R.X.singularPoints.card + R.graph.degree B ≤ Y.singularPoints.card + 2 ∧
      Y.singularPoints.card + 1 ≤ R.X.singularPoints.card + R.graph.degree B := by
  have hcount := imagePoints_ncard_add_one R W B P hc Y f hbir hf hconn hexc
  have hsub1 := singularPoints_subset_imagePoints R Y f hbir hf hconn
  have hset := imagePoints_eq R B P Y f hexc
  have hfin := ActualExceptionalLocus.imagePoints_finite f hbir
  have hyP_mem : f.base P.genericPoint ∈ ActualExceptionalLocus.imagePoints f := by
    rw [hset]
    exact Or.inr rfl
  have hWP := image_W_eq_image_P R W B P hc Y f hexc
  have hsub : ActualExceptionalLocus.imagePoints f \ {f.base P.genericPoint} ⊆
      (Y.singularPoints : Set Y.Point) := by
    rintro y ⟨hy, hne⟩
    rw [hset] at hy
    rcases hy with ⟨i, rfl⟩ | hy
    · by_cases hi : i = Wd R W B P hc
      · exfalso
        apply hne
        rw [Set.mem_singleton_iff, hi]
        exact hWP
      · exact image_val_mem_singularPoints' R W B P hc Y f hbir hf hexc hK hpull i hi
    · exact absurd hy hne
  have h1 : (ActualExceptionalLocus.imagePoints f \ {f.base P.genericPoint}).ncard ≤
      Y.singularPoints.card := by
    rw [← Set.ncard_coe_Finset]
    exact Set.ncard_le_ncard hsub (Y.singularPoints.finite_toSet)
  rw [Set.ncard_diff_singleton_of_mem hyP_mem hfin] at h1
  have h2 : Y.singularPoints.card ≤ (ActualExceptionalLocus.imagePoints f).ncard := by
    rw [← Set.ncard_coe_Finset]
    exact Set.ncard_le_ncard hsub1 hfin
  omega

include hbir hf hconn hexc in
/-- The exact count `#Sing(X₀) − #Sing(X) = d − 2` of eq:isolated-mixed-nonterminal-gain, under
the explicit hypothesis that the common image `f(W) = f(P)` of the two contracted curves is a
regular point of `X₀` (the manuscript's `T` is smooth and `S → X₀` factors through `T → X₀`,
which is an isomorphism near that point, lines 1176–1182). -/
theorem singularPoints_card_eq_of_regular [DecidableRel R.graph.Adj] [IsIso f.c]
    (hK : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      Y.QCartier (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (R.S.cartierToWeilHom R.KS))))
    (hpull : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      QCartierPullback.pullback f (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (R.S.cartierToWeilHom R.KS))) hK =
        R.S.rationalCartierToWeilHom R.KS + ∑ j, Finsupp.single (famG R B P j) (lamX R W B P hc j))
    (hreg : RegularPoint Y.toScheme (f.base P.genericPoint)) :
    Y.singularPoints.card + 2 = R.X.singularPoints.card + R.graph.degree B := by
  obtain ⟨hlow, -⟩ := singularPoints_card_bounds R W B P hc Y f hbir hf hconn hexc hK hpull
  have hcount := imagePoints_ncard_add_one R W B P hc Y f hbir hf hconn hexc
  have hsub1 := singularPoints_subset_imagePoints R Y f hbir hf hconn
  have hfin := ActualExceptionalLocus.imagePoints_finite f hbir
  have hset := imagePoints_eq R B P Y f hexc
  have hyP_mem : f.base P.genericPoint ∈ ActualExceptionalLocus.imagePoints f := by
    rw [hset]
    exact Or.inr rfl
  have hnot : f.base P.genericPoint ∉ Y.singularPoints := by
    rw [Y.mem_singularPoints]
    exact not_not.mpr hreg
  have hsub : (Y.singularPoints : Set Y.Point) ⊆
      ActualExceptionalLocus.imagePoints f \ {f.base P.genericPoint} := by
    intro y hy
    refine ⟨hsub1 hy, ?_⟩
    rw [Set.mem_singleton_iff]
    rintro rfl
    exact hnot hy
  have h2 : Y.singularPoints.card ≤
      (ActualExceptionalLocus.imagePoints f \ {f.base P.genericPoint}).ncard := by
    rw [← Set.ncard_coe_Finset]
    exact Set.ncard_le_ncard hsub hfin.diff
  rw [Set.ncard_diff_singleton_of_mem hyP_mem hfin] at h2
  have hpos : 0 < (ActualExceptionalLocus.imagePoints f).ncard :=
    (Set.ncard_pos hfin).mpr ⟨_, hyP_mem⟩
  omega

end Contraction

/-! ### The exchange datum -/

/-- **Theorem 4.6, datum form.** For the configuration `Config` (an isolated `(-2)`-curve `W`, an
exterior `(-1)`-curve `P` meeting `W` and a higher-weight vertex `B` once each and nothing else),
the rank-one klt del Pezzo surface `X₀` obtained by contracting `(D − B) ∪ {P}` carries a resolution
datum `R₁` with `ρ(R₁.S) < ρ(R.S)` and `#Sing(X) + d − 2 ≤ #Sing(X₀) ≤ #Sing(X) + d − 1`, `d` the
valency of `B`. -/
theorem isolatedNodeExchange_datum' [DecidableRel R.graph.Adj] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hc : Config R W B P) :
    ∃ R₁ : ResolutionDatum k, R₁.S.picardRank < R.S.picardRank ∧
      R.X.singularPoints.card + R.graph.degree B ≤ R₁.X.singularPoints.card + 2 ∧
      R₁.X.singularPoints.card + 1 ≤ R.X.singularPoints.card + R.graph.degree B := by
  obtain ⟨Y, f, hproper, hbir, hf, hcY, hbirational, hconn, hexc, hDP, hrankY, hrest⟩ :=
    anticanonicalContraction_exchange R W B P p hp hc
  letI : IsProper f := hproper
  letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
  letI : IsIso f.c := hcY
  obtain ⟨hKY, -, hK, hpull⟩ := hrest
  have hres : IsResolution R.S Y f := ⟨hf, R.hreg, hbirational⟩
  have hPexc : IsExceptionalCurve f P := (hexc P).mpr ⟨Sum.inr (), rfl⟩
  obtain ⟨T, g, hmin, hlt⟩ := exists_minimalResolution_ncard_lt hres P hPexc hc.hP.1
  let R₁ : ResolutionDatum k := ⟨T, Y, g, hmin, hDP, hrankY⟩
  refine ⟨R₁, ?_, ?_⟩
  · show T.picardRank < R.S.picardRank
    have h1 : T.picardRank = 1 + Nat.card (ActualExceptionalIncidence.Vertices g) := by
      have := hmin.picardRank_eq_of_klt ⟨_, hKY⟩ p hp
      rw [hrankY] at this
      exact this
    have h2 : Nat.card (ActualExceptionalIncidence.Vertices g) =
        {Q : T.PrimeCurve | IsExceptionalCurve g Q}.ncard := Set.Nat.card_coe_set_eq _
    have h3 : {Q : R.S.PrimeCurve | IsExceptionalCurve f Q}.ncard =
        Fintype.card (D0 R B ⊕ Unit) := by
      rw [← Set.Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
      have hinj := famG_injective R B P hc.hP.2
      let eV : D0 R B ⊕ Unit ≃ {Q : R.S.PrimeCurve | IsExceptionalCurve f Q} :=
        Equiv.ofBijective (fun j => ⟨famG R B P j, (hexc _).mpr ⟨j, rfl⟩⟩)
          ⟨fun a b h => hinj (congrArg Subtype.val h),
           fun v => by
            obtain ⟨j, hj⟩ := (hexc v.1).mp v.2
            exact ⟨j, Subtype.ext hj.symm⟩⟩
      exact Nat.card_congr eV.symm
    have h4 := card_famG R B p hp
    omega
  · show R.X.singularPoints.card + R.graph.degree B ≤ Y.singularPoints.card + 2 ∧
      Y.singularPoints.card + 1 ≤ R.X.singularPoints.card + R.graph.degree B
    exact singularPoints_card_bounds R W B P hc Y f hbir hf hconn hexc hK hpull


/-! ### (iv) The terminal case `d = 1`: the scalar content (manuscript lines 1194–1219)

For `d = 1` the manuscript blows up the point `B_T ∩ C_T` of `T` and contracts the strict
transform of `B_T` (an isolated `(-2)`-curve) together with the transformed `D − W − B`; the
retained matrix is `A₀ + a aᵀ` (`a = e_C`) with canonical degrees `q₀ + a`, and the new discrepancy
vector is `λ₀† = λ₀ + ε u`, `ε = (1 − s)/(1 + t) = (2h − η)/(4h − 1)`
(eq:isolated-mixed-new-discrepancy). The scalar identities and bounds are proved here on the data
of `S`; the point blowup itself is not constructed (see the module docstring). -/

/-- `ε = (1 − s)/(1 + t)`. -/
def epsT : ℚ := (1 - vvec R B ⬝ᵥ theta R B) / (1 + vvec R B ⬝ᵥ wv R B)

/-- `1 + t = (4h − 1)/h > 0`. -/
theorem one_add_t_eq (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    1 + vvec R B ⬝ᵥ wv R B = (4 * gC R B - 1) / gC R B := by
  rw [t_eq R W B P p hp hc]
  have hg := (gC_pos R B).ne'
  field_simp
  ring

theorem one_add_t_pos (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    0 < 1 + vvec R B ⬝ᵥ wv R B := by
  rw [one_add_t_eq R W B P p hp hc]
  have hg := half_lt_gC R W B P p hp hc
  apply div_pos <;> linarith

/-- eq:isolated-mixed-new-discrepancy: `ε = (2h − η)/(4h − 1)`. -/
theorem terminal_epsilon_eq (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    epsT R B = (2 * gC R B - muC R B) / (4 * gC R B - 1) := by
  unfold epsT
  rw [one_add_t_eq R W B P p hp hc]
  have hs : 1 - vvec R B ⬝ᵥ theta R B = (2 * gC R B - muC R B) / gC R B := by
    have hmu := muC_eq_gC_mul_one_add R W B P p hp hc
    have hg := (gC_pos R B).ne'
    field_simp
    linarith
  rw [hs]
  have hg := (gC_pos R B).ne'
  have h4 : 4 * gC R B - 1 ≠ 0 := by
    have := half_lt_gC R W B P p hp hc
    intro h
    linarith
  field_simp

/-- `0 < ε` (manuscript line 1208). -/
theorem terminal_epsilon_pos (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    0 < epsT R B := by
  rw [terminal_epsilon_eq R W B P p hp hc]
  exact KltDP.LinearAlgebra.isolated_exchange_increment_pos (half_lt_gC R W B P p hp hc)
    (muC_lt_one R B)

/-- `ε < η` (manuscript lines 1208–1209). -/
theorem terminal_epsilon_lt_muC (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    epsT R B < muC R B := by
  rw [terminal_epsilon_eq R W B P p hp hc]
  exact KltDP.LinearAlgebra.isolated_exchange_increment_lt (half_lt_gC R W B P p hp hc)
    (gC_le_muC R W B P p hp hc)

/-- The new discrepancy vector `λ₀† = λ₀ + ε u` on `D − B`. -/
def lamT : D0 R B → ℚ := theta R B + epsT R B • wv R B

/-- eq:isolated-mixed-new-discrepancy: `(A₀ + a aᵀ)(λ₀ + ε u) = q₀ + a`. -/
theorem terminal_rankOne_identity (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    (Mblock R B + vecMulVec (vvec R B) (vvec R B)) *ᵥ lamT R B = q0 R B + vvec R B := by
  have ht := one_add_t_pos R W B P p hp hc
  have hε : epsT R B * (1 + vvec R B ⬝ᵥ wv R B) = 1 - vvec R B ⬝ᵥ theta R B := by
    unfold epsT
    exact div_mul_cancel₀ _ ht.ne'
  funext i
  have hM : (Mblock R B *ᵥ lamT R B) i = q0 R B i + epsT R B * vvec R B i := by
    unfold lamT
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Mblock_mulVec_theta, Mblock_mulVec_wv]
    simp
  have hr : (vecMulVec (vvec R B) (vvec R B) *ᵥ lamT R B) i =
      vvec R B i * (vvec R B ⬝ᵥ lamT R B) := by
    simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]
  have hdot : vvec R B ⬝ᵥ lamT R B =
      vvec R B ⬝ᵥ theta R B + epsT R B * (vvec R B ⬝ᵥ wv R B) := by
    unfold lamT
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [Matrix.add_mulVec, Pi.add_apply, hM, hr, hdot, Pi.add_apply]
  linear_combination (vvec R B i) * hε

/-- `0 ≤ λ₀†`. -/
theorem lamT_nonneg (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) (i : D0 R B) :
    0 ≤ lamT R B i := by
  unfold lamT
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := mul_nonneg (terminal_epsilon_pos R W B P p hp hc).le (wv_nonneg R B i)
  linarith [theta_nonneg R B i]

/-- `λ₀† ≤ λ₀` (comparison with `λ₀ = θ + η u`, manuscript line 1210). -/
theorem lamT_le_lam0 (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) (i : D0 R B) :
    lamT R B i ≤ lam0 R B i := by
  unfold lamT
  rw [lam0_eq R B]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := mul_le_mul_of_nonneg_right (terminal_epsilon_lt_muC R W B P p hp hc).le (wv_nonneg R B i)
  linarith

/-- `λ₀† < 1`. -/
theorem lamT_lt_one (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) (i : D0 R B) :
    lamT R B i < 1 :=
  lt_of_le_of_lt (lamT_le_lam0 R W B P p hp hc i) (lam0_lt_one R B i)

/-- The square change `1 + 2s + t − (s + t)²/(1 + t) − η²/h` of manuscript line 1214 equals
`2(2η(1 − η) + 2h − 1)/(4h − 1)` (eq:isolated-mixed-terminal-gain). -/
theorem terminal_square_change_eq (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    1 + 2 * (vvec R B ⬝ᵥ theta R B) + vvec R B ⬝ᵥ wv R B -
        (vvec R B ⬝ᵥ theta R B + vvec R B ⬝ᵥ wv R B) ^ 2 / (1 + vvec R B ⬝ᵥ wv R B) -
        muC R B ^ 2 / gC R B =
      2 * (2 * muC R B * (1 - muC R B) + 2 * gC R B - 1) / (4 * gC R B - 1) := by
  have hg := (gC_pos R B).ne'
  have h4 : 4 * gC R B - 1 ≠ 0 := by
    have := half_lt_gC R W B P p hp hc
    intro h
    linarith
  have hs : vvec R B ⬝ᵥ theta R B = muC R B / gC R B - 1 := by
    have hmu := muC_eq_gC_mul_one_add R W B P p hp hc
    field_simp
    linarith
  rw [hs, t_eq R W B P p hp hc]
  have h1 : 1 + (3 - 1 / gC R B) = (4 * gC R B - 1) / gC R B := by
    field_simp
    ring
  rw [h1]
  field_simp
  ring

/-- eq:isolated-mixed-terminal-gain is positive. -/
theorem terminal_gain_pos (p : ℕ) [CharP k p] (hp : 0 < p) (hc : Config R W B P) :
    0 < 2 * (2 * muC R B * (1 - muC R B) + 2 * gC R B - 1) / (4 * gC R B - 1) :=
  KltDP.LinearAlgebra.isolated_exchange_terminal_gain_pos (half_lt_gC R W B P p hp hc)
    (gC_le_muC R W B P p hp hc) (muC_lt_one R B)

end IsolatedNodeExchange

/-! ### The interface for Theorem 7.1 -/

open IsolatedNodeExchange

/-- Manuscript Theorem 4.6 (`thm:isolated-node-exchange`, lines 1114–1136), datum form with the
valency `d` of `B` explicit: for an exterior `(-1)`-curve `P`, an isolated exceptional `(-2)`-curve
`W` and an exceptional curve `B` of weight `≥ 3` such that `P` meets `W` and `B` once each and
nothing else (`W ≠ B` follows from the weights), there is a resolution datum `R₁` with
`ρ(R₁.S) < ρ(R.S)` and `#Sing(X) + d − 2 ≤ #Sing(R₁.X) ≤ #Sing(X) + d − 1`. -/
theorem isolatedNodeExchange_datum {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)
    [DecidableEq R.Vertices] [DecidableRel R.graph.Adj] (p : ℕ) [CharP k p] (hp : 0 < p)
    (W B : R.Vertices) (P : R.S.PrimeCurve)
    (hP : R.IsExteriorMinusOne P) (hW2 : R.w W = 2) (hWiso : ∀ y : R.Vertices, ¬ R.graph.Adj W y)
    (hB3 : 3 ≤ R.w B) (hPW : R.contact P W = 1) (hPB : R.contact P B = 1)
    (hP0 : ∀ i : R.Vertices, i ≠ W → i ≠ B → R.contact P i = 0) :
    ∃ R₁ : ResolutionDatum k, R₁.S.picardRank < R.S.picardRank ∧
      R.X.singularPoints.card + R.graph.degree B ≤ R₁.X.singularPoints.card + 2 ∧
      R₁.X.singularPoints.card + 1 ≤ R.X.singularPoints.card + R.graph.degree B := by
  have hWB : W ≠ B := by
    intro h
    rw [h] at hW2
    linarith
  exact isolatedNodeExchange_datum' R W B P p hp ⟨hP, hW2, hWiso, hWB, hPW, hPB, hP0, hB3⟩

/-- `IsolatedExchangeHyp` restricted to vertices `B` of valency at least two (the nonterminal
case of Theorem 4.6, manuscript lines 1137–1140). -/
def IsolatedExchangeHypOfDegreeGeTwo {k : Type u} [Field k] [IsAlgClosed k]
    (R : ResolutionDatum k) [DecidableRel R.graph.Adj] : Prop :=
  ∀ (W B : R.Vertices) (P : R.S.PrimeCurve), R.IsExteriorMinusOne P →
    R.w W = 2 → (∀ y, ¬ R.graph.Adj W y) → 3 ≤ R.w B →
    R.contact P W = 1 → R.contact P B = 1 → (∀ i, i ≠ W → i ≠ B → R.contact P i = 0) →
    2 ≤ R.graph.degree B →
    ∃ R₁ : ResolutionDatum k, R₁.S.picardRank < R.S.picardRank ∧
      R.X.singularPoints.card ≤ R₁.X.singularPoints.card

/-- **The terminal case `d = 1` of Theorem 4.6, isolated** (manuscript lines 1141–1145 and
1194–1219): blow up the point `B_T ∩ C_T` of `T`, retain the strict transform of `B_T` as an
isolated `A₁` and the transformed `D − W − B`, omit the new `(-1)`-curve, and contract to `X₁`
with unchanged singular-point count and Picard decrease one. The geometric construction (a point
blowup of the surface `T`) is not available in the compiled union; the scalar content is proved
in `IsolatedNodeExchange.terminal_*`. -/
def IsolatedExchangeTerminalHyp {k : Type u} [Field k] [IsAlgClosed k]
    (R : ResolutionDatum k) [DecidableRel R.graph.Adj] : Prop :=
  ∀ (W B : R.Vertices) (P : R.S.PrimeCurve), R.IsExteriorMinusOne P →
    R.w W = 2 → (∀ y, ¬ R.graph.Adj W y) → 3 ≤ R.w B →
    R.contact P W = 1 → R.contact P B = 1 → (∀ i, i ≠ W → i ≠ B → R.contact P i = 0) →
    R.graph.degree B = 1 →
    ∃ R₁ : ResolutionDatum k, R₁.S.picardRank < R.S.picardRank ∧
      R.X.singularPoints.card ≤ R₁.X.singularPoints.card

/-- **Theorem 4.6 for `d ≥ 2`, in the interface form of Theorem 7.1.** -/
theorem isolatedExchangeHyp_of_degree_ge_two {k : Type u} [Field k] [IsAlgClosed k]
    (R : ResolutionDatum k) [DecidableRel R.graph.Adj] (p : ℕ) [CharP k p] (hp : 0 < p) :
    IsolatedExchangeHypOfDegreeGeTwo R := by
  classical
  intro W B P hP hW2 hWiso hB3 hPW hPB hP0 hd
  obtain ⟨R₁, h1, h2, -⟩ := isolatedNodeExchange_datum R p hp W B P hP hW2 hWiso hB3 hPW hPB hP0
  exact ⟨R₁, h1, by omega⟩

/-- **Theorem 4.6 in the interface form of Theorem 7.1**, given the terminal case `d = 1`: the
valency of `B` is positive (`one_le_degree`), so either `d = 1` (the isolated terminal statement)
or `d ≥ 2` (`isolatedExchangeHyp_of_degree_ge_two`). -/
theorem isolatedExchangeHyp_of_terminal {k : Type u} [Field k] [IsAlgClosed k]
    (R : ResolutionDatum k) [DecidableRel R.graph.Adj] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hterm : IsolatedExchangeTerminalHyp R) : IsolatedExchangeHyp R := by
  classical
  intro W B P hP hW2 hWiso hB3 hPW hPB hP0
  have hWB : W ≠ B := by
    intro h
    rw [h] at hW2
    linarith
  have hc : Config R W B P := ⟨hP, hW2, hWiso, hWB, hPW, hPB, hP0, hB3⟩
  have hd := one_le_degree R W B P p hp hc
  by_cases hd1 : R.graph.degree B = 1
  · exact hterm W B P hP hW2 hWiso hB3 hPW hPB hP0 hd1
  · exact isolatedExchangeHyp_of_degree_ge_two R p hp W B P hP hW2 hWiso hB3 hPW hPB hP0
      (by omega)

end KltDP.Manuscript.S04

#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.energy
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.w_B_eq_three
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.one_le_degree
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.negIntersectionMatrix_famG_mulVec_lamX
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.LsqX_sub_Lsq
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.degree_B
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.famG_acyclic
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.anticanonicalContraction_exchange
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.singularPoints_card_bounds
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.singularPoints_card_eq_of_regular
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.isolatedNodeExchange_datum'
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.terminal_rankOne_identity
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.terminal_square_change_eq
#print axioms KltDP.Manuscript.S04.isolatedNodeExchange_datum
#print axioms KltDP.Manuscript.S04.isolatedExchangeHyp_of_degree_ge_two
#print axioms KltDP.Manuscript.S04.isolatedExchangeHyp_of_terminal
