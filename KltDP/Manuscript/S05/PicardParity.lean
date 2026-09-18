import KltDP.Manuscript.S05.PicardIndex
import KltDP.Support.PicardParity

/-!
# Section 5.3 of the manuscript: Riemann–Roch parity and the full Picard index

Manuscript `source/manuscript.tex`, Lemma 5.3 (`lem:picard-parity`, lines 1393–1433), on the
resolution datum `R` with an exterior `(−1)`-curve `P` and a finset `N` of `t` isolated
exceptional nodes disjoint from `P`. With `Γ = ⟨D, P⟩`, `I = [Pic S : Γ]` and `s = v₂(I)`:

* `picardIndexParity_code`: the binary code `𝒦 = integralNodeCode (nodeFamily R N) ⊆ 𝔽₂^t` of
  words `ε` with `½ Σ ε_i [W_i] ∈ Pic S` has dimension `≥ t − s` and is doubly even (every word
  has Hamming weight divisible by four), in every positive characteristic.
* `picardIndexParity_word`: for every word `ε ∈ 𝒦` the half-sum `M_ε` satisfies
  `K_S · M_ε = 0` and `M_ε² = −½ wt(ε)`.
* `picardIndexParity_36`: the index data `(I, t) = (36, 3)` and `(36, 4)` are impossible.
* `picardIndexParity_24`: `(I, t) = (24, 4)` forces `W₁ + W₂ + W₃ + W₄ = 2M` with `M² = −2` and
  `K_S · M = 0`.
* `picardIndexParity_24_impossible`: in characteristic `p > 2` the last case is excluded by
  Theorem 5.1 (`isolated_nodes_no_half_sum`).
* `picardIndexParity`: the bundled statement.

The lattice-theoretic content is the union's `TenRowPicardExclusions` / `IntegralNodeObstruction`;
this file supplies the geometric instantiation (basis, characteristic class, node rows).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Codes KltDP.LinearAlgebra KltDP.Lattices.SmallADEForestLattice
open KltDP.Lattices.TenRowPicardExclusions KltDP.Lattices.IntegralNodeObstruction
open scoped BigOperators

universe u

namespace KltDP.Manuscript.S05

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-- The node classes `[W_i] ∈ Pic S`, indexed by the finset `N` of isolated nodes. -/
def nodeFamily (N : Finset R.Vertices) : {W : R.Vertices // W ∈ N} → Additive R.S.toScheme.Pic :=
  fun i => cls R i.val

/-- The embedding of the node index type into the vertex type. -/
def nodeEmb (N : Finset R.Vertices) : {W : R.Vertices // W ∈ N} ↪ R.Vertices :=
  ⟨Subtype.val, Subtype.val_injective⟩

section NodeRows

variable [DecidableEq R.Vertices] [DecidableRel R.graph.Adj]
  (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) (N : Finset R.Vertices)
  (hw : ∀ W ∈ N, R.w W = 2) (hiso : ∀ W ∈ N, ∀ y, ¬ R.graph.Adj W y)
  (hPN : ∀ W ∈ N, P.intersectionNumber (R.S.primeCurveCartier R.hreg W.val) = 0)

include hP hw hiso hPN

/-- The Gram row of an isolated node disjoint from `P` against the family `(D_i, P)`:
`W · W = −2` and `W · D_j = W · P = 0` otherwise. -/
theorem node_rows (W : R.Vertices) (hW : W ∈ N) :
    ∀ j : R.Vertices ⊕ Unit,
      R.S.integralPicardIntersectionBilinForm R.hreg (cls R W)
        (Sum.elim (cls R) (fun _ : Unit => primeClass R P) j) =
        if Sum.inl W = j then -2 else 0 :=
  isolated_graph_node_rows (R.S.integralPicardIntersectionBilinForm R.hreg) (cls R)
    (primeClass R P) R.graph R.w (contact R P) (familyGram_eq_borderedGram_graph R P hP) W
    (hiso W hW) (hw W hW) (contact_eq_zero R P W (hPN W hW))

theorem nodeFamily_sq (i : {W : R.Vertices // W ∈ N}) :
    R.S.integralPicardIntersectionBilinForm R.hreg (nodeFamily R N i) (nodeFamily R N i) = -2 := by
  have h := node_rows R P hP N hw hiso hPN i.val i.property (Sum.inl i.val)
  simpa [nodeFamily] using h

theorem nodeFamily_orth (i j : {W : R.Vertices // W ∈ N}) (hij : i ≠ j) :
    R.S.integralPicardIntersectionBilinForm R.hreg (nodeFamily R N i) (nodeFamily R N j) = 0 := by
  have h := node_rows R P hP N hw hiso hPN i.val i.property (Sum.inl j.val)
  rw [if_neg (fun h' => hij (Subtype.ext (Sum.inl.inj h')))] at h
  simpa [nodeFamily] using h

/-- Even pairings of the node classes with the whole lattice `Γ = ⟨D, P⟩`. -/
theorem nodeFamily_even_on_span (i : {W : R.Vertices // W ∈ N}) (y : Additive R.S.toScheme.Pic)
    (hy : y ∈ R.S.exceptionalExteriorPicardSpan R.π R.hreg P) :
    Even (R.S.integralPicardIntersectionBilinForm R.hreg (nodeFamily R N i) y) := by
  rw [← span_range_family R P] at hy
  let nodes : {W : R.Vertices // W ∈ N} ↪ (R.Vertices ⊕ Unit) :=
    ⟨fun i => Sum.inl i.val, fun i j h => Subtype.ext (Sum.inl.inj h)⟩
  exact node_rows_even_on_span (R.S.integralPicardIntersectionBilinForm R.hreg)
    (Sum.elim (cls R) (fun _ : Unit => primeClass R P)) nodes
    (fun i j => node_rows R P hP N hw hiso hPN i.val i.property j) i y hy

omit [DecidableEq R.Vertices] [DecidableRel R.graph.Adj] hP hiso hPN in
/-- Adjunction: `K_S · W = 0` for a weight-two exceptional curve. -/
theorem nodeFamily_K (i : {W : R.Vertices // W ∈ N}) :
    R.S.integralPicardIntersectionBilinForm R.hreg (Kcls R) (nodeFamily R N i) = 0 := by
  have h := pairing_Kcls_cls R i.val
  rw [hw i.val i.property] at h
  have h2 : (R.S.integralPicardIntersectionBilinForm R.hreg (Kcls R) (cls R i.val) : ℚ) = 0 := by
    rw [h]
    norm_num
  show R.S.integralPicardIntersectionBilinForm R.hreg (Kcls R) (cls R i.val) = 0
  exact_mod_cast h2

/-- **5.3, the code**: the binary code of integral node half-sums has dimension at least
`t − v₂(I)` and is doubly even (Riemann–Roch parity), in every positive characteristic. -/
theorem picardIndexParity_code (p : ℕ) [CharP k p] (hp : 0 < p)
    (hPext : ¬ IsExceptionalCurve R.π P) :
    DoublyEvenCode (integralNodeCode (nodeFamily R N)) ∧
      N.card - (R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index.factorization 2
        ≤ Module.finrank (ZMod 2) (integralNodeCode (nodeFamily R N)) := by
  haveI : NeZero p := ⟨by omega⟩
  haveI := finiteIndex_exceptionalExteriorPicardSpan R p P hPext
  obtain ⟨b, hb⟩ := exists_basis_unimodular R p hp
  have h := integralNodeCode_doublyEven_and_finrank_ge b _ hb
    (R.S.exceptionalExteriorPicardSpan R.π R.hreg P) (nodeFamily R N)
    (nodeFamily_even_on_span R P hP N hw hiso hPN) (Kcls R) (Kcls_isCharacteristic R)
    (nodeFamily_sq R P hP N hw hiso hPN) (nodeFamily_orth R P hP N hw hiso hPN)
    (nodeFamily_K R N hw)
  rwa [Fintype.card_coe] at h

omit [DecidableEq R.Vertices] [DecidableRel R.graph.Adj] hP hiso hPN in
/-- **5.3, the words**: every word `ε` of the code has an integral half-sum
`M_ε = ½ Σ ε_i [W_i]` with `K_S · M_ε = 0`, `M_ε² = −½ wt(ε)`, and `4 ∣ wt(ε)`. -/
theorem picardIndexParity_word (x : BinaryWord {W : R.Vertices // W ∈ N})
    (hx : x ∈ integralNodeCode (nodeFamily R N))
    (horth : ∀ i j, i ≠ j →
      R.S.integralPicardIntersectionBilinForm R.hreg (nodeFamily R N i) (nodeFamily R N j) = 0) :
    ∃ m : Additive R.S.toScheme.Pic,
      (2 : ℤ) • m = ∑ i ∈ Finset.univ.filter (fun j => x j ≠ 0), nodeFamily R N i ∧
      R.S.integralPicardIntersectionBilinForm R.hreg (Kcls R) m = 0 ∧
      2 * R.S.integralPicardIntersectionBilinForm R.hreg m m = -(hammingNorm x : ℤ) ∧
      4 ∣ hammingNorm x := by
  obtain ⟨m, hm⟩ := (mem_integralNodeCode_iff (nodeFamily R N) x).mp hx
  have hsq : ∀ i, R.S.integralPicardIntersectionBilinForm R.hreg (nodeFamily R N i)
      (nodeFamily R N i) = -2 := by
    intro i
    show R.S.integralPicardIntersectionBilinForm R.hreg (primeClass R i.val.val)
      (primeClass R i.val.val) = -2
    rw [pairing_primeClass, R.S.intersectionPairing_primeCurve R.hreg]
    have hw' := hw i.val i.property
    rw [w_eq_neg_selfIntersection] at hw'
    have hself : (i.val.val.selfIntersectionNumber R.hreg : ℚ) = -2 := by linarith
    show i.val.val.selfIntersectionNumber R.hreg = -2
    exact_mod_cast hself
  obtain ⟨hK, hsq', hdvd⟩ := KltDP.Support.u_picard_parity_finset
    (R.S.integralPicardIntersectionBilinForm R.hreg) (Kcls R) (Kcls_isCharacteristic R)
    (nodeFamily R N) (Finset.univ.filter (fun j => x j ≠ 0)) m (fun i _ => hsq i)
    (fun i _ j _ hij => horth i j hij) (fun i _ => nodeFamily_K R N hw i) hm
  exact ⟨m, hm, hK, hsq', hdvd⟩

/-- **5.3, `(I, t) = (36, 3)` and `(36, 4)`** are impossible by Riemann–Roch parity. -/
theorem picardIndexParity_36 (p : ℕ) [CharP k p] (hp : 0 < p)
    (hPext : ¬ IsExceptionalCurve R.π P)
    (hI : (R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index = 36)
    (ht : N.card = 3 ∨ N.card = 4) : False := by
  obtain ⟨b, hb⟩ := exists_basis_unimodular R p hp
  have hdet : |(borderedGram (graphWeightMatrix R.graph R.w) (contact R P) (-1)).det| = 1296 := by
    have h := index_sq_eq_abs_det_borderedGram R p hp P hP hPext
    rw [hI] at h
    rw [← R.A_eq_graphWeightMatrix, ← h]
    norm_num
  exact bordered_graph_determinant1296_impossible b _ hb (cls R) (primeClass R P) R.graph R.w
    (contact R P) (familyGram_eq_borderedGram_graph R P hP) hdet (nodeEmb R N)
    (fun i => hiso i.val i.property) (fun i => hw i.val i.property)
    (fun i => contact_eq_zero R P i.val (hPN i.val i.property))
    (Kcls R) (Kcls_isCharacteristic R) (fun i => nodeFamily_K R N hw i)
    (by rwa [Fintype.card_coe])

/-- **5.3, `(I, t) = (24, 4)`**: the forced divisibility `W₁ + W₂ + W₃ + W₄ = 2M` with
`M² = −2` and `K_S · M = 0`. -/
theorem picardIndexParity_24 (p : ℕ) [CharP k p] (hp : 0 < p)
    (hPext : ¬ IsExceptionalCurve R.π P)
    (hI : (R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index = 24)
    (ht : N.card = 4) :
    ∃ m : Additive R.S.toScheme.Pic, (2 : ℤ) • m = ∑ W ∈ N, cls R W ∧
      R.S.integralPicardIntersectionBilinForm R.hreg m m = -2 ∧
      R.S.integralPicardIntersectionBilinForm R.hreg (Kcls R) m = 0 := by
  obtain ⟨b, hb⟩ := exists_basis_unimodular R p hp
  have hdet : |(borderedGram (graphWeightMatrix R.graph R.w) (contact R P) (-1)).det| = 576 := by
    have h := index_sq_eq_abs_det_borderedGram R p hp P hP hPext
    rw [hI] at h
    rw [← R.A_eq_graphWeightMatrix, ← h]
    norm_num
  obtain ⟨m, hm, hsq, hK⟩ := bordered_graph_determinant576_four_nodes_half b _ hb (cls R)
    (primeClass R P) R.graph R.w (contact R P) (familyGram_eq_borderedGram_graph R P hP) hdet
    (nodeEmb R N) (fun i => hiso i.val i.property) (fun i => hw i.val i.property)
    (fun i => contact_eq_zero R P i.val (hPN i.val i.property))
    (Kcls R) (Kcls_isCharacteristic R) (fun i => nodeFamily_K R N hw i)
    (by rwa [Fintype.card_coe])
  refine ⟨m, ?_, hsq, hK⟩
  rw [hm]
  exact Finset.sum_coe_sort N (cls R)

/-- **5.3, the last case**: in characteristic `p > 2`, `(I, t) = (24, 4)` is excluded by
Theorem 5.1 (no nonempty even set of isolated nodes). -/
theorem picardIndexParity_24_impossible (p : ℕ) [CharP k p] (hp : 2 < p)
    (hPext : ¬ IsExceptionalCurve R.π P)
    (hI : (R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index = 24)
    (ht : N.card = 4) : False := by
  obtain ⟨m, hm, _, _⟩ := picardIndexParity_24 R P hP N hw hiso hPN p (by omega) hPext hI ht
  exact isolated_nodes_no_half_sum R p hp N (Finset.card_pos.mp (by omega)) hw hiso ⟨m, hm⟩

/-- **Lemma 5.3 (`lem:picard-parity`)**, bundled, in characteristic `p > 2`. -/
theorem picardIndexParity (p : ℕ) [CharP k p] (hp : 2 < p)
    (hPext : ¬ IsExceptionalCurve R.π P) :
    (DoublyEvenCode (integralNodeCode (nodeFamily R N)) ∧
      N.card - (R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index.factorization 2
        ≤ Module.finrank (ZMod 2) (integralNodeCode (nodeFamily R N))) ∧
    ((R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index = 36 →
      N.card = 3 ∨ N.card = 4 → False) ∧
    ((R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index = 24 → N.card = 4 →
      ∃ m : Additive R.S.toScheme.Pic, (2 : ℤ) • m = ∑ W ∈ N, cls R W ∧
        R.S.integralPicardIntersectionBilinForm R.hreg m m = -2 ∧
        R.S.integralPicardIntersectionBilinForm R.hreg (Kcls R) m = 0) ∧
    ((R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index = 24 → N.card = 4 →
      False) :=
  ⟨picardIndexParity_code R P hP N hw hiso hPN p (by omega) hPext,
    picardIndexParity_36 R P hP N hw hiso hPN p (by omega) hPext,
    picardIndexParity_24 R P hP N hw hiso hPN p (by omega) hPext,
    picardIndexParity_24_impossible R P hP N hw hiso hPN p hp hPext⟩

end NodeRows

end KltDP.Manuscript.S05

#print axioms KltDP.Manuscript.S05.picardIndexParity
#print axioms KltDP.Manuscript.S05.picardIndexParity_word
