import KltDP.LinearAlgebra.SmallRootedTrees
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# From rooted graph isomorphisms to the weighted Green table

The weighted matrix is defined directly from a simple graph: root diagonal
`b`, every other diagonal two, and minus one precisely on graph edges. A
root-preserving graph isomorphism gives an equality of reindexed matrices and
of their inverse root entries.

For the eight listed graphs, the weighted matrices are identified with the
actual arm and leaf-star matrices already used in the inverse calculations.
The final theorem therefore derives the Green table for an arbitrary finite
rooted tree with at most three edges, rather than assuming its matrix is a
listed example. The shape specialization uses rational coefficients, as do
the manuscript's intersection calculations; matrix transport itself works
over any field.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

variable {𝕜 V W : Type*} [Field 𝕜]

/-- The actual positive intersection matrix associated with a rooted simple
graph and one distinguished weight. This definition does not assume positive
definiteness. -/
def rootedGraphMatrix [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : V) (b : 𝕜) : Matrix V V 𝕜 :=
  fun v w => if v = w then (if v = root then b else 2) else if G.Adj v w then -1 else 0

/-- Changing the root weight changes exactly its diagonal entry. -/
theorem rootedGraphMatrix_weight_update [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (root : V) (b c : 𝕜) (v w : V) :
    rootedGraphMatrix G root b v w =
      if v = root ∧ w = root then b else rootedGraphMatrix G root c v w := by
  by_cases hv : v = root
  · subst v
    by_cases hw : w = root
    · subst w
      simp [rootedGraphMatrix]
    · simp [rootedGraphMatrix, hw, Ne.symm hw]
  · simp [rootedGraphMatrix, hv]

/-- Its diagonal-minus-two vector is the root-supported canonical source. -/
theorem rootedGraphMatrix_diagonal_source [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (root : V) (b : 𝕜) :
    (fun v => rootedGraphMatrix G root b v v - 2) = Pi.single root (b - 2) := by
  funext v
  by_cases hv : v = root
  · subst v
    simp [rootedGraphMatrix]
  · simp [rootedGraphMatrix, hv, Pi.single_eq_of_ne hv]

/-- A root-preserving graph isomorphism identifies the actual weighted
matrices after reindexing, for every value of the root weight. -/
theorem rootedGraphMatrix_submatrix [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (root : V) (targetRoot : W) (hroot : e root = targetRoot) (b : 𝕜) :
    (rootedGraphMatrix H targetRoot b).submatrix e.toEquiv e.toEquiv =
      rootedGraphMatrix G root b := by
  ext v w
  have heq : e v = e w ↔ v = w := e.toEquiv.injective.eq_iff
  have hroot' : e v = targetRoot ↔ v = root := by
    rw [← hroot]
    exact e.toEquiv.injective.eq_iff
  change rootedGraphMatrix H targetRoot b (e v) (e w) =
    rootedGraphMatrix G root b v w
  simp only [rootedGraphMatrix, heq, hroot', e.map_adj_iff]

/-- Reindexing preserves the inverse entry at the distinguished root. The
identity also holds for singular matrices under Mathlib's nonsingular-inverse
convention; no invertibility premise is hidden here. -/
theorem rootedGraphMatrix_inverse_root_eq [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (root : V) (targetRoot : W) (hroot : e root = targetRoot) (b : 𝕜) :
    (rootedGraphMatrix G root b)⁻¹ root root =
      (rootedGraphMatrix H targetRoot b)⁻¹ targetRoot targetRoot := by
  rw [← rootedGraphMatrix_submatrix e root targetRoot hroot b,
    Matrix.inv_submatrix_equiv]
  change (rootedGraphMatrix H targetRoot b)⁻¹ (e root) (e root) = _
  rw [hroot]

/-- Root coefficient of any source concentrated at the root. -/
theorem rootedGraphMatrix_source_root [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) (b t : 𝕜) :
    ((rootedGraphMatrix G root b)⁻¹ *ᵥ Pi.single root t) root =
      t * (rootedGraphMatrix G root b)⁻¹ root root := by
  change dotProduct ((rootedGraphMatrix G root b)⁻¹ root) (Pi.single root t) = _
  rw [dotProduct_single, mul_comm]

/-- The source correction is the square of its strength times the root Green
entry; `t = b-2` gives the manuscript's canonical correction. -/
theorem rootedGraphMatrix_source_correction [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) (b t : 𝕜) :
    dotProduct (Pi.single root t)
      ((rootedGraphMatrix G root b)⁻¹ *ᵥ Pi.single root t) =
        t ^ 2 * (rootedGraphMatrix G root b)⁻¹ root root := by
  rw [single_dotProduct, rootedGraphMatrix_source_root]
  ring

/-- The previously defined actual matrices, now allowing any rational root
weight instead of fixing that weight at three. -/
def rootedBlockMatrixAt : (choice : RootedBlockChoice) → ℚ →
    Matrix (RootedBlockVertex choice) (RootedBlockVertex choice) ℚ
  | .arms shape, b => rootedArmMatrix shape b
  | .leafStar, b => leafRootedStarMatrix b

/-- Inspecting the block definitions proves that only the root diagonal
depends on `b`; no matrix multiplication is repeated. -/
theorem rootedBlockMatrixAt_weight_update (choice : RootedBlockChoice) (b : ℚ) :
    ∀ v w : RootedBlockVertex choice,
      rootedBlockMatrixAt choice b v w =
        if v = rootedBlockRoot choice ∧ w = rootedBlockRoot choice then b
        else rootedBlockMatrix choice v w := by
  cases choice with
  | arms shape =>
    intro v w
    cases v with
    | inl u =>
      cases u
      cases w with
      | inl u => cases u; rfl
      | inr w => rfl
    | inr v =>
      cases w with
      | inl u => cases u; rfl
      | inr w => rfl
  | leafStar =>
    intro v w
    cases v with
    | inl u =>
      cases u
      cases w with
      | inl u => cases u; rfl
      | inr w => rfl
    | inr v =>
      cases w with
      | inl u => cases u; rfl
      | inr w => rfl

private theorem rootedBlockMatrix_diagonal (choice : RootedBlockChoice)
    (v : RootedBlockVertex choice) :
    rootedBlockMatrix choice v v = if v = rootedBlockRoot choice then 3 else 2 := by
  have hsource : (fun v => rootedBlockMatrix choice v v - 2) =
      Pi.single (f := fun _ : RootedBlockVertex choice => ℚ)
        (rootedBlockRoot choice) ((3 : ℚ) - 2) := by
    cases choice with
    | arms shape => exact rootedArmMatrix_diagonal_source shape (3 : ℚ)
    | leafStar => exact leafRootedStarMatrix_diagonal_source (3 : ℚ)
  have hvsource := congr_fun hsource v
  by_cases hv : v = rootedBlockRoot choice
  · subst v
    rw [Pi.single_eq_same] at hvsource
    simp only [if_pos rfl, if_true]
    linarith
  · simp [hv, Pi.single_eq_of_ne hv] at hvsource ⊢; linarith

/-- The block definitions supply an exhaustive value set for off-diagonal
entries. This prevents the adjacency bridge from overlooking a nonedge with
some other nonzero matrix entry. -/
private theorem rootedBlockMatrix_offdiagonal (choice : RootedBlockChoice)
    (v w : RootedBlockVertex choice) (hne : v ≠ w) :
    rootedBlockMatrix choice v w = -1 ∨ rootedBlockMatrix choice v w = 0 := by
  cases choice with
  | arms shape =>
    rcases v with ⟨⟩ | ⟨a, i⟩ <;> rcases w with ⟨⟩ | ⟨b, j⟩
    · exact False.elim (hne rfl)
    · change -(if j.val = 0 then (1 : ℚ) else 0) = -1 ∨
        -(if j.val = 0 then (1 : ℚ) else 0) = 0
      split_ifs <;> norm_num
    · change -(if i.val = 0 then (1 : ℚ) else 0) = -1 ∨
        -(if i.val = 0 then (1 : ℚ) else 0) = 0
      split_ifs <;> norm_num
    · change chainArms (rootedArmLengths shape) ⟨a, i⟩ ⟨b, j⟩ = (-1 : ℚ) ∨
        chainArms (rootedArmLengths shape) ⟨a, i⟩ ⟨b, j⟩ = 0
      by_cases hab : a = b
      · subst b
        have hij : i ≠ j := by
          intro hij
          subst j
          exact hne rfl
        simp only [chainArms, Matrix.blockDiagonal'_apply_eq,
          weightTwoChain_apply, if_neg hij]
        split_ifs <;> norm_num
      · exact Or.inr (Matrix.blockDiagonal'_apply_ne
          (fun a : Fin 3 => weightTwoChain (𝕜 := ℚ) (rootedArmLengths shape a)) i j hab)
  | leafStar =>
    rcases v with ⟨⟩ | i <;> rcases w with ⟨⟩ | j
    · exact False.elim (hne rfl)
    · change Pi.single (f := fun _ : Fin 3 => ℚ) 1 (-1) j = -1 ∨
        Pi.single (f := fun _ : Fin 3 => ℚ) 1 (-1) j = 0
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · change Pi.single (f := fun _ : Fin 3 => ℚ) 1 (-1) i = -1 ∨
        Pi.single (f := fun _ : Fin 3 => ℚ) 1 (-1) i = 0
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · have hij : i ≠ j := by
        intro hij
        subst j
        exact hne rfl
      change weightTwoChain 3 i j = (-1 : ℚ) ∨ weightTwoChain 3 i j = 0
      simp only [weightTwoChain_apply, if_neg hij]
      split_ifs <;> norm_num

/-- At the fixed reference weight, the graph-defined matrix is exactly the
matrix from which the graph was constructed. The diagonal-source, adjacency,
and off-diagonal value results account for every entry. -/
theorem rootedBlockGraph_matrix_three : ∀ choice : RootedBlockChoice,
    rootedGraphMatrix (rootedBlockGraph choice) (rootedBlockRoot choice) (3 : ℚ) =
      rootedBlockMatrix choice := by
  intro choice
  ext v w
  by_cases hvw : v = w
  · subst w
    simp only [rootedGraphMatrix, if_pos rfl, if_true, rootedBlockMatrix_diagonal]
  · by_cases hadj : (rootedBlockGraph choice).Adj v w
    · have hentry := (rootedBlockGraph_adj_iff choice v w).mp hadj
      simp [rootedGraphMatrix, hvw, hadj, hentry]
    · have hentry : rootedBlockMatrix choice v w = 0 := by
        rcases rootedBlockMatrix_offdiagonal choice v w hvw with hentry | hentry
        · exact False.elim (hadj ((rootedBlockGraph_adj_iff choice v w).mpr hentry))
        · exact hentry
      simp [rootedGraphMatrix, hvw, hadj, hentry]

/-- The symbolic weight-update identities attach the actual shape matrices to
the graph-defined matrix at every rational root weight. -/
theorem rootedBlockMatrixAt_eq_graph (choice : RootedBlockChoice) (b : ℚ) :
    rootedBlockMatrixAt choice b =
      rootedGraphMatrix (rootedBlockGraph choice) (rootedBlockRoot choice) b := by
  ext v w
  rw [rootedBlockMatrixAt_weight_update,
    rootedGraphMatrix_weight_update _ _ b (3 : ℚ), rootedBlockGraph_matrix_three]

/-- The eight rational expressions in the source's root Green table. -/
def rootedBlockGreen : RootedBlockChoice → ℚ → ℚ
  | .arms shape, b =>
    (rootedArmGreenNumerator shape : ℚ) / rootedArmDenominator shape b
  | .leafStar, b => 1 / (b - 1)

/-- Reuse of the already established inverse formulas for the actual matrices.
All nonvanishing requirements follow from the source assumption `b ≥ 3`. -/
theorem rootedBlockMatrixAt_inverse_root (choice : RootedBlockChoice) {b : ℚ}
    (hb : 3 ≤ b) :
    (rootedBlockMatrixAt choice b)⁻¹ (rootedBlockRoot choice) (rootedBlockRoot choice) =
      rootedBlockGreen choice b := by
  cases choice with
  | arms shape => exact rootedArmMatrix_inverse_root_of_three_le shape hb
  | leafStar => exact leafRootedStarMatrix_inverse_root_of_three_le hb

/-- The Green table for an arbitrary finite rooted tree with at most three
edges. Both family membership and the edge-budget correspondence are derived
from the graph, not included among the hypotheses. -/
theorem smallRootedTree_inverse_root {U : Type*} [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) [DecidableRel G.Adj] (root : U)
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) {b : ℚ} (hb : 3 ≤ b) :
    ∃ choice : RootedBlockChoice,
      rootedBlockEdges choice = G.edgeFinset.card ∧
        (rootedGraphMatrix G root b)⁻¹ root root = rootedBlockGreen choice b := by
  obtain ⟨choice, e, hroot⟩ := smallRootedTree_classification hG hedges root
  refine ⟨choice, rootedBlockEdges_eq_of_iso e, ?_⟩
  rw [rootedGraphMatrix_inverse_root_eq e root (rootedBlockRoot choice) hroot b,
    ← rootedBlockMatrixAt_eq_graph choice b, rootedBlockMatrixAt_inverse_root choice hb]

end KltDP.LinearAlgebra
