import KltDP.Lattices.SmallADEPartitions
import KltDP.LinearAlgebra.RootedTreeMatrix
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.DeriveFintype

/-!
# Actual integral matrices for small ADE component counts

Integer chain matrices are compared entrywise with the existing rational
chain matrices, and their determinant formula is transferred back to the
integers. The integer `D4` matrix is similarly compared with the existing
three-leaf rooted-star matrix at center weight two.

Arbitrary natural component counts determine an actual finite dependent
coordinate type and an actual block-diagonal integer matrix. Its coordinate
cardinality is the count model's rank, and its determinant is exactly the
root-determinant product in `SmallADEPartitions`. The negative matrix gives
an actual integer-valued bilinear form. Its `A1` coordinates are actual
standard-basis vectors of square minus two, orthogonal to every other basis
coordinate.

This is a matrix bridge for the manuscript's small-partition arithmetic.
It does not assert that an arbitrary graph or geometric exceptional forest
is isomorphic to these matrices, or supply its embedding in a Picard lattice.
-/

namespace KltDP.Lattices.SmallADEMatrices

open Matrix KltDP.LinearAlgebra
open SmallADEPartitions
open scoped BigOperators

/-- The integral Cartan matrix of an actual path on `Fin n`. -/
def integerChain (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

/-- The integer matrix reduces to the existing rational chain construction. -/
theorem integerChain_cast (n : ℕ) :
    (integerChain n).map (fun z => (z : ℚ)) = weightTwoChain (𝕜 := ℚ) n := by
  ext i j
  simp [integerChain, weightTwoChain_apply]

/-- The chain determinant formula is transferred through the injective integer cast. -/
theorem det_integerChain (n : ℕ) : (integerChain n).det = ((n + 1 : ℕ) : ℤ) := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_det, integerChain_cast, det_weightTwoChain]
  simp

/-- The same center-and-arms index type used by the existing rooted-star construction. -/
abbrev D4Index := Unit ⊕ ArmIndex (fun _ : Fin 3 => 1)

/-- The integral matrix of a center joined to three isolated leaves. -/
def integerD4 : Matrix D4Index D4Index ℤ := fun i j =>
  if i = j then 2 else if i = Sum.inl () ∨ j = Sum.inl () then -1 else 0

/-- Entrywise identification with the existing three-leaf rooted-star matrix. -/
theorem integerD4_cast :
    integerD4.map (fun z => (z : ℚ)) =
      rootedStarMatrix (fun _ : Fin 3 => 1) (2 : ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integerD4, rootedStarMatrix, armSpokes, chainArms,
      weightTwoChain_apply, Matrix.blockDiagonal'_apply]
  all_goals simp only [Sum.inl_ne_inr, Sum.inr_ne_inl, not_false_eq_true, and_self]

/-- The `D4` determinant is obtained from the actual rooted-star determinant. -/
theorem det_integerD4 : integerD4.det = 4 := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_det, integerD4_cast, det_rootedStarMatrix]
  norm_num [rootedStarSchur, Fin.sum_univ_succ, Fin.prod_univ_succ]

/-- The five component types admitted by the count model. -/
inductive Kind where
  | a1
  | a2
  | a3
  | a4
  | d4
  deriving DecidableEq, Fintype

private theorem kind_univ :
    (Finset.univ : Finset Kind) = {.a1, .a2, .a3, .a4, .d4} := by
  ext k
  cases k <;> simp

/-- Actual multiplicity of each type in the supplied count record. -/
def multiplicity (c : Counts) : Kind → ℕ
  | .a1 => c.a1
  | .a2 => c.a2
  | .a3 => c.a3
  | .a4 => c.a4
  | .d4 => c.d4

def kindRank : Kind → ℕ
  | .a1 => 1
  | .a2 => 2
  | .a3 => 3
  | .a4 => 4
  | .d4 => 4

def kindDet : Kind → ℕ
  | .a1 => 2
  | .a2 => 3
  | .a3 => 4
  | .a4 => 5
  | .d4 => 4

/-- Each component has the actual index type of its chain or star matrix. -/
abbrev KindVertex : Kind → Type
  | .a1 => Fin 1
  | .a2 => Fin 2
  | .a3 => Fin 3
  | .a4 => Fin 4
  | .d4 => D4Index

instance kindVertexFintype (k : Kind) : Fintype (KindVertex k) := by
  cases k <;> dsimp [KindVertex] <;> infer_instance

instance kindVertexDecidableEq (k : Kind) : DecidableEq (KindVertex k) := by
  cases k <;> dsimp [KindVertex] <;> infer_instance

/-- The actual block matrix for each component type. -/
def componentMatrix : (k : Kind) → Matrix (KindVertex k) (KindVertex k) ℤ
  | .a1 => integerChain 1
  | .a2 => integerChain 2
  | .a3 => integerChain 3
  | .a4 => integerChain 4
  | .d4 => integerD4

theorem card_kindVertex (k : Kind) : Fintype.card (KindVertex k) = kindRank k := by
  cases k <;> simp [KindVertex, kindRank, D4Index, ArmIndex]

/-- The five small determinant values are the determinants of the actual matrices. -/
theorem det_componentMatrix (k : Kind) : (componentMatrix k).det = (kindDet k : ℤ) := by
  cases k with
  | a1 =>
    change (integerChain 1).det = 2
    exact det_integerChain 1
  | a2 =>
    change (integerChain 2).det = 3
    exact det_integerChain 2
  | a3 =>
    change (integerChain 3).det = 4
    exact det_integerChain 3
  | a4 =>
    change (integerChain 4).det = 5
    exact det_integerChain 4
  | d4 =>
    change integerD4.det = 4
    exact det_integerD4

theorem componentMatrix_diagonal (k : Kind) (v : KindVertex k) :
    componentMatrix k v v = 2 := by
  cases k <;> simp [componentMatrix, integerChain, integerD4]

/-- Individual component copies, indexed by their actual natural multiplicity. -/
abbrev ComponentIndex (c : Counts) := Σ k : Kind, Fin (multiplicity c k)

/-- Actual vertices: component kind, local vertex, and component-copy number. -/
abbrev Vertex (c : Counts) := Σ k : Kind, KindVertex k × Fin (multiplicity c k)

theorem card_components (c : Counts) : Fintype.card (ComponentIndex c) = c.components := by
  simp [ComponentIndex, Fintype.card_sigma, kind_univ, multiplicity,
    Counts.components, Nat.add_assoc]

/-- The coordinate cardinality agrees with the rank of the supplied count model. -/
theorem card_vertices (c : Counts) : Fintype.card (Vertex c) = c.rank := by
  simp [Vertex, Fintype.card_sigma, card_kindVertex, kind_univ, multiplicity,
    kindRank, Counts.rank, Nat.mul_comm, Nat.add_assoc]

theorem finrank_integer_coordinates (c : Counts) :
    Module.finrank ℤ (Vertex c → ℤ) = c.rank :=
  (Module.finrank_eq_card_basis (Pi.basisFun ℤ (Vertex c))).trans (card_vertices c)

/-- Repeated copies of one actual component matrix. -/
def repeatedMatrix (c : Counts) (k : Kind) :
    Matrix (KindVertex k × Fin (multiplicity c k))
      (KindVertex k × Fin (multiplicity c k)) ℤ :=
  Matrix.blockDiagonal (fun _ : Fin (multiplicity c k) => componentMatrix k)

/-- The actual integral positive Cartan matrix of the entire count record. -/
def cartanMatrix (c : Counts) : Matrix (Vertex c) (Vertex c) ℤ :=
  Matrix.blockDiagonal' (repeatedMatrix c)

/-- Dependent block determinants, proved by the actual block-triangular
decomposition and explicit equivalences with each coordinate fiber. -/
theorem det_dependent_blockDiagonal {α : Type*} [Fintype α] [DecidableEq α]
    {κ : α → Type*} [∀ a, Fintype (κ a)] [∀ a, DecidableEq (κ a)]
    (A : ∀ a, Matrix (κ a) (κ a) ℤ) :
    (Matrix.blockDiagonal' A).det = ∏ a, (A a).det := by
  classical
  letI : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α)
    (Fintype.equivFin α).injective
  have htri := Matrix.blockTriangular_blockDiagonal' A
  rw [htri.det_fintype]
  apply Finset.prod_congr rfl
  intro a _
  let e : κ a ≃ {x : Sigma κ // x.1 = a} :=
    { toFun := fun i => ⟨⟨a, i⟩, rfl⟩
      invFun := fun x => x.2 ▸ x.1.2
      left_inv := by intro i; rfl
      right_inv := by
        rintro ⟨⟨b, i⟩, h⟩
        cases h
        rfl }
  have hblock :
      (((Matrix.blockDiagonal' A).toSquareBlock Sigma.fst a).submatrix e e) = A a := by
    ext i j
    simp [e, Matrix.toSquareBlock_def, Matrix.submatrix_apply]
  exact (Matrix.det_submatrix_equiv_self e _).symm.trans (congrArg Matrix.det hblock)

/-- The arbitrary count record's determinant product is an actual matrix determinant. -/
theorem det_cartanMatrix (c : Counts) : (cartanMatrix c).det = (c.rootDet : ℤ) := by
  rw [cartanMatrix, det_dependent_blockDiagonal]
  simp only [repeatedMatrix, Matrix.det_blockDiagonal, det_componentMatrix,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp [kind_univ, multiplicity, kindDet, Counts.rootDet, mul_assoc]

/-- The actual intersection-sign Gram matrix. -/
def negativeGramMatrix (c : Counts) : Matrix (Vertex c) (Vertex c) ℤ := -cartanMatrix c

theorem det_negativeGramMatrix (c : Counts) :
    (negativeGramMatrix c).det = (-1 : ℤ) ^ c.rank * (c.rootDet : ℤ) := by
  rw [negativeGramMatrix, Matrix.det_neg, det_cartanMatrix, card_vertices]

/-- Its absolute determinant is exactly the count model's root determinant. -/
theorem natAbs_det_negativeGramMatrix (c : Counts) :
    (negativeGramMatrix c).det.natAbs = c.rootDet := by
  rw [det_negativeGramMatrix, Int.natAbs_mul, Int.natAbs_pow]
  simp

/-- The negative Gram matrix defines an actual integer-valued bilinear form. -/
def negativeForm (c : Counts) : LinearMap.BilinForm ℤ (Vertex c → ℤ) :=
  (negativeGramMatrix c).toBilin'

/-- The unique local coordinate of each actual `A1` component copy. -/
def nodeIndex (c : Counts) (i : Fin c.a1) : Vertex c := ⟨.a1, (0 : Fin 1), i⟩

theorem nodeIndex_injective (c : Counts) : Function.Injective (nodeIndex c) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun x : Vertex c => x.2.2.val) hij

/-- The isolated nodes are actual coordinate basis vectors. -/
def nodeVector (c : Counts) (i : Fin c.a1) : Vertex c → ℤ := Pi.single (nodeIndex c i) 1

theorem nodeVector_eq_basis (c : Counts) (i : Fin c.a1) :
    nodeVector c i = Pi.basisFun ℤ (Vertex c) (nodeIndex c i) := by
  simp [nodeVector]

theorem cartanMatrix_diagonal (c : Counts) (v : Vertex c) : cartanMatrix c v v = 2 := by
  rcases v with ⟨k, v, j⟩
  simp [cartanMatrix, repeatedMatrix, componentMatrix_diagonal]

/-- Every other actual coordinate lies in a different component from the
unique vertex of an `A1` block, so the corresponding matrix entry vanishes. -/
theorem cartanMatrix_node_offdiagonal (c : Counts) (i : Fin c.a1)
    (x : Vertex c) (hne : x ≠ nodeIndex c i) : cartanMatrix c (nodeIndex c i) x = 0 := by
  rcases x with ⟨k, v, j⟩
  cases k
  · have hij : i ≠ j := by
      intro h
      subst j
      have hv : v = (0 : Fin 1) := Subsingleton.elim _ _
      subst v
      exact hne rfl
    simp [cartanMatrix, nodeIndex, repeatedMatrix, Matrix.blockDiagonal_apply, hij]
  all_goals simp [cartanMatrix, nodeIndex, Matrix.blockDiagonal'_apply]

/-- The actual integer bilinear square of every isolated node is minus two. -/
theorem negativeForm_node_square (c : Counts) (i : Fin c.a1) :
    negativeForm c (nodeVector c i) (nodeVector c i) = -2 := by
  simp only [negativeForm, nodeVector, Matrix.toBilin'_single,
    negativeGramMatrix, Matrix.neg_apply]
  rw [cartanMatrix_diagonal]

/-- An isolated node is perpendicular to every other actual basis vector. -/
theorem negativeForm_node_basis_pairing (c : Counts) (i : Fin c.a1)
    (x : Vertex c) (hne : x ≠ nodeIndex c i) :
    negativeForm c (nodeVector c i) (Pi.basisFun ℤ (Vertex c) x) = 0 := by
  simp only [negativeForm, nodeVector, Pi.basisFun_apply, Matrix.toBilin'_single,
    negativeGramMatrix, Matrix.neg_apply]
  rw [cartanMatrix_node_offdiagonal c i x hne, neg_zero]

/-- Distinct supplied node basis vectors are pairwise orthogonal. -/
theorem negativeForm_nodes_orthogonal (c : Counts) (i j : Fin c.a1) (hij : i ≠ j) :
    negativeForm c (nodeVector c i) (nodeVector c j) = 0 := by
  have hne : nodeIndex c j ≠ nodeIndex c i := fun h =>
    hij ((nodeIndex_injective c h).symm)
  simpa only [nodeVector_eq_basis] using
    negativeForm_node_basis_pairing c i (nodeIndex c j) hne

end KltDP.Lattices.SmallADEMatrices
