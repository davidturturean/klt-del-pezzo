import KltDP.Lattices.SmallADEForestDecomposition
import KltDP.Lattices.IndexDeterminant
import KltDP.Lattices.IntegralNodeObstruction

/-!
# A lattice obstruction for an actual eight-vertex forest

The graph vertices index actual vectors in an integral module with a finite
basis and a unimodular bilinear form. Their Gram matrix is the negative
graph Cartan matrix. Additional actual vectors have a unimodular Gram
matrix and are perpendicular to the forest vectors in the stated direction.
The ambient basis has the combined index type.

The span of all these vectors is constructed, its basis and finite index are
derived, and its determinant computes that actual index squared. The actual
forest decomposition then forces more isolated vertices than the exponent
of two in the index. The existing integral node code produces a nonempty
half-sum of the original isolated graph vertices. Thus an explicit exclusion
of such half-sums bounds the forest's number of components by four.

No Picard group, intersection pairing, geometric embedding, or geometric
no-even-node theorem is constructed here. This is not the complete
manuscript `lem:eight-curve-forest`.

Reuse review: the pinned Mathlib determinant, `Basis.span`, linear
independence, and subgroup-index APIs are used directly. Newer official
Mathlib documentation for `FreeModule/Finite/CardQuotient`,
`Matrix/Determinant/Basic`, and `SimpleGraph/Finite` was also inspected;
the required APIs already exist at this pin. No source port or dependency
change is needed. The graph/count and integral-node-code adapters are the
existing project proofs, not additional input assumptions.
-/

namespace KltDP.Lattices.SmallADEForestLattice

open Matrix SimpleGraph SmallADEMatrices SmallADEPartitions SmallADEGraphs
open SmallADEForestDecomposition IndexDeterminant IntegralNodeObstruction
open scoped BigOperators

variable {M : Type*} [AddCommGroup M]

/-- The Gram matrix of an actual vector family in the original module. -/
def familyGram {ι : Type*} (B : LinearMap.BilinForm ℤ M) (v : ι → M) :
    Matrix ι ι ℤ := fun i j => B (v i) (v j)

/-- A nonzero actual Gram determinant implies independence of the original
vectors, by evaluating them against the same family. -/
theorem linearIndependent_of_familyGram_det_ne_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B : LinearMap.BilinForm ℤ M) (v : ι → M)
    (hdet : (familyGram B v).det ≠ 0) : LinearIndependent ℤ v := by
  apply LinearIndependent.of_comp (LinearMap.pi (fun j => B.flip (v j)))
  exact Matrix.linearIndependent_rows_of_det_ne_zero hdet

/-- The restricted form on the derived span basis is the original family's
actual Gram matrix. -/
theorem gram_span_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℤ M) (v : ι → M) (hv : LinearIndependent ℤ v) :
    BilinForm.toMatrix (Basis.span hv)
      (B.comp (Submodule.span ℤ (Set.range v)).subtype
        (Submodule.span ℤ (Set.range v)).subtype) = familyGram B v := by
  ext i j
  simp [BilinForm.toMatrix_apply, familyGram, Basis.span_apply]

/-- The determinant computes the index of the actual span in the original
unimodular module; no index value or square equation is a hypothesis. -/
theorem familyGram_natAbs_det_eq_span_index_sq {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ M)
    (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (v : ι → M) (hv : LinearIndependent ℤ v) :
    (familyGram B v).det.natAbs =
      (Submodule.span ℤ (Set.range v)).toAddSubgroup.index ^ 2 := by
  rw [← gram_span_basis B v hv]
  exact natAbs_det_gram_restriction_of_unimodular B b
    (Submodule.span ℤ (Set.range v)) (Basis.span hv) hB

/-- Even pairings with the supplied generators imply even pairings with
their actual integral span. -/
theorem even_pairing_span {ι : Type*} (B : LinearMap.BilinForm ℤ M)
    (v : ι → M) (x : M) (h : ∀ i, Even (B x (v i)))
    (y : M) (hy : y ∈ Submodule.span ℤ (Set.range v)) : Even (B x y) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact h i
  | zero => simp
  | add y z _ _ hy hz => simpa only [map_add] using hy.add hz
  | smul a y _ hy => simpa only [map_smul, smul_eq_mul] using hy.mul_left a

section GraphNodes

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An isolated vertex is a vertex outside the support of the actual graph. -/
theorem graphCartanMatrix_isolated_row (v : V) (hv : v ∉ G.support) (x : V) :
    graphCartanMatrix G v x = if v = x then 2 else 0 := by
  have hnot : ¬ G.Adj v x := fun h => hv ⟨x, h⟩
  simp [graphCartanMatrix, hnot]

/-- Pull an actual `A1` coordinate back to an original graph vertex. -/
def transportedNode (counts : Counts) (e : V ≃ Vertex counts) (i : Fin counts.a1) : V :=
  e.symm (nodeIndex counts i)

theorem transportedNode_injective (counts : Counts) (e : V ≃ Vertex counts) :
    Function.Injective (transportedNode counts e) :=
  e.symm.injective.comp (nodeIndex_injective counts)

/-- Full matrix equality identifies these transported vertices as genuinely
isolated in the original graph. -/
theorem transportedNode_not_mem_support (counts : Counts) (e : V ≃ Vertex counts)
    (hGram : (cartanMatrix counts).submatrix e e = graphCartanMatrix G)
    (i : Fin counts.a1) : transportedNode counts e i ∉ G.support := by
  rintro ⟨x, hx⟩
  have hne : e x ≠ nodeIndex counts i := by
    intro he
    have hxi : x = transportedNode counts e i := by
      apply e.injective
      simpa only [transportedNode, Equiv.apply_symm_apply] using he
    exact G.ne_of_adj hx hxi.symm
  have h := congr_fun (congr_fun hGram (transportedNode counts e i)) x
  have hzero : graphCartanMatrix G (transportedNode counts e i) x = 0 := by
    rw [← h]
    simpa only [Matrix.submatrix_apply, transportedNode, Equiv.apply_symm_apply] using
      cartanMatrix_node_offdiagonal counts i (e x) hne
  norm_num [graphCartanMatrix, G.ne_of_adj hx, hx] at hzero

/-- The actual vector attached to an isolated graph vertex pairs evenly
with every forest vector, because its Gram row is diagonal minus two. -/
theorem isolated_vector_pairing_even (B : LinearMap.BilinForm ℤ M) (w : V → M)
    (hGram : familyGram B w = -graphCartanMatrix G)
    (v : V) (hv : v ∉ G.support) (x : V) : Even (B (w v) (w x)) := by
  have h := congr_fun (congr_fun hGram v) x
  change B (w v) (w x) = -graphCartanMatrix G v x at h
  rw [h, graphCartanMatrix_isolated_row G v hv x]
  split_ifs <;> norm_num

end GraphNodes

/-- A one-sided perpendicularity statement is enough for the actual full
Gram matrix to be block triangular. Symmetry is not needed for this algebra. -/
theorem familyGram_sum_eq_fromBlocks {α V : Type*}
    (B : LinearMap.BilinForm ℤ M) (u : α → M) (w : V → M)
    (hperp : ∀ v i, B (w v) (u i) = 0) :
    familyGram B (Sum.elim u w) = Matrix.fromBlocks
      (familyGram B u) (fun i v => B (u i) (w v)) 0 (familyGram B w) := by
  ext i j
  cases i <;> cases j <;> simp [familyGram, hperp]

/-- The full actual Gram determinant loses precisely the unimodular
auxiliary block. The forest determinant is supplied by matrix computation. -/
theorem familyGram_sum_natAbs_det {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    (B : LinearMap.BilinForm ℤ M) (u : α → M) (w : V → M)
    (hperp : ∀ v i, B (w v) (u i) = 0)
    (hu : (familyGram B u).det.natAbs = 1)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hGram : familyGram B w = -graphCartanMatrix G)
    (counts : Counts) (hdet : (graphCartanMatrix G).det = (counts.rootDet : ℤ)) :
    (familyGram B (Sum.elim u w)).det.natAbs = counts.rootDet := by
  rw [familyGram_sum_eq_fromBlocks B u w hperp, Matrix.det_fromBlocks_zero₂₁,
    Int.natAbs_mul, hu, one_mul, hGram, Matrix.det_neg, hdet,
    Int.natAbs_mul, Int.natAbs_pow]
  simp

/-- An actual eight-vertex forest with at least five components forces an
integral half-sum of a nonempty set of its original isolated vertices.
The sublattice, its independence, finite index, and index square equation
are all derived from the displayed actual Gram matrices. -/
theorem exists_isolated_half_sum_of_eight_vertices {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    [∀ c : G.ConnectedComponent, Fintype c.supp]
    (hG : G.IsAcyclic) (hvertices : Fintype.card V = 8)
    (hcomponents : 5 ≤ Fintype.card G.ConnectedComponent)
    (b : Basis (α ⊕ V) ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (u : α → M) (w : V → M) (hu : (familyGram B u).det.natAbs = 1)
    (hperp : ∀ v i, B (w v) (u i) = 0)
    (hGram : familyGram B w = -graphCartanMatrix G) :
    ∃ J : Finset V, J.Nonempty ∧ (∀ v ∈ J, v ∉ G.support) ∧
      ∃ m : M, (2 : ℤ) • m = ∑ v ∈ J, w v := by
  classical
  obtain ⟨counts, e, hrank, hcount, hmatrix, hdet⟩ :=
    smallADEForest_decomposition G hG hvertices.le hcomponents
  have hfull := familyGram_sum_natAbs_det B u w hperp hu G hGram counts hdet
  have hpositive : 0 < counts.rootDet := by
    unfold Counts.rootDet
    positivity
  have hnonzero : (familyGram B (Sum.elim u w)).det ≠ 0 := by
    intro hz
    rw [hz, Int.natAbs_zero] at hfull
    omega
  have hli := linearIndependent_of_familyGram_det_ne_zero B (Sum.elim u w) hnonzero
  let Γ : Submodule ℤ M := Submodule.span ℤ (Set.range (Sum.elim u w))
  let bΓ : Basis (α ⊕ V) ℤ Γ := Basis.span hli
  letI : Γ.toAddSubgroup.FiniteIndex := ⟨ne_of_gt (index_pos b Γ bΓ)⟩
  have hsquare : counts.rootDet = Γ.toAddSubgroup.index ^ 2 :=
    hfull.symm.trans (familyGram_natAbs_det_eq_span_index_sq b B hB (Sum.elim u w) hli)
  have hindex : Γ.toAddSubgroup.index.factorization 2 < counts.a1 :=
    rankEight_square_factorization_lt_nodes counts Γ.toAddSubgroup.index
      (hrank.trans hvertices) (by omega) hsquare
  let nodes : Fin counts.a1 → V := transportedNode counts e
  have hnodes : Function.Injective nodes := transportedNode_injective counts e
  have hisolated : ∀ i, nodes i ∉ G.support :=
    transportedNode_not_mem_support G counts e hmatrix
  have hpair : ∀ i y, y ∈ Γ → Even (B (w (nodes i)) y) := by
    intro i y hy
    apply even_pairing_span B (Sum.elim u w) (w (nodes i)) ?_ y hy
    intro j
    cases j with
    | inl j => simpa only [Sum.elim_inl, hperp] using (Even.zero : Even (0 : ℤ))
    | inr v =>
        exact isolated_vector_pairing_even G B w hGram (nodes i) (hisolated i) v
  obtain ⟨J, hJ, m, hm⟩ :=
    exists_nonempty_integral_half_sum_of_index_factorization_lt_card
      b B hB Γ (fun i => w (nodes i)) hpair (by simpa only [Fintype.card_fin] using hindex)
  refine ⟨J.image nodes, hJ.image nodes, ?_, m, ?_⟩
  · intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact hisolated i
  · rw [Finset.sum_image (fun i _ j _ hij => hnodes hij)]
    exact hm

/-- An explicit no-even-node condition on the actual graph-indexed vectors
excludes five or more components. The condition is not asserted to follow
from geometry in this module. -/
theorem components_le_four_of_no_isolated_half_sum {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    [∀ c : G.ConnectedComponent, Fintype c.supp]
    (hG : G.IsAcyclic) (hvertices : Fintype.card V = 8)
    (b : Basis (α ⊕ V) ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (u : α → M) (w : V → M) (hu : (familyGram B u).det.natAbs = 1)
    (hperp : ∀ v i, B (w v) (u i) = 0)
    (hGram : familyGram B w = -graphCartanMatrix G)
    (hnoEven : ∀ J : Finset V, J.Nonempty → (∀ v ∈ J, v ∉ G.support) →
      ¬ ∃ m : M, (2 : ℤ) • m = ∑ v ∈ J, w v) :
    Fintype.card G.ConnectedComponent ≤ 4 := by
  by_contra hcount
  have hfive : 5 ≤ Fintype.card G.ConnectedComponent := by omega
  obtain ⟨J, hJ, hisolated, hhalf⟩ :=
    exists_isolated_half_sum_of_eight_vertices G hG hvertices hfive
      b B hB u w hu hperp hGram
  exact hnoEven J hJ hisolated hhalf

end KltDP.Lattices.SmallADEForestLattice
