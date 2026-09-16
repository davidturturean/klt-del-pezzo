import KltDP.Lattices.SmallADEGraphs
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.EquivFin

/-!
# Decomposing an actual small forest into its ADE multiplicities

The input is an actual finite acyclic graph with at most eight vertices and
at least five connected components. The component classification is derived
from that graph. Its five multiplicities count the fibers of the derived
component-kind function, rather than a supplied partition.

Actual vertex equivalences split the graph into its connected-component
supports, identify their integral Cartan matrices, and regroup those matrices
into the existing `SmallADEMatrices.cartanMatrix`. Rank, component totals,
and the determinant product then follow from those equivalences. No Picard
embedding, full-rank lattice index, or geometric node exclusion is claimed.

Reuse: pinned `Equiv.sigmaFiberEquiv`, `sigmaCongr`, `sigmaAssoc`,
`sigmaEquivProd`, and `Fintype.equivFinOfCardEq` provide the actual finite
reindexings. Existing block-diagonal and determinant APIs supply the matrix
operations. Newer official Mathlib graph/equivalence sources were checked;
the local adapter preserves the current pin and imports no new library.
-/

namespace KltDP.Lattices.SmallADEForestDecomposition

open Matrix SimpleGraph SmallADEMatrices SmallADEGraphs SmallADEPartitions

universe u v

/-- Multiplicities are cardinalities of the actual fibers of a kind label. -/
noncomputable def countsOfKinds {C : Type u} (kind : C → Kind) : Counts :=
  ⟨Nat.card {c // kind c = .a1}, Nat.card {c // kind c = .a2},
    Nat.card {c // kind c = .a3}, Nat.card {c // kind c = .a4},
    Nat.card {c // kind c = .d4}⟩

theorem multiplicity_countsOfKinds {C : Type u} (kind : C → Kind) (k : Kind) :
    multiplicity (countsOfKinds kind) k = Nat.card {c // kind c = k} := by
  cases k <;> rfl

/-- Number each actual fiber by its proved cardinality. -/
noncomputable def kindFiberEquiv {C : Type u} [Fintype C] (kind : C → Kind) (k : Kind) :
    {c // kind c = k} ≃ Fin (multiplicity (countsOfKinds kind) k) :=
  Fintype.equivFinOfCardEq (by rw [multiplicity_countsOfKinds, Nat.card_eq_fintype_card])

/-- The actual components are equivalent to kind-labelled numbered copies. -/
noncomputable def componentKeyEquiv {C : Type u} [Fintype C] (kind : C → Kind) :
    C ≃ ComponentIndex (countsOfKinds kind) :=
  (Equiv.sigmaFiberEquiv kind).symm.trans
    (Equiv.sigmaCongrRight (kindFiberEquiv kind))

theorem componentKeyEquiv_apply {C : Type u} [Fintype C] (kind : C → Kind) (c : C) :
    componentKeyEquiv kind c = ⟨kind c, kindFiberEquiv kind (kind c) ⟨c, rfl⟩⟩ := rfl

/-- In particular, the sum of the derived multiplicities is the number of
actual connected components, regardless of how the kind function was chosen. -/
theorem countsOfKinds_components {C : Type u} [Fintype C] (kind : C → Kind) :
    (countsOfKinds kind).components = Fintype.card C := by
  exact (card_components (countsOfKinds kind)).symm.trans
    (Fintype.card_congr (componentKeyEquiv kind).symm)

/-- Shuffle a component-copy label and its local vertex into the coordinate
order used by the existing full ADE matrix. -/
def copyVertexEquiv (counts : Counts) :
    (Σ c : ComponentIndex counts, KindVertex c.1) ≃ Vertex counts :=
  (Equiv.sigmaAssoc (fun k (_ : Fin (multiplicity counts k)) => KindVertex k)).trans
    (Equiv.sigmaCongrRight fun k =>
      (Equiv.sigmaEquivProd (Fin (multiplicity counts k)) (KindVertex k)).trans
        (Equiv.prodComm _ _))

theorem copyVertexEquiv_apply (counts : Counts) (k : Kind)
    (i : Fin (multiplicity counts k)) (v : KindVertex k) :
    copyVertexEquiv counts ⟨⟨k, i⟩, v⟩ = ⟨k, v, i⟩ := rfl

/-- Block matrices transport through an actual base equivalence and actual
fiber equivalences. Distinct source blocks stay distinct under the base map. -/
theorem blockDiagonal_submatrix_sigmaCongr
    {C : Type u} {D : Type v} [DecidableEq C] [DecidableEq D]
    {X : C → Type*} {Y : D → Type*}
    (A : ∀ c, Matrix (X c) (X c) ℤ) (B : ∀ d, Matrix (Y d) (Y d) ℤ)
    (e : C ≃ D) (f : ∀ c, X c ≃ Y (e c))
    (hAB : ∀ c, (B (e c)).submatrix (f c) (f c) = A c) :
    (Matrix.blockDiagonal' B).submatrix (Equiv.sigmaCongr e f) (Equiv.sigmaCongr e f) =
      Matrix.blockDiagonal' A := by
  ext ⟨c, x⟩ ⟨d, y⟩
  by_cases hcd : c = d
  · subst d
    change (Matrix.blockDiagonal' B) ⟨e c, f c x⟩ ⟨e c, f c y⟩ =
      (Matrix.blockDiagonal' A) ⟨c, x⟩ ⟨c, y⟩
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_eq]
    exact congr_fun (congr_fun (hAB c) x) y
  · have he : e c ≠ e d := fun h => hcd (e.injective h)
    change (Matrix.blockDiagonal' B) ⟨e c, f c x⟩ ⟨e d, f d y⟩ =
      (Matrix.blockDiagonal' A) ⟨c, x⟩ ⟨d, y⟩
    rw [Matrix.blockDiagonal'_apply_ne B _ _ he,
      Matrix.blockDiagonal'_apply_ne A _ _ hcd]

/-- The existing repeated blocks are the same actual matrix as one block for
each kind-labelled component copy. -/
theorem cartanMatrix_submatrix_copyVertexEquiv (counts : Counts) :
    (cartanMatrix counts).submatrix (copyVertexEquiv counts) (copyVertexEquiv counts) =
      Matrix.blockDiagonal' (fun c : ComponentIndex counts => componentMatrix c.1) := by
  ext ⟨⟨k, i⟩, v⟩ ⟨⟨l, j⟩, w⟩
  change cartanMatrix counts ⟨k, v, i⟩ ⟨l, w, j⟩ =
    (Matrix.blockDiagonal' (fun c : ComponentIndex counts => componentMatrix c.1))
      ⟨⟨k, i⟩, v⟩ ⟨⟨l, j⟩, w⟩
  by_cases hkl : k = l
  · subst l
    by_cases hij : i = j
    · subst j
      simp [cartanMatrix, repeatedMatrix, Matrix.blockDiagonal_apply]
    · have hcopy : (⟨k, i⟩ : ComponentIndex counts) ≠ ⟨k, j⟩ := by
        intro h
        exact hij (@sigma_mk_injective Kind (fun k => Fin (multiplicity counts k)) k i j h)
      rw [Matrix.blockDiagonal'_apply_ne
        (fun c : ComponentIndex counts => componentMatrix c.1) v w hcopy]
      simp [cartanMatrix, repeatedMatrix, Matrix.blockDiagonal_apply, hij]
  · have hcopy : (⟨k, i⟩ : ComponentIndex counts) ≠ ⟨l, j⟩ := by
      intro h
      exact hkl (congrArg Sigma.fst h)
    rw [Matrix.blockDiagonal'_apply_ne
      (fun c : ComponentIndex counts => componentMatrix c.1) v w hcopy]
    exact Matrix.blockDiagonal'_apply_ne (repeatedMatrix counts) (v, i) (w, j) hkl

/-- Regroup the actual component coordinates by their derived kind and copy. -/
noncomputable def regroupVertices {C : Type u} [Fintype C] (kind : C → Kind) :
    (Σ c, KindVertex (kind c)) ≃ Vertex (countsOfKinds kind) :=
  (Equiv.sigmaCongr (componentKeyEquiv kind)
    (fun c => Equiv.refl (KindVertex (kind c)))).trans
      (copyVertexEquiv (countsOfKinds kind))

/-- Regrouping preserves the full integer block matrix, including zero
entries between copies of the same kind. -/
theorem cartanMatrix_submatrix_regroupVertices {C : Type u} [Fintype C] [DecidableEq C]
    (kind : C → Kind) :
    (cartanMatrix (countsOfKinds kind)).submatrix (regroupVertices kind) (regroupVertices kind) =
      Matrix.blockDiagonal' (fun c => componentMatrix (kind c)) := by
  change ((cartanMatrix (countsOfKinds kind)).submatrix
      (copyVertexEquiv (countsOfKinds kind)) (copyVertexEquiv (countsOfKinds kind))).submatrix
      (Equiv.sigmaCongr (componentKeyEquiv kind) (fun c => Equiv.refl (KindVertex (kind c))))
      (Equiv.sigmaCongr (componentKeyEquiv kind) (fun c => Equiv.refl (KindVertex (kind c)))) = _
  rw [cartanMatrix_submatrix_copyVertexEquiv]
  exact blockDiagonal_submatrix_sigmaCongr
    (fun c => componentMatrix (kind c))
    (fun c : ComponentIndex (countsOfKinds kind) => componentMatrix c.1)
    (componentKeyEquiv kind)
    (fun c => Equiv.refl (KindVertex (kind c))) (fun _ => rfl)

/-- Splitting a graph into its actual connected-component supports is the
canonical sigma-of-fibers equivalence, not a chosen vertex partition. -/
def componentVerticesEquiv {V : Type*} (G : SimpleGraph V) :
    (Σ c : G.ConnectedComponent, c.supp) ≃ V :=
  Equiv.sigmaFiberEquiv G.connectedComponentMk

/-- The graph-defined Cartan matrix is block diagonal on actual connected
components: an edge cannot join vertices with different component classes. -/
theorem graphCartanMatrix_component_blocks {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq G.ConnectedComponent] :
    (graphCartanMatrix G).submatrix (componentVerticesEquiv G) (componentVerticesEquiv G) =
      Matrix.blockDiagonal' (fun c : G.ConnectedComponent => graphCartanMatrix (G.induce c.supp)) := by
  ext ⟨c, x⟩ ⟨d, y⟩
  by_cases hcd : c = d
  · subst d
    change graphCartanMatrix G x.val y.val =
      (Matrix.blockDiagonal' (fun c : G.ConnectedComponent => graphCartanMatrix (G.induce c.supp)))
        ⟨c, x⟩ ⟨c, y⟩
    rw [Matrix.blockDiagonal'_apply_eq]
    have hxy : x = y ↔ x.val = y.val := Subtype.ext_iff
    simp only [graphCartanMatrix, hxy]
    rfl
  · have hxy : x.val ≠ y.val := by
      intro h
      apply hcd
      exact x.property.symm.trans ((congrArg G.connectedComponentMk h).trans y.property)
    have hnadj : ¬G.Adj x.val y.val := by
      intro h
      apply hcd
      exact x.property.symm.trans ((SimpleGraph.ConnectedComponent.sound h.reachable).trans y.property)
    change graphCartanMatrix G x.val y.val =
      (Matrix.blockDiagonal' (fun c : G.ConnectedComponent => graphCartanMatrix (G.induce c.supp)))
        ⟨c, x⟩ ⟨d, y⟩
    rw [Matrix.blockDiagonal'_apply_ne
      (fun c : G.ConnectedComponent => graphCartanMatrix (G.induce c.supp)) x y hcd]
    simp [graphCartanMatrix, hxy, hnadj]

/-- The full ADE count matrix is derived from the actual forest. The proof
chooses only the already-proved component isomorphisms; no partition or
determinant equality is supplied as an input assumption. -/
theorem smallADEForest_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    [∀ c : G.ConnectedComponent, Fintype c.supp]
    (hG : G.IsAcyclic) (hvertices : Fintype.card V ≤ 8)
    (hcomponents : 5 ≤ Fintype.card G.ConnectedComponent) :
    ∃ counts : Counts, ∃ e : V ≃ Vertex counts,
      counts.rank = Fintype.card V ∧
      counts.components = Fintype.card G.ConnectedComponent ∧
      (cartanMatrix counts).submatrix e e = graphCartanMatrix G ∧
      (graphCartanMatrix G).det = (counts.rootDet : ℤ) := by
  classical
  choose kind iso hmatrix hrank hdet using
    (fun c => forest_component_matrix_classification G hG hvertices hcomponents c)
  let counts := countsOfKinds kind
  let f : (Σ c : G.ConnectedComponent, c.supp) ≃ (Σ c, KindVertex (kind c)) :=
    Equiv.sigmaCongr (Equiv.refl G.ConnectedComponent) (fun c => (iso c).toEquiv)
  let r := regroupVertices kind
  let e : V ≃ Vertex counts := (componentVerticesEquiv G).symm.trans (f.trans r)
  have hblocks :
      (Matrix.blockDiagonal' (fun c => componentMatrix (kind c))).submatrix f f =
        Matrix.blockDiagonal' (fun c : G.ConnectedComponent => graphCartanMatrix (G.induce c.supp)) := by
    exact blockDiagonal_submatrix_sigmaCongr
      (fun c : G.ConnectedComponent => graphCartanMatrix (G.induce c.supp))
      (fun c : G.ConnectedComponent => componentMatrix (kind c))
      (Equiv.refl G.ConnectedComponent)
      (fun c => (iso c).toEquiv) hmatrix
  have hwhole : (cartanMatrix counts).submatrix (f.trans r) (f.trans r) =
      (graphCartanMatrix G).submatrix (componentVerticesEquiv G) (componentVerticesEquiv G) := by
    change ((cartanMatrix counts).submatrix r r).submatrix f f = _
    rw [cartanMatrix_submatrix_regroupVertices, hblocks, graphCartanMatrix_component_blocks]
  have hmatrixG : (cartanMatrix counts).submatrix e e = graphCartanMatrix G := by
    ext v w
    have h := congr_fun (congr_fun hwhole ((componentVerticesEquiv G).symm v))
      ((componentVerticesEquiv G).symm w)
    simpa only [Matrix.submatrix_apply, e, Equiv.trans_apply, Equiv.apply_symm_apply] using h
  refine ⟨counts, e, ?_, countsOfKinds_components kind, hmatrixG, ?_⟩
  · exact (card_vertices counts).symm.trans (Fintype.card_congr e).symm
  · rw [← hmatrixG, Matrix.det_submatrix_equiv_self, det_cartanMatrix]

/-- The eight arithmetic rank partitions therefore apply to the determinant
of an actual eight-vertex forest with at least five actual components. -/
theorem eight_vertex_forest_determinant_rows {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    [∀ c : G.ConnectedComponent, Fintype c.supp]
    (hG : G.IsAcyclic) (hvertices : Fintype.card V = 8)
    (hcomponents : 5 ≤ Fintype.card G.ConnectedComponent) :
    ∃ counts : Counts, ∃ e : V ≃ Vertex counts,
      (cartanMatrix counts).submatrix e e = graphCartanMatrix G ∧
      counts ∈ rankEightRows ∧
      (graphCartanMatrix G).det = (counts.rootDet : ℤ) := by
  obtain ⟨counts, e, hrank, hcount, hmatrix, hdet⟩ :=
    smallADEForest_decomposition G hG (by omega) hcomponents
  exact ⟨counts, e, hmatrix,
    rankEight_classification counts (hrank.trans hvertices) (by omega), hdet⟩

end KltDP.Lattices.SmallADEForestDecomposition
