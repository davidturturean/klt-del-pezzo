/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Lu-Ming Zhang
-/
import KltDP.LinearAlgebra.NearestHigherWeightPath
import KltDP.LinearAlgebra.WeightedTwoEndPath
import KltDP.LinearAlgebra.CanonicalEndPath
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Tactic

/-!
# Actual weighted matrices along induced paths

The weighted graph matrix is the existing Mathlib diagonal matrix minus the
existing Mathlib adjacency matrix. A graph embedding transports both pieces.
The actual endpoint and interior weights then identify the selected principal
matrix with the path matrices whose inverse-source formulas were proved.

`embedding_submatrix_adjMatrix` is a small source port of official Apache-2.0
Mathlib `SimpleGraph.Embedding.submatrix_adjMatrix`, revision
5aedf732b6987e8c26ab3c9ebc855314f82b045f, AdjMatrix.lean line 290. The above
notice is retained for that port. All required proof APIs exist in the pin.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

variable {V W 𝕜 : Type*} [Field 𝕜]

/-- The standard path adjacency is decidable by its two explicit successor
equalities. The pin exposes this equivalence but not the instance. -/
instance decidablePathGraphAdj (n : ℕ) : DecidableRel (SimpleGraph.pathGraph n).Adj :=
  fun i j => decidable_of_iff (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    SimpleGraph.pathGraph_adj.symm

/-- An actual weighted graph matrix: its diagonal is the supplied weight
function, and every graph edge contributes minus one. -/
def graphWeightMatrix [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → 𝕜) : Matrix V V 𝕜 :=
  Matrix.diagonal weight - G.adjMatrix 𝕜

/-- Entry formula from the existing diagonal and adjacency definitions. -/
theorem graphWeightMatrix_apply [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (weight : V → 𝕜) (v w : V) :
    graphWeightMatrix G weight v w =
      if v = w then weight v else if G.Adj v w then -1 else 0 := by
  by_cases hvw : v = w
  · subst w
    simp [graphWeightMatrix, SimpleGraph.adjMatrix_apply]
  · by_cases hadj : G.Adj v w <;>
      simp [graphWeightMatrix, Matrix.diagonal_apply_ne _ hvw,
        SimpleGraph.adjMatrix_apply, hvw, hadj]

/-- The actual diagonal is exactly the graph weight. -/
theorem graphWeightMatrix_diagonal [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (weight : V → 𝕜) (v : V) :
    graphWeightMatrix G weight v v = weight v := by
  simp [graphWeightMatrix_apply]

/-- The canonical source of this actual matrix is `weight−2`. -/
theorem graphWeightMatrix_diagonal_source [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (weight : V → 𝕜) :
    (fun v => graphWeightMatrix G weight v v - 2) = fun v => weight v - 2 := by
  ext v
  rw [graphWeightMatrix_diagonal]

/-- Port of the official newer adjacency-matrix embedding theorem. -/
theorem embedding_submatrix_adjMatrix {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ↪g H) :
    (H.adjMatrix 𝕜).submatrix e e = G.adjMatrix 𝕜 := by
  ext
  simp

/-- An actual graph embedding transports the weighted matrix to its actual
principal submatrix, with the restricted weight function. -/
theorem graphWeightMatrix_submatrix [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ↪g H) (weight : W → 𝕜) :
    (graphWeightMatrix H weight).submatrix e e = graphWeightMatrix G (weight ∘ e) := by
  change (Matrix.diagonal weight).submatrix e e - (H.adjMatrix 𝕜).submatrix e e = _
  rw [Matrix.submatrix_diagonal weight e e.injective, embedding_submatrix_adjMatrix e]
  rfl

/-- Adding an arbitrary diagonal correction to the actual weight-two chain
is the weighted matrix of Mathlib's actual standard path graph. -/
theorem chain_diagonal_update_eq_graphWeightMatrix (n : ℕ) (correction : Fin n → 𝕜) :
    weightTwoChain n + Matrix.diagonal correction =
      graphWeightMatrix (SimpleGraph.pathGraph n) (fun i => 2 + correction i) := by
  ext i j
  simp only [Matrix.add_apply, weightTwoChain_apply, Matrix.diagonal_apply,
    graphWeightMatrix_apply, SimpleGraph.pathGraph_adj]
  split_ifs <;> ring

/-- Actual graph-matrix expression for the two higher-weight endpoint path. -/
theorem weightedTwoEndPath_eq_graphWeightMatrix (d : ℕ) (β : 𝕜) :
    weightedTwoEndPath d β =
      graphWeightMatrix (SimpleGraph.pathGraph (d + 1)) (fun i => 2 + twoEndSource d β i) :=
  chain_diagonal_update_eq_graphWeightMatrix (d + 1) (twoEndSource d β)

/-- Actual graph-matrix expression for the path with one higher-weight endpoint. -/
theorem canonicalEndPath_eq_graphWeightMatrix (d : ℕ) (β : 𝕜) :
    canonicalEndPath d β =
      graphWeightMatrix (SimpleGraph.pathGraph (d + 1)) (fun i => 2 + canonicalEndSource d β i) :=
  chain_diagonal_update_eq_graphWeightMatrix (d + 1) (canonicalEndSource d β)

private theorem path_zero_ne_last {d : ℕ} (hd : 0 < d) :
    (0 : Fin (d + 1)) ≠ Fin.last d := by
  intro h
  have hval : (0 : ℕ) = d := congrArg Fin.val h
  omega

/-- For an actual induced path of positive length, first weight `β`, last
weight exactly three, and weight-two interiors give the actual two-end matrix.
The terminal weight equality is explicit; merely being higher-weight would
not justify this matrix identification. -/
theorem graphWeightMatrix_submatrix_twoEnd [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (weight : V → 𝕜) {d : ℕ}
    (e : SimpleGraph.pathGraph (d + 1) ↪g G) (hd : 0 < d) (β : 𝕜)
    (hfirst : weight (e 0) = β) (hlast : weight (e (Fin.last d)) = 3)
    (hinterior : ∀ i, i ≠ 0 → i ≠ Fin.last d → weight (e i) = 2) :
    (graphWeightMatrix G weight).submatrix e e = weightedTwoEndPath d β := by
  have hweights : weight ∘ e = fun i => 2 + twoEndSource d β i := by
    funext i
    change weight (e i) = _
    by_cases hi0 : i = 0
    · subst i
      rw [hfirst]
      simp only [twoEndSource, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (path_zero_ne_last hd), add_zero]
      ring
    · by_cases hilast : i = Fin.last d
      · subst i
        rw [hlast]
        simp only [twoEndSource, Pi.add_apply, Pi.single_eq_of_ne hi0,
          Pi.single_eq_same, zero_add]
        ring
      · rw [hinterior i hi0 hilast]
        simp only [twoEndSource, Pi.add_apply, Pi.single_eq_of_ne hi0,
          Pi.single_eq_of_ne hilast, zero_add, add_zero]
  rw [graphWeightMatrix_submatrix e weight, hweights, ← weightedTwoEndPath_eq_graphWeightMatrix]

/-- An induced path with first weight `β` and every other weight two has the
actual canonical-end path matrix. This includes the one-vertex case. -/
theorem graphWeightMatrix_submatrix_canonicalEnd [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (weight : V → 𝕜) {d : ℕ}
    (e : SimpleGraph.pathGraph (d + 1) ↪g G) (β : 𝕜)
    (hfirst : weight (e 0) = β) (hrest : ∀ i, i ≠ 0 → weight (e i) = 2) :
    (graphWeightMatrix G weight).submatrix e e = canonicalEndPath d β := by
  have hweights : weight ∘ e = fun i => 2 + canonicalEndSource d β i := by
    funext i
    change weight (e i) = _
    by_cases hi : i = 0
    · subst i
      rw [hfirst]
      simp only [canonicalEndSource, Pi.single_eq_same]
      ring
    · rw [hrest i hi]
      simp only [canonicalEndSource, Pi.single_eq_of_ne hi, add_zero]
  rw [graphWeightMatrix_submatrix e weight, hweights, ← canonicalEndPath_eq_graphWeightMatrix]

/-- The shortest-path result supplies the graph embedding in the two-end
identification, so inducedness is derived from the actual shortest distance. -/
theorem shortest_path_matrix_twoEnd [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (weight : V → 𝕜) {root target : V} (p : G.Walk root target)
    (hp : p.length = G.dist root target) (hpos : 0 < p.length) (β : 𝕜)
    (hfirst : weight root = β) (hlast : weight target = 3)
    (hinterior : ∀ i : ℕ, 0 < i → i < p.length → weight (p.getVert i) = 2) :
    (graphWeightMatrix G weight).submatrix (walkVertexMap p) (walkVertexMap p) =
      weightedTwoEndPath p.length β := by
  apply graphWeightMatrix_submatrix_twoEnd G weight (shortestWalkGraphEmbedding p hp) hpos β
  · change weight (walkVertexMap p 0) = β
    rw [walkVertexMap_zero]
    exact hfirst
  · change weight (walkVertexMap p (Fin.last p.length)) = 3
    rw [walkVertexMap_last]
    exact hlast
  · intro i hi0 hilast
    change weight (p.getVert i.val) = 2
    have h0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    have hlast' : i.val ≠ p.length := fun h => hilast (Fin.ext h)
    exact hinterior i.val (by omega) (by have := i.isLt; omega)

/-- The canonical-end identification likewise uses the actual shortest-path
embedding, with the higher-weight endpoint indexed first. -/
theorem shortest_path_matrix_canonicalEnd [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (weight : V → 𝕜) {root target : V} (p : G.Walk root target)
    (hp : p.length = G.dist root target) (β : 𝕜) (hfirst : weight root = β)
    (hrest : ∀ i : ℕ, 0 < i → i ≤ p.length → weight (p.getVert i) = 2) :
    (graphWeightMatrix G weight).submatrix (walkVertexMap p) (walkVertexMap p) =
      canonicalEndPath p.length β := by
  apply graphWeightMatrix_submatrix_canonicalEnd G weight (shortestWalkGraphEmbedding p hp) β
  · change weight (walkVertexMap p 0) = β
    rw [walkVertexMap_zero]
    exact hfirst
  · intro i hi
    change weight (p.getVert i.val) = 2
    have h0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    exact hrest i.val (by omega) (by have := i.isLt; omega)

end KltDP.LinearAlgebra
