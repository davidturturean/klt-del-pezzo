import KltDP.LinearAlgebra.TenForestModelRealization
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Actual matrices and sources under a marked weighted graph isomorphism

The generic lemmas reuse Mathlib's determinant, inverse, matrix-vector,
and dot-product reindexing theorems. The selected-row theorem applies them
to the actual isomorphism constructed from the classified forest. No
matrix equality or equality of Green invariants is assumed.
-/

noncomputable section

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

section Generic

variable {I J 𝕜 : Type*} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] [Field 𝕜]
  {G : SimpleGraph I} {H : SimpleGraph J}
  [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- The actual weighted graph matrix transports along a weight-preserving
graph isomorphism. -/
theorem weightedGraphIso_matrix (e : G ≃g H) (u : I → 𝕜) (w : J → 𝕜)
    (hw : ∀ i, w (e i) = u i) :
    (graphWeightMatrix H w).submatrix e e = graphWeightMatrix G u := by
  calc
    (graphWeightMatrix H w).submatrix e e = graphWeightMatrix G (w ∘ e) := by
      simpa only [SimpleGraph.Iso.toEmbedding, RelIso.coe_toRelEmbedding] using
        graphWeightMatrix_submatrix e.toEmbedding w
    _ = graphWeightMatrix G u := congrArg (graphWeightMatrix G) (funext hw)

/-- The determinant is preserved by the actual graph isomorphism. -/
theorem weightedGraphIso_det (e : G ≃g H) (u : I → 𝕜) (w : J → 𝕜)
    (hw : ∀ i, w (e i) = u i) :
    (graphWeightMatrix G u).det = (graphWeightMatrix H w).det := by
  rw [← weightedGraphIso_matrix e u w hw]
  exact Matrix.det_submatrix_equiv_self e.toEquiv (graphWeightMatrix H w)

/-- The full inverse transports without an extra nonsingularity premise;
Mathlib's inverse reindexing theorem also covers singular matrices. -/
theorem weightedGraphIso_inverse (e : G ≃g H) (u : I → 𝕜) (w : J → 𝕜)
    (hw : ∀ i, w (e i) = u i) :
    (graphWeightMatrix G u)⁻¹ = (graphWeightMatrix H w)⁻¹.submatrix e e := by
  rw [← weightedGraphIso_matrix e u w hw]
  exact Matrix.inv_submatrix_equiv (graphWeightMatrix H w) e.toEquiv e.toEquiv

/-- An arbitrary actual inverse-source vector transports coordinatewise. -/
theorem weightedGraphIso_inverse_mulVec (e : G ≃g H) (u : I → 𝕜) (w : J → 𝕜)
    (hw : ∀ i, w (e i) = u i) (source : J → 𝕜) :
    (graphWeightMatrix G u)⁻¹ *ᵥ (source ∘ e) =
      ((graphWeightMatrix H w)⁻¹ *ᵥ source) ∘ e := by
  rw [weightedGraphIso_inverse e u w hw]
  have hcomp : (source ∘ e) ∘ e.toEquiv.symm = source := by
    funext j
    change source (e.toEquiv (e.toEquiv.symm j)) = source j
    exact congrArg source (e.toEquiv.apply_symm_apply j)
  simpa only [hcomp] using Matrix.submatrix_mulVec_equiv
    (graphWeightMatrix H w)⁻¹ (source ∘ e) e e.toEquiv

/-- Bilinear Green pairings are unchanged under the same actual map. -/
theorem weightedGraphIso_green_pairing (e : G ≃g H) (u : I → 𝕜) (w : J → 𝕜)
    (hw : ∀ i, w (e i) = u i) (left right : J → 𝕜) :
    dotProduct (left ∘ e) ((graphWeightMatrix G u)⁻¹ *ᵥ (right ∘ e)) =
      dotProduct left ((graphWeightMatrix H w)⁻¹ *ᵥ right) := by
  rw [weightedGraphIso_inverse_mulVec e u w hw]
  exact comp_equiv_dotProduct_comp_equiv left
    ((graphWeightMatrix H w)⁻¹ *ᵥ right) e.toEquiv

/-- The three actual marked source contributions are transported by an
equivalence, including their multiplicities if some labels coincide. -/
theorem threeMarkedSource_comp_equiv (e : I ≃ J) (C B D : I) :
    (threeMarkedSource (e C) (e B) (e D) : J → 𝕜) ∘ e =
      threeMarkedSource C B D := by
  funext i
  simp only [Function.comp_apply, threeMarkedSource, Pi.add_apply,
    Pi.single_apply, e.injective.eq_iff]

end Generic

namespace TenForestRow

/-- The actual rational weighted matrix of the named row model. -/
def modelMatrix (row : TenForestRow) : Matrix row.ModelVertex row.ModelVertex ℚ := by
  classical
  exact graphWeightMatrix row.modelGraph (fun v => (row.modelWeight v : ℚ))

/-- The actual diagonal-minus-two source of the row model. -/
def modelCanonicalSource (row : TenForestRow) : row.ModelVertex → ℚ :=
  fun v => (row.modelWeight v : ℚ) - 2

/-- The actual source at the three specified model vertices. -/
def modelMarkedSource (row : TenForestRow) : row.ModelVertex → ℚ :=
  threeMarkedSource row.modelC row.modelB row.modelD

end TenForestRow

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The selected row's marked weighted isomorphism also identifies the
actual matrix, inverse, canonical inverse-source vector, marked source,
determinant and marked Green energy with that same row's model. -/
theorem TenForestRow.Realized.matrix_realization
    {row : TenForestRow} {G : SimpleGraph V} [DecidableRel G.Adj]
    {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ}
    (h : row.Realized G weight coeff C B D β)
    (hcard : Fintype.card V = β + 7)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = β) (hBD : B ≠ D) :
    let A := graphWeightMatrix G (fun v => (weight v : ℚ))
    let q := fun v => (weight v : ℚ) - 2
    let p : V → ℚ := threeMarkedSource C B D
    ∃ f : row.modelGraph ≃g G,
      f row.modelC = C ∧ f row.modelB = B ∧ f row.modelD = D ∧
      (∀ v, weight (f v) = row.modelWeight v) ∧
      A.submatrix f f = row.modelMatrix ∧
      A⁻¹.submatrix f f = row.modelMatrix⁻¹ ∧
      (A⁻¹ *ᵥ q) ∘ f = row.modelMatrix⁻¹ *ᵥ row.modelCanonicalSource ∧
      p ∘ f = row.modelMarkedSource ∧
      A.det = row.modelMatrix.det ∧
      dotProduct p (A⁻¹ *ᵥ p) =
        dotProduct row.modelMarkedSource (row.modelMatrix⁻¹ *ᵥ row.modelMarkedSource) := by
  classical
  dsimp only
  obtain ⟨f, hfC, hfB, hfD, hw⟩ := h.weighted_graph_iso hcard hC hB hD hBD
  have hwq : ∀ v, (weight (f v) : ℚ) = (row.modelWeight v : ℚ) := by
    intro v
    exact congrArg (fun n : ℕ => (n : ℚ)) (hw v)
  have hq : (fun v => (weight v : ℚ) - 2) ∘ f = row.modelCanonicalSource := by
    funext v
    exact congrArg (fun x : ℚ => x - 2) (hwq v)
  have hp : (threeMarkedSource C B D : V → ℚ) ∘ f = row.modelMarkedSource := by
    rw [← hfC, ← hfB, ← hfD]
    exact threeMarkedSource_comp_equiv f.toEquiv row.modelC row.modelB row.modelD
  have hm := weightedGraphIso_matrix f (fun v => (row.modelWeight v : ℚ))
    (fun v => (weight v : ℚ)) hwq
  have hi := weightedGraphIso_inverse f (fun v => (row.modelWeight v : ℚ))
    (fun v => (weight v : ℚ)) hwq
  have hc := weightedGraphIso_inverse_mulVec f (fun v => (row.modelWeight v : ℚ))
    (fun v => (weight v : ℚ)) hwq (fun v => (weight v : ℚ) - 2)
  have hd := weightedGraphIso_det f (fun v => (row.modelWeight v : ℚ))
    (fun v => (weight v : ℚ)) hwq
  have hg := weightedGraphIso_green_pairing f (fun v => (row.modelWeight v : ℚ))
    (fun v => (weight v : ℚ)) hwq (threeMarkedSource C B D) (threeMarkedSource C B D)
  rw [hq] at hc
  rw [hp] at hg
  exact ⟨f, hfC, hfB, hfD, hw, hm, hi.symm, hc.symm, hp, hd.symm, hg.symm⟩

end KltDP.LinearAlgebra
