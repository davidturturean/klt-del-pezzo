import KltDP.LinearAlgebra.WeightedPathTransport
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-!
# Determinant decomposition of an actual graph with isolated complement

An injectively indexed set of actual graph vertices carries every edge.
The complementary vertices therefore give a diagonal block, and the full
determinant is the determinant of the actual principal block times the
product of the actual complementary weights.

This module derives the matrix block decomposition from actual adjacency.
It does not assume a graph fixture or a determinant certificate.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V I 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Field 𝕜]

/-- Actual graph vertices outside an injectively indexed subset. -/
def outsideRange (e : I ↪ V) : Finset V :=
  Finset.univ \ Finset.univ.image e

omit [DecidableEq I] in
@[simp]
theorem mem_outsideRange (e : I ↪ V) (v : V) :
    v ∈ outsideRange e ↔ v ∉ Set.range e := by
  simp only [outsideRange, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image, Set.mem_range, exists_prop]

omit [DecidableEq I] in
/-- The complement cardinality is derived from injectivity, including empty
index types and the case when every graph vertex is indexed. -/
theorem card_outsideRange (e : I ↪ V) :
    (outsideRange e).card = Fintype.card V - Fintype.card I := by
  rw [outsideRange, Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ,
    Finset.card_image_of_injective _ e.injective, Finset.card_univ]

/-- Splitting the actual weighted graph determinant at an injectively
indexed block, when every actual vertex outside it is isolated. -/
theorem graph_det_eq_principal_mul_complement
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜)
    (e : I ↪ V) (hisolated : ∀ v, v ∉ Set.range e → ∀ u, ¬ G.Adj v u) :
    (graphWeightMatrix G weight).det =
      ((graphWeightMatrix G weight).submatrix e e).det *
        ∏ v ∈ outsideRange e, weight v := by
  classical
  letI : Fintype {v // v ∈ Set.range e} :=
    Subtype.fintype (fun v => v ∈ Set.range e)
  let A := graphWeightMatrix G weight
  let E := Equiv.ofInjective e e.injective
  have hcross : ∀ i, i ∉ Set.range e → ∀ j, j ∈ Set.range e → A i j = 0 := by
    intro i hi j hj
    have hij : i ≠ j := by intro h; subst j; exact hi hj
    change graphWeightMatrix G weight i j = 0
    rw [graphWeightMatrix_apply, if_neg hij, if_neg (hisolated i hi j)]
  have hblock :
      (A.toSquareBlockProp (fun v => v ∈ Set.range e)).submatrix E E = A.submatrix e e := by
    ext i j
    rfl
  have hblockdet : (A.toSquareBlockProp (fun v => v ∈ Set.range e)).det =
      (A.submatrix e e).det := by
    rw [← hblock, Matrix.det_submatrix_equiv_self]
  have hdiag : A.toSquareBlockProp (fun v => v ∉ Set.range e) =
      Matrix.diagonal (fun v : {v // v ∉ Set.range e} => weight v) := by
    ext i j
    by_cases hij : i = j
    · subst j
      change graphWeightMatrix G weight i.val i.val = _
      simp only [graphWeightMatrix_diagonal, Matrix.diagonal_apply_eq]
    · have hval : i.val ≠ j.val := by intro h; exact hij (Subtype.ext h)
      change graphWeightMatrix G weight i.val j.val = _
      rw [graphWeightMatrix_apply, if_neg hval,
        if_neg (hisolated i.val i.property j.val), Matrix.diagonal_apply_ne _ hij]
  have hcomplement : (A.toSquareBlockProp (fun v => v ∉ Set.range e)).det =
      ∏ v ∈ outsideRange e, weight v := by
    rw [hdiag, Matrix.det_diagonal]
    exact (Finset.prod_subtype (outsideRange e) (mem_outsideRange e) weight).symm
  exact (Matrix.twoBlockTriangular_det A (fun v => v ∈ Set.range e) hcross).trans
    (congrArg₂ (fun x y : 𝕜 => x * y) hblockdet hcomplement)

omit [Fintype V] [Fintype I] [DecidableEq I] in
/-- The actual finite product with two distinguished weights and weight two
everywhere else. The exponent is the proved number of remaining vertices. -/
theorem prod_weights_two_exceptions (S : Finset V) (weight : V → 𝕜)
    (B D : V) (hBD : B ≠ D) (hB : B ∈ S) (hD : D ∈ S)
    (hother : ∀ i ∈ S, i ≠ B → i ≠ D → weight i = 2) :
    (∏ i ∈ S, weight i) = weight B * weight D * 2 ^ (S.card - 2) := by
  have hD' : D ∈ S.erase B := by simp [hD, Ne.symm hBD]
  have hfirst := Finset.prod_erase_mul S weight hB
  have hsecond := Finset.prod_erase_mul (S.erase B) weight hD'
  have hrest : (∏ i ∈ (S.erase B).erase D, weight i) =
      (2 : 𝕜) ^ ((S.erase B).erase D).card := by
    calc
      _ = ∏ _i ∈ (S.erase B).erase D, (2 : 𝕜) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hiD := (Finset.mem_erase.mp hi).1
        have hiB := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        have hiS := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2
        exact hother i hiS hiB hiD
      _ = _ := by simp
  have hcard : ((S.erase B).erase D).card = S.card - 2 := by
    rw [Finset.card_erase_of_mem hD', Finset.card_erase_of_mem hB]
    omega
  rw [hcard] at hrest
  rw [← hfirst, ← hsecond, hrest]
  ring

end KltDP.LinearAlgebra
