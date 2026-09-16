import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# Decreasing increments along a finite path

These results formalize the discrete-concavity argument in manuscript §9.
The input is an actual finite vector, with a canonical leaf row and actual
interior row equations whose side terms are nonnegative. The endpoint bound
is derived using Mathlib's finite antitone criterion and telescoping sums.

No matrix identity or side-branch geometry is encoded as a desired endpoint
bound. Applications must establish the displayed coordinate equations.
-/

namespace KltDP.LinearAlgebra

open scoped BigOperators

variable {𝕜 : Type*} [Field 𝕜]

/-- Consecutive differences of an actual finite path vector. -/
def pathIncrement {d : ℕ} (x : Fin (d + 1) → 𝕜) : Fin d → 𝕜 :=
  fun i => x i.succ - x i.castSucc

/-- Finite telescoping, directly reusing Mathlib's first/last decompositions
of the sum over `Fin`. The one-vertex path is included. -/
theorem sum_pathIncrement {d : ℕ} (x : Fin (d + 1) → 𝕜) :
    ∑ i, pathIncrement x i = x (Fin.last d) - x 0 := by
  simp only [pathIncrement, Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ x
  have hlast := Fin.sum_univ_castSucc x
  linear_combination hlast - hfirst

section Ordered

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Nonnegative terms in the interior canonical row equations make the
increments antitone. There are `n+1` edges and `n` interior vertices. -/
theorem pathIncrement_antitone_of_rows {n : ℕ} (x : Fin (n + 2) → 𝕜)
    (branch : Fin n → 𝕜) (hbranch : ∀ i, 0 ≤ branch i)
    (hrows : ∀ i : Fin n,
      2 * x i.castSucc.succ - x i.castSucc.castSucc - x i.succ.succ = branch i) :
    Antitone (pathIncrement x) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  change x i.succ.succ - x i.succ.castSucc ≤
    x i.castSucc.succ - x i.castSucc.castSucc
  have hmiddle : i.succ.castSucc = i.castSucc.succ := rfl
  rw [hmiddle]
  have hrow := hrows i
  have hnonneg := hbranch i
  linarith

/-- A canonical leaf inequality bounds the first increment by the leaf
coefficient; antitonicity then bounds every increment by it. -/
theorem pathIncrement_le_leaf {n : ℕ} (x : Fin (n + 2) → 𝕜)
    (hanti : Antitone (pathIncrement x))
    (hleaf : x (0 : Fin (n + 1)).succ ≤ 2 * x 0) :
    ∀ i, pathIncrement x i ≤ x 0 := by
  intro i
  have hi : pathIncrement x i ≤ pathIncrement x 0 := hanti (Fin.zero_le i)
  have hfirst : pathIncrement x 0 ≤ x 0 := by
    change x (0 : Fin (n + 1)).succ - x 0 ≤ x 0
    linarith
  exact hi.trans hfirst

/-- For a path of `n+1` edges, decreasing increments and the leaf inequality
give the endpoint bound `(n+2)*x₀`. The leaf coefficient need not be nonnegative. -/
theorem path_endpoint_le_of_antitone {n : ℕ} (x : Fin (n + 2) → 𝕜)
    (hanti : Antitone (pathIncrement x))
    (hleaf : x (0 : Fin (n + 1)).succ ≤ 2 * x 0) :
    x (Fin.last (n + 1)) ≤ ((n + 2 : ℕ) : 𝕜) * x 0 := by
  have hinc := pathIncrement_le_leaf x hanti hleaf
  have hsum : ∑ i, pathIncrement x i ≤ ((n + 1 : ℕ) : 𝕜) * x 0 := by
    calc
      _ ≤ ∑ _i : Fin (n + 1), x 0 := Finset.sum_le_sum (fun i _ => hinc i)
      _ = _ := by simp [nsmul_eq_mul]
  rw [sum_pathIncrement] at hsum
  calc
    x (Fin.last (n + 1)) = (x (Fin.last (n + 1)) - x 0) + x 0 := by ring
    _ ≤ ((n + 1 : ℕ) : 𝕜) * x 0 + x 0 := add_le_add_right hsum (x 0)
    _ = ((n + 2 : ℕ) : 𝕜) * x 0 := by push_cast; ring

/-- The full coordinate-equation version: a nonnegative leaf-side term and
nonnegative interior side terms imply the endpoint bound. In the source's
actual leaf case the leaf-side term is zero. -/
theorem path_endpoint_le_of_branch_rows {n : ℕ} (x : Fin (n + 2) → 𝕜)
    (leafBranch : 𝕜) (branch : Fin n → 𝕜)
    (hleafBranch : 0 ≤ leafBranch) (hbranch : ∀ i, 0 ≤ branch i)
    (hleaf : 2 * x 0 - x (0 : Fin (n + 1)).succ = leafBranch)
    (hrows : ∀ i : Fin n,
      2 * x i.castSucc.succ - x i.castSucc.castSucc - x i.succ.succ = branch i) :
    x (Fin.last (n + 1)) ≤ ((n + 2 : ℕ) : 𝕜) * x 0 := by
  apply path_endpoint_le_of_antitone x (pathIncrement_antitone_of_rows x branch hbranch hrows)
  linarith

/-- Side terms can be the actual finite weighted sums of nonnegative branch
coefficients. Their required nonnegativity is proved from those sums. -/
theorem path_endpoint_le_of_nonnegative_side_sums {n : ℕ} {B : Type*} [Fintype B]
    (x : Fin (n + 2) → 𝕜) (sideCoeff : B → 𝕜)
    (leafWeight : B → 𝕜) (sideWeight : Fin n → B → 𝕜)
    (hcoeff : ∀ b, 0 ≤ sideCoeff b) (hleafWeight : ∀ b, 0 ≤ leafWeight b)
    (hsideWeight : ∀ i b, 0 ≤ sideWeight i b)
    (hleaf : 2 * x 0 - x (0 : Fin (n + 1)).succ =
      ∑ b, leafWeight b * sideCoeff b)
    (hrows : ∀ i : Fin n,
      2 * x i.castSucc.succ - x i.castSucc.castSucc - x i.succ.succ =
        ∑ b, sideWeight i b * sideCoeff b) :
    x (Fin.last (n + 1)) ≤ ((n + 2 : ℕ) : 𝕜) * x 0 := by
  apply path_endpoint_le_of_branch_rows x (∑ b, leafWeight b * sideCoeff b)
    (fun i => ∑ b, sideWeight i b * sideCoeff b) ?_ ?_ hleaf hrows
  · exact Finset.sum_nonneg (fun b _ => mul_nonneg (hleafWeight b) (hcoeff b))
  · intro i
    exact Finset.sum_nonneg (fun b _ => mul_nonneg (hsideWeight i b) (hcoeff b))

/-- The source's `λ_T ≤ 4 λ_C` consequence for at most three edges.
Nonnegativity of the leaf coefficient is needed only for this last comparison
of the two multiplicative constants. -/
theorem path_endpoint_le_four_mul_leaf {n : ℕ} (x : Fin (n + 2) → 𝕜)
    (hn : n ≤ 2) (hx : 0 ≤ x 0) (leafBranch : 𝕜) (branch : Fin n → 𝕜)
    (hleafBranch : 0 ≤ leafBranch) (hbranch : ∀ i, 0 ≤ branch i)
    (hleaf : 2 * x 0 - x (0 : Fin (n + 1)).succ = leafBranch)
    (hrows : ∀ i : Fin n,
      2 * x i.castSucc.succ - x i.castSucc.castSucc - x i.succ.succ = branch i) :
    x (Fin.last (n + 1)) ≤ 4 * x 0 := by
  have hbound := path_endpoint_le_of_branch_rows x leafBranch branch
    hleafBranch hbranch hleaf hrows
  have hlength : ((n + 2 : ℕ) : 𝕜) ≤ 4 := by
    exact_mod_cast (show n + 2 ≤ 4 by omega)
  exact hbound.trans (mul_le_mul_of_nonneg_right hlength hx)

omit [IsStrictOrderedRing 𝕜] in
/-- The degenerate path has one vertex and satisfies the same length rule
with coefficient one, without row hypotheses. -/
theorem path_endpoint_zero (x : Fin 1 → 𝕜) : x (Fin.last 0) ≤ 1 * x 0 := by
  simp

end Ordered

end KltDP.LinearAlgebra
