import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

/-!
# Integral intersection calculations for the Frobenius construction

The lattice is the actual free integer module `ℤ × ℤ × (ι → ℤ)` with
the hyperbolic pairing on the first two coordinates and the negative
standard pairing on the exceptional coordinates. No matrix entries or
intersection conclusions are supplied as data fields.

The vectors below are the total-transform coordinate formulas of the frozen
manuscript, Proposition 10.1. These calculations do not construct a surface,
its Picard group, or any curves. A geometric adapter must identify the actual
integral Picard basis and its pairing with this explicitly defined lattice.
All subtraction in intersection-number formulas is performed after casting
to `ℤ`. The terminal index uses the natural predecessor under `0 < p`.
-/

namespace KltDP.Examples.FrobeniusPicard

open scoped BigOperators

/-- A hyperbolic plane and one negative integral coordinate for each blowup. -/
abbrev BlowupLattice (ι : Type*) := ℤ × ℤ × (ι → ℤ)

section Lattice

variable {ι : Type*} [Fintype ι]

/-- The intersection form in the total-transform basis. -/
def pairing (x y : BlowupLattice ι) : ℤ :=
  x.1 * y.2.1 + x.2.1 * y.1 - ∑ i, x.2.2 i * y.2.2 i

theorem pairing_comm (x y : BlowupLattice ι) : pairing x y = pairing y x := by
  simp [pairing, mul_comm, add_comm]

theorem pairing_add_left (x y z : BlowupLattice ι) :
    pairing (x + y) z = pairing x z + pairing y z := by
  simp [pairing, add_mul, Finset.sum_add_distrib]
  ring

theorem pairing_smul_left (r : ℤ) (x y : BlowupLattice ι) :
    pairing (r • x) y = r * pairing x y := by
  simp [pairing, smul_eq_mul, mul_assoc, Finset.mul_sum, mul_add, mul_sub]

theorem pairing_add_right (x y z : BlowupLattice ι) :
    pairing x (y + z) = pairing x y + pairing x z := by
  rw [pairing_comm x, pairing_add_left, pairing_comm y, pairing_comm z]

theorem pairing_smul_right (r : ℤ) (x y : BlowupLattice ι) :
    pairing x (r • y) = r * pairing x y := by
  rw [pairing_comm x, pairing_smul_left, pairing_comm y]

theorem pairing_sub_left (x y z : BlowupLattice ι) :
    pairing (x - y) z = pairing x z - pairing y z := by
  simp [pairing, sub_mul, Finset.sum_sub_distrib]
  ring

theorem pairing_sub_right (x y z : BlowupLattice ι) :
    pairing x (y - z) = pairing x y - pairing x z := by
  rw [pairing_comm x, pairing_sub_left, pairing_comm y, pairing_comm z]

/-- The same explicitly computed form, bundled for reuse in linear algebra. -/
def intersectionForm : LinearMap.BilinForm ℤ (BlowupLattice ι) :=
  LinearMap.mk₂ ℤ pairing pairing_add_left
    (fun r x y => by simpa only [smul_eq_mul] using pairing_smul_left r x y)
    pairing_add_right (fun r x y => by simpa only [smul_eq_mul] using pairing_smul_right r x y)

def a : BlowupLattice ι := (1, 0, 0)

def b : BlowupLattice ι := (0, 1, 0)

@[simp] theorem pairing_a_left (x : BlowupLattice ι) : pairing a x = x.2.1 := by
  simp [pairing, a]

@[simp] theorem pairing_b_left (x : BlowupLattice ι) : pairing b x = x.1 := by
  simp [pairing, b]

variable [DecidableEq ι]

def exceptional (i : ι) : BlowupLattice ι :=
  (0, 0, fun j => if j = i then 1 else 0)

@[simp] theorem pairing_exceptional_left (i : ι) (x : BlowupLattice ι) :
    pairing (exceptional i) x = -x.2.2 i := by
  simp [pairing, exceptional, ite_mul]

@[simp] theorem pairing_exceptional (i j : ι) :
    pairing (exceptional i) (exceptional j) = if i = j then -1 else 0 := by
  rw [pairing_exceptional_left]
  by_cases hij : i = j <;> simp [exceptional, hij]

@[simp] theorem exceptional_square (i : ι) :
    pairing (exceptional i) (exceptional i) = -1 := by
  rw [pairing_exceptional]
  simp

/-- Differences of exceptional total transforms, prior to choosing chain labels. -/
def exceptionalDifference (i j : ι) : BlowupLattice ι := exceptional i - exceptional j

theorem pairing_difference_left (i j : ι) (x : BlowupLattice ι) :
    pairing (exceptionalDifference i j) x = -x.2.2 i + x.2.2 j := by
  simp [exceptionalDifference, pairing_sub_left]

theorem difference_square (i j : ι) (hij : i ≠ j) :
    pairing (exceptionalDifference i j) (exceptionalDifference i j) = -2 := by
  simp only [exceptionalDifference, pairing_sub_left, pairing_sub_right, pairing_exceptional]
  simp [hij, hij.symm]

/-- Complete incidence formula for any two exceptional differences. -/
theorem pairing_differences (i j k l : ι) :
    pairing (exceptionalDifference i j) (exceptionalDifference k l) =
      (if i = k then -1 else 0) - (if i = l then -1 else 0) -
        (if j = k then -1 else 0) + (if j = l then -1 else 0) := by
  simp only [exceptionalDifference, pairing_sub_left, pairing_sub_right, pairing_exceptional]
  ring

/-- The actual integral basis of the hyperbolic plane and exceptional coordinates. -/
noncomputable def integralBasis :
    Basis (Unit ⊕ (Unit ⊕ ι)) ℤ (BlowupLattice ι) :=
  (Basis.singleton Unit ℤ).prod
    ((Basis.singleton Unit ℤ).prod (Pi.basisFun ℤ ι))

omit [DecidableEq ι] in
@[simp] theorem integralBasis_a :
    integralBasis (Sum.inl ()) = (a : BlowupLattice ι) := by
  simp [integralBasis, a]

omit [DecidableEq ι] in
@[simp] theorem integralBasis_b :
    integralBasis (Sum.inr (Sum.inl ())) = (b : BlowupLattice ι) := by
  simp [integralBasis, b]

@[simp] theorem integralBasis_exceptional (i : ι) :
    integralBasis (Sum.inr (Sum.inr i)) = exceptional i := by
  ext j <;> simp [integralBasis, exceptional, Pi.single_apply]

omit [DecidableEq ι] in
theorem lattice_rank :
    Module.finrank ℤ (BlowupLattice ι) = 2 + Fintype.card ι := by
  rw [Module.finrank_eq_card_basis integralBasis]
  simp only [Fintype.card_sum, Fintype.card_unit]
  omega

end Lattice

abbrev PicardVector (p n : ℕ) := BlowupLattice (Fin n × Fin p)

/-- `B = pa + b - Σ Eᵢⱼ`, written in integral coordinates. -/
def graphVector (p n : ℕ) : PicardVector p n := (p, 1, fun _ => -1)

/-- `Fᵢ = b - Σⱼ Eᵢⱼ`. -/
def fiberVector (p n : ℕ) (i : Fin n) : PicardVector p n :=
  (0, 1, fun k => if k.1 = i then -1 else 0)

/-- The canonical class `-2a - 2b + Σ Eᵢⱼ`. -/
def canonicalVector (p n : ℕ) : PicardVector p n := (-2, -2, fun _ => 1)

/-- The integral candidate `M = B + (n-2)b`, including every sign case. -/
def nefVector (p n : ℕ) : PicardVector p n := (p, (n : ℤ) - 1, fun _ => -1)

theorem nefVector_eq_graph_add (p n : ℕ) :
    nefVector p n = graphVector p n + ((n : ℤ) - 2) • b := by
  ext k <;> simp [nefVector, graphVector, b, smul_eq_mul]
  ring

/-- Arbitrary-vector graph intersection, so subsequent calculations are evaluations. -/
theorem pairing_graph_left (p n : ℕ) (x : PicardVector p n) :
    pairing (graphVector p n) x =
      (p : ℤ) * x.2.1 + x.1 + ∑ i, ∑ j, x.2.2 (i, j) := by
  simp [pairing, graphVector, Fintype.sum_prod_type]

theorem pairing_fiber_left (p n : ℕ) (i : Fin n) (x : PicardVector p n) :
    pairing (fiberVector p n i) x = x.1 + ∑ j, x.2.2 (i, j) := by
  simp [pairing, fiberVector, Fintype.sum_prod_type, ite_mul]
  rw [Finset.sum_comm]
  simp

theorem pairing_canonical_left (p n : ℕ) (x : PicardVector p n) :
    pairing (canonicalVector p n) x =
      -2 * x.2.1 - 2 * x.1 - ∑ i, ∑ j, x.2.2 (i, j) := by
  simp [pairing, canonicalVector, Fintype.sum_prod_type]
  ring

theorem pairing_nef_left (p n : ℕ) (x : PicardVector p n) :
    pairing (nefVector p n) x =
      (p : ℤ) * x.2.1 + ((n : ℤ) - 1) * x.1 + ∑ i, ∑ j, x.2.2 (i, j) := by
  simp [pairing, nefVector, Fintype.sum_prod_type]

theorem graph_square (p n : ℕ) :
    pairing (graphVector p n) (graphVector p n) = -(p : ℤ) * ((n : ℤ) - 2) := by
  rw [pairing_graph_left]
  simp [graphVector]
  ring

theorem fiber_square (p n : ℕ) (i : Fin n) :
    pairing (fiberVector p n i) (fiberVector p n i) = -(p : ℤ) := by
  rw [pairing_fiber_left]
  simp [fiberVector]

theorem pairing_fibers (p n : ℕ) (i j : Fin n) :
    pairing (fiberVector p n i) (fiberVector p n j) =
      if i = j then -(p : ℤ) else 0 := by
  rw [pairing_fiber_left]
  by_cases hij : i = j <;> simp [fiberVector, hij]

theorem pairing_graph_fiber (p n : ℕ) (i : Fin n) :
    pairing (graphVector p n) (fiberVector p n i) = 0 := by
  rw [pairing_comm, pairing_fiber_left]
  simp [graphVector]

theorem canonical_square (p n : ℕ) :
    pairing (canonicalVector p n) (canonicalVector p n) = 8 - (n : ℤ) * p := by
  rw [pairing_canonical_left]
  simp [canonicalVector]

theorem pairing_canonical_graph (p n : ℕ) :
    pairing (canonicalVector p n) (graphVector p n) =
      (p : ℤ) * ((n : ℤ) - 2) - 2 := by
  rw [pairing_canonical_left]
  simp [graphVector]
  ring

theorem pairing_canonical_fiber (p n : ℕ) (i : Fin n) :
    pairing (canonicalVector p n) (fiberVector p n i) = (p : ℤ) - 2 := by
  rw [pairing_comm, pairing_fiber_left]
  simp [canonicalVector]
  ring

theorem nef_square (p n : ℕ) :
    pairing (nefVector p n) (nefVector p n) = (p : ℤ) * ((n : ℤ) - 2) := by
  rw [pairing_nef_left]
  simp [nefVector]
  ring

theorem pairing_nef_graph (p n : ℕ) :
    pairing (nefVector p n) (graphVector p n) = 0 := by
  rw [pairing_nef_left]
  simp [graphVector]
  ring

theorem pairing_nef_fiber (p n : ℕ) (i : Fin n) :
    pairing (nefVector p n) (fiberVector p n i) = 0 := by
  rw [pairing_comm, pairing_fiber_left]
  simp [nefVector]

theorem pairing_graph_exceptional (p n : ℕ) (i : Fin n) (j : Fin p) :
    pairing (graphVector p n) (exceptional (i, j)) = 1 := by
  rw [pairing_comm, pairing_exceptional_left]
  simp [graphVector]

theorem pairing_nef_exceptional (p n : ℕ) (i : Fin n) (j : Fin p) :
    pairing (nefVector p n) (exceptional (i, j)) = 1 := by
  rw [pairing_comm, pairing_exceptional_left]
  simp [nefVector]

theorem pairing_canonical_exceptional (p n : ℕ) (i : Fin n) (j : Fin p) :
    pairing (canonicalVector p n) (exceptional (i, j)) = -1 := by
  rw [pairing_comm, pairing_exceptional_left]
  simp [canonicalVector]

theorem pairing_fiber_exceptional (p n : ℕ) (i k : Fin n) (j : Fin p) :
    pairing (fiberVector p n i) (exceptional (k, j)) = if k = i then 1 else 0 := by
  rw [pairing_comm, pairing_exceptional_left]
  by_cases hki : k = i <;> simp [fiberVector, hki]

/-- Adjacent total-transform differences; coordinates are numbered from zero in Lean. -/
def chainVector (p n : ℕ) (i : Fin n) (j : Fin p) (hj : j.val + 1 < p) :
    PicardVector p n :=
  exceptionalDifference (i, j) (i, ⟨j.val + 1, hj⟩)

theorem chain_square (p n : ℕ) (i : Fin n) (j : Fin p) (hj : j.val + 1 < p) :
    pairing (chainVector p n i j hj) (chainVector p n i j hj) = -2 := by
  apply difference_square
  intro heq
  have hval := congrArg (fun k : Fin n × Fin p => k.2.val) heq
  simp only at hval
  omega

theorem pairing_chain_graph (p n : ℕ) (i : Fin n) (j : Fin p) (hj : j.val + 1 < p) :
    pairing (chainVector p n i j hj) (graphVector p n) = 0 := by
  simp [chainVector, pairing_difference_left, graphVector]

theorem pairing_chain_fiber (p n : ℕ) (i k : Fin n) (j : Fin p)
    (hj : j.val + 1 < p) :
    pairing (chainVector p n i j hj) (fiberVector p n k) = 0 := by
  simp [chainVector, pairing_difference_left, fiberVector]

theorem pairing_chain_nef (p n : ℕ) (i : Fin n) (j : Fin p) (hj : j.val + 1 < p) :
    pairing (chainVector p n i j hj) (nefVector p n) = 0 := by
  simp [chainVector, pairing_difference_left, nefVector]

theorem pairing_chain_canonical (p n : ℕ) (i : Fin n) (j : Fin p)
    (hj : j.val + 1 < p) :
    pairing (chainVector p n i j hj) (canonicalVector p n) = 0 := by
  simp [chainVector, pairing_difference_left, canonicalVector]

/-- Every pair of chain components, including disjoint clusters and nonadjacent vertices. -/
theorem pairing_chains (p n : ℕ) (i k : Fin n) (j l : Fin p)
    (hj : j.val + 1 < p) (hl : l.val + 1 < p) :
    pairing (chainVector p n i j hj) (chainVector p n k l hl) =
      if i = k then
        if j = l then -2 else if j.val + 1 = l.val ∨ l.val + 1 = j.val then 1 else 0
      else 0 := by
  simp only [chainVector, pairing_differences, Prod.mk.injEq, Fin.ext_iff]
  split_ifs <;> omega

def lastIndex (p : ℕ) (hp : 0 < p) : Fin p := ⟨p - 1, by omega⟩

/-- The last exceptional total transform, corresponding to the source's `Pᵢ`. -/
def lastVector (p n : ℕ) (hp : 0 < p) (i : Fin n) : PicardVector p n :=
  exceptional (i, lastIndex p hp)

theorem pairing_chain_last (p n : ℕ) (hp : 0 < p) (i k : Fin n) (j : Fin p)
    (hj : j.val + 1 < p) :
    pairing (chainVector p n i j hj) (lastVector p n hp k) =
      if i = k ∧ j.val + 2 = p then 1 else 0 := by
  simp only [chainVector, lastVector, exceptionalDifference, pairing_sub_left,
    pairing_exceptional, Prod.mk.injEq, Fin.ext_iff, lastIndex]
  split_ifs <;> omega

@[simp] theorem last_square (p n : ℕ) (hp : 0 < p) (i : Fin n) :
    pairing (lastVector p n hp i) (lastVector p n hp i) = -1 := by
  exact exceptional_square _

theorem pairing_graph_last (p n : ℕ) (hp : 0 < p) (i : Fin n) :
    pairing (graphVector p n) (lastVector p n hp i) = 1 := by
  exact pairing_graph_exceptional p n i (lastIndex p hp)

theorem pairing_fiber_last (p n : ℕ) (hp : 0 < p) (i k : Fin n) :
    pairing (fiberVector p n i) (lastVector p n hp k) = if k = i then 1 else 0 := by
  exact pairing_fiber_exceptional p n i k (lastIndex p hp)

theorem pairing_nef_last (p n : ℕ) (hp : 0 < p) (i : Fin n) :
    pairing (nefVector p n) (lastVector p n hp i) = 1 := by
  exact pairing_nef_exceptional p n i (lastIndex p hp)

/-- At characteristic-two cluster length, the remaining chain component. -/
def nodeVector (n : ℕ) (i : Fin n) : PicardVector 2 n :=
  exceptionalDifference (i, (0 : Fin 2)) (i, (1 : Fin 2))

def lastVectorTwo (n : ℕ) (i : Fin n) : PicardVector 2 n :=
  exceptional (i, (1 : Fin 2))

/-- The integral identity between the two node classes and the last exceptional class. -/
theorem fiber_add_node (n : ℕ) (i : Fin n) :
    fiberVector 2 n i + nodeVector n i = b - (2 : ℤ) • lastVectorTwo n i := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [fiberVector, nodeVector, exceptionalDifference, exceptional, b, lastVectorTwo]
  · simp [fiberVector, nodeVector, exceptionalDifference, exceptional, b, lastVectorTwo]
  · funext k
    rcases k with ⟨k, j⟩
    fin_cases j <;> by_cases hk : k = i <;>
      simp [fiberVector, nodeVector, exceptionalDifference, exceptional, b,
        lastVectorTwo, hk, smul_eq_mul]

theorem paired_subset_sum (n : ℕ) (J : Finset (Fin n)) :
    (∑ i ∈ J, (fiberVector 2 n i + nodeVector n i)) =
      (J.card : ℤ) • b - (2 : ℤ) • ∑ i ∈ J, lastVectorTwo n i := by
  simp_rw [fiber_add_node]
  simp [Finset.sum_sub_distrib, Finset.smul_sum]

/-- An explicit integral half-class for every even-cardinality subset of paired nodes. -/
theorem paired_subset_half_sum (n : ℕ) (J : Finset (Fin n)) (hJ : Even J.card) :
    ∃ M : PicardVector 2 n,
      (2 : ℤ) • M = ∑ i ∈ J, (fiberVector 2 n i + nodeVector n i) := by
  obtain ⟨m, hm⟩ := hJ
  refine ⟨(m : ℤ) • b - ∑ i ∈ J, lastVectorTwo n i, ?_⟩
  simp only [paired_subset_sum, hm, Nat.cast_add, add_smul, smul_sub, two_smul]

/-- Divisibility is exact, not only a construction of some divisible subsets. -/
theorem paired_subset_half_sum_iff_even (n : ℕ) (J : Finset (Fin n)) :
    (∃ M : PicardVector 2 n,
      (2 : ℤ) • M = ∑ i ∈ J, (fiberVector 2 n i + nodeVector n i)) ↔ Even J.card := by
  constructor
  · rintro ⟨M, hM⟩
    rw [paired_subset_sum] at hM
    have hb := congrArg (fun x : PicardVector 2 n => x.2.1) hM
    have hsum : ∀ S : Finset (Fin n), (∑ i ∈ S, lastVectorTwo n i).2.1 = 0 := by
      intro S
      induction S using Finset.induction_on with
      | empty => rfl
      | @insert i S hi ih =>
        rw [Finset.sum_insert hi]
        change (lastVectorTwo n i).2.1 + (∑ k ∈ S, lastVectorTwo n k).2.1 = 0
        rw [ih]
        rfl
    have hcoef : (2 : ℤ) * M.2.1 = J.card := by
      simpa [b, hsum J, smul_eq_mul] using hb
    have heven : Even (J.card : ℤ) := ⟨M.2.1, by linarith⟩
    exact_mod_cast heven
  · exact paired_subset_half_sum n J

end KltDP.Examples.FrobeniusPicard
