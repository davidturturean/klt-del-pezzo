import KltDP.Examples.FrobeniusPicard
import Mathlib.Data.Rat.Star
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Integral and rational lattice calculations for the characteristic-two family

The vectors in this module are the actual total-transform coordinate vectors
from `FrobeniusPicard`. Their retained Gram matrix is computed from the
intersection form, then proved negative definite for every `n ≥ 3`.

Coordinatewise rationalization is an injective integer-linear map preserving
the intersection pairing. The rational anticanonical candidate is a scalar
multiple of the existing integral nef candidate. Its square, retained
intersections, last-exceptional intersections, and canonical-adjoint identity
are proved as vector and bilinear-form calculations.

These are the lattice calculations in Proposition `prop:frobenius-family`
and Theorem `thm:characteristic-two` of the manuscript. They do not construct
surfaces, prove a contraction or klt condition, identify a Picard group, or
prove positivity against every exterior prime. In particular the name
`anticanonicalCandidate` does not assert it is an actual geometric pullback.
-/

namespace KltDP.Examples.FrobeniusCharacteristicTwo

open KltDP.Examples.FrobeniusPicard
open scoped BigOperators

section RationalCoordinates

variable {ι : Type*}

/-- Rational coordinates in the same total-transform basis. -/
abbrev RationalLattice (ι : Type*) := ℚ × ℚ × (ι → ℚ)

/-- Coordinatewise scalar extension, as an actual integer-linear map. -/
def rationalize : BlowupLattice ι →ₗ[ℤ] RationalLattice ι :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => ((x.1 : ℚ), (x.2.1 : ℚ), fun i => (x.2.2 i : ℚ))
      map_zero' := by ext i <;> simp
      map_add' := by intros; ext i <;> simp }

theorem rationalize_injective : Function.Injective (rationalize (ι := ι)) := by
  intro x y h
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · have hc : (x.1 : ℚ) = (y.1 : ℚ) := congrArg Prod.fst h
    exact_mod_cast hc
  · have hc : (x.2.1 : ℚ) = (y.2.1 : ℚ) := congrArg (fun v => v.2.1) h
    exact_mod_cast hc
  · funext i
    have hc : (x.2.2 i : ℚ) = (y.2.2 i : ℚ) := congrArg (fun v => v.2.2 i) h
    exact_mod_cast hc

variable [Fintype ι]

/-- The rational intersection form in the same coordinates. -/
def rationalPairing (x y : RationalLattice ι) : ℚ :=
  x.1 * y.2.1 + x.2.1 * y.1 - ∑ i, x.2.2 i * y.2.2 i

theorem rationalPairing_comm (x y : RationalLattice ι) :
    rationalPairing x y = rationalPairing y x := by
  simp [rationalPairing, mul_comm, add_comm]

theorem rationalPairing_add_left (x y z : RationalLattice ι) :
    rationalPairing (x + y) z = rationalPairing x z + rationalPairing y z := by
  simp [rationalPairing, add_mul, Finset.sum_add_distrib]
  ring

theorem rationalPairing_smul_left (r : ℚ) (x y : RationalLattice ι) :
    rationalPairing (r • x) y = r * rationalPairing x y := by
  simp [rationalPairing, smul_eq_mul, mul_assoc, Finset.mul_sum, mul_add, mul_sub]

theorem rationalPairing_add_right (x y z : RationalLattice ι) :
    rationalPairing x (y + z) = rationalPairing x y + rationalPairing x z := by
  rw [rationalPairing_comm x, rationalPairing_add_left,
    rationalPairing_comm y, rationalPairing_comm z]

theorem rationalPairing_smul_right (r : ℚ) (x y : RationalLattice ι) :
    rationalPairing x (r • y) = r * rationalPairing x y := by
  rw [rationalPairing_comm x, rationalPairing_smul_left, rationalPairing_comm y]

/-- Rationalization preserves the actual integral pairing. -/
theorem rationalize_pairing (x y : BlowupLattice ι) :
    rationalPairing (rationalize x) (rationalize y) = (pairing x y : ℚ) := by
  simp [rationalPairing, rationalize, pairing]

end RationalCoordinates

section RetainedGram

/-- One graph label and independent labels for all fibers and chain nodes. -/
abbrev RetainedLabel (n : ℕ) := Unit ⊕ (Fin n ⊕ Fin n)

def retainedVector (n : ℕ) : RetainedLabel n → PicardVector 2 n
  | .inl _ => graphVector 2 n
  | .inr (.inl i) => fiberVector 2 n i
  | .inr (.inr i) => nodeVector n i

def retainedWeight (n : ℕ) : RetainedLabel n → ℤ
  | .inl _ => 2 * ((n : ℤ) - 2)
  | .inr _ => 2

theorem retainedLabel_card (n : ℕ) : Fintype.card (RetainedLabel n) = 2 * n + 1 := by
  simp [RetainedLabel]
  omega

theorem node_graph_pairing (n : ℕ) (i : Fin n) :
    pairing (nodeVector n i) (graphVector 2 n) = 0 := by
  rw [nodeVector, pairing_difference_left]
  simp [graphVector]

theorem node_fiber_pairing (n : ℕ) (i j : Fin n) :
    pairing (nodeVector n i) (fiberVector 2 n j) = 0 := by
  rw [nodeVector, pairing_difference_left]
  simp [fiberVector]

theorem node_nef_pairing (n : ℕ) (i : Fin n) :
    pairing (nodeVector n i) (nefVector 2 n) = 0 := by
  rw [nodeVector, pairing_difference_left]
  simp [nefVector]

theorem node_node_pairing (n : ℕ) (i j : Fin n) :
    pairing (nodeVector n i) (nodeVector n j) = if i = j then -2 else 0 := by
  rw [nodeVector, nodeVector, pairing_differences]
  by_cases hij : i = j <;> simp [hij]

/-- All entries are computed from the explicit integral vectors. -/
theorem retained_pairing (n : ℕ) (i j : RetainedLabel n) :
    pairing (retainedVector n i) (retainedVector n j) =
      if i = j then -retainedWeight n i else 0 := by
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  · simp [retainedVector, retainedWeight, graph_square]
  · simp [retainedVector, pairing_graph_fiber]
  · simpa [retainedVector, pairing_comm (graphVector 2 n) (nodeVector n j)] using
      node_graph_pairing n j
  · simpa [retainedVector, pairing_comm (fiberVector 2 n i) (graphVector 2 n)] using
      pairing_graph_fiber 2 n i
  · simp [retainedVector, retainedWeight, pairing_fibers]
  · simpa [retainedVector, pairing_comm (fiberVector 2 n i) (nodeVector n j)] using
      node_fiber_pairing n j i
  · simpa [retainedVector] using node_graph_pairing n i
  · simpa [retainedVector] using node_fiber_pairing n i j
  · simpa [retainedVector, retainedWeight] using node_node_pairing n i j

/-- This Gram matrix is evaluated on the retained vectors, not prescribed as data. -/
def retainedGram (n : ℕ) : Matrix (RetainedLabel n) (RetainedLabel n) ℚ :=
  fun i j => (pairing (retainedVector n i) (retainedVector n j) : ℚ)

theorem retainedGram_diagonal (n : ℕ) :
    retainedGram n = Matrix.diagonal (fun i => -(retainedWeight n i : ℚ)) := by
  ext i j
  by_cases hij : i = j <;>
    simp [retainedGram, retained_pairing, Matrix.diagonal, hij]

theorem retainedWeight_pos {n : ℕ} (hn : 3 ≤ n) (i : RetainedLabel n) :
    0 < (retainedWeight n i : ℚ) := by
  have hnq : (3 : ℚ) ≤ n := by exact_mod_cast hn
  rcases i with i | i <;> simp [retainedWeight]
  linarith

/-- Negative definiteness of the actual retained Gram matrix, over the rationals. -/
theorem retainedGram_negative_definite {n : ℕ} (hn : 3 ≤ n) :
    (-retainedGram n).PosDef := by
  rw [retainedGram_diagonal, Matrix.diagonal_neg]
  apply Matrix.PosDef.diagonal
  intro i
  simpa only [neg_neg] using retainedWeight_pos hn i

end RetainedGram

section AnticanonicalCandidate

abbrev RationalPicard (n : ℕ) := RationalLattice (Fin n × Fin 2)

/-- The manuscript's scalar, before identifying any divisor with a geometric pullback. -/
def exteriorDegree (n : ℕ) : ℚ := 1 / ((n : ℚ) - 2)

/-- The actual rational vector `M / (n-2)` in the specified basis. -/
def anticanonicalCandidate (n : ℕ) : RationalPicard n :=
  exteriorDegree n • rationalize (nefVector 2 n)

theorem parameter_denominator_pos {n : ℕ} (hn : 3 ≤ n) : 0 < (n : ℚ) - 2 := by
  have h : (3 : ℚ) ≤ n := by exact_mod_cast hn
  linarith

theorem exteriorDegree_pos {n : ℕ} (hn : 3 ≤ n) : 0 < exteriorDegree n :=
  one_div_pos.mpr (parameter_denominator_pos hn)

/-- Evaluation on every integral vector, with no curve-specific hypotheses. -/
theorem anticanonicalCandidate_pairing (n : ℕ) (x : PicardVector 2 n) :
    rationalPairing (anticanonicalCandidate n) (rationalize x) =
      exteriorDegree n * (pairing (nefVector 2 n) x : ℚ) := by
  rw [anticanonicalCandidate, rationalPairing_smul_left, rationalize_pairing]

/-- The positive square is derived from the actual vector and its pairing. -/
theorem anticanonicalCandidate_square {n : ℕ} (hn : 3 ≤ n) :
    rationalPairing (anticanonicalCandidate n) (anticanonicalCandidate n) =
      2 / ((n : ℚ) - 2) := by
  have hd : (n : ℚ) - 2 ≠ 0 := ne_of_gt (parameter_denominator_pos hn)
  rw [anticanonicalCandidate, rationalPairing_smul_left,
    rationalPairing_smul_right, rationalize_pairing, nef_square]
  push_cast
  dsimp [exteriorDegree]
  field_simp [hd]

theorem anticanonicalCandidate_square_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < rationalPairing (anticanonicalCandidate n) (anticanonicalCandidate n) := by
  rw [anticanonicalCandidate_square hn]
  exact div_pos (by norm_num) (parameter_denominator_pos hn)

theorem anticanonicalCandidate_retained (n : ℕ) (i : RetainedLabel n) :
    rationalPairing (anticanonicalCandidate n) (rationalize (retainedVector n i)) = 0 := by
  rw [anticanonicalCandidate_pairing]
  rcases i with i | (i | i)
  · simp [retainedVector, pairing_nef_graph]
  · simp [retainedVector, pairing_nef_fiber]
  · simp [retainedVector, pairing_comm (nefVector 2 n) (nodeVector n i),
      node_nef_pairing]

theorem anticanonicalCandidate_last (n : ℕ) (i : Fin n) :
    rationalPairing (anticanonicalCandidate n) (rationalize (lastVectorTwo n i)) =
      exteriorDegree n := by
  rw [anticanonicalCandidate_pairing]
  simp [lastVectorTwo, pairing_nef_exceptional]

theorem anticanonicalCandidate_last_pos {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    0 < rationalPairing (anticanonicalCandidate n) (rationalize (lastVectorTwo n i)) := by
  rw [anticanonicalCandidate_last]
  exact exteriorDegree_pos hn

/-- Integral form of the canonical-adjoint identity. -/
theorem nef_add_canonical (n : ℕ) :
    nefVector 2 n + canonicalVector 2 n = ((n : ℤ) - 3) • b := by
  ext i <;> simp [nefVector, canonicalVector, b, smul_eq_mul]
  ring

/-- The rational adjoint identity is an equality of actual rational coordinate vectors. -/
theorem anticanonicalCandidate_adjoint {n : ℕ} (hn : 3 ≤ n) :
    anticanonicalCandidate n + exteriorDegree n • rationalize (canonicalVector 2 n) =
      (((n : ℚ) - 3) / ((n : ℚ) - 2)) • rationalize (b : PicardVector 2 n) := by
  have hd : (n : ℚ) - 2 ≠ 0 := ne_of_gt (parameter_denominator_pos hn)
  ext i <;>
    simp [anticanonicalCandidate, exteriorDegree, rationalize,
      nefVector, canonicalVector, b, smul_eq_mul]
  field_simp [hd]
  ring

end AnticanonicalCandidate

end KltDP.Examples.FrobeniusCharacteristicTwo
