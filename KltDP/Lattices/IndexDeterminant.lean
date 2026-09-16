import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.Ring

/-!
# The determinant of a full-rank integral sublattice

Let `N` be an actual submodule of an integral module `M`, with bases of
`M` and `N` indexed by the same finite type. The matrix of the inclusion
computes the subgroup index. Restricting an integral bilinear form to
`N` changes its Gram matrix by integral matrix congruence. Combining
these two facts gives the index-square determinant formula.

No index/determinant identity is a hypothesis. The index is the actual
additive subgroup index, and finiteness of the quotient follows from
the two bases. Unimodularity is expressed by the ambient determinant
having absolute value one.

This proves the lattice arithmetic used in the first paragraph of the
proof of `lem:picard-index` in manuscript.tex. It does not construct
the Picard group of a rational surface, identify its intersection form,
or prove its unimodularity. The isolated-node discriminant-group
argument is also separate from this module.
-/

namespace KltDP.Lattices.IndexDeterminant

open LinearMap (BilinForm)

section MatrixCongruence

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Determinants under congruence, with no invertibility assumption. -/
theorem det_congruence (C G : Matrix ι ι R) :
    (C.transpose * G * C).det = C.det ^ 2 * G.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

end MatrixCongruence

section IntegralLattice

variable {M ι : Type*} [AddCommGroup M] [Fintype ι] [DecidableEq ι]

/-- The coordinate matrix of the actual submodule inclusion. -/
noncomputable def inclusionMatrix (b : Basis ι ℤ M) (N : Submodule ℤ M)
    (bN : Basis ι ℤ N) : Matrix ι ι ℤ :=
  LinearMap.toMatrix bN b N.subtype

/-- Columns of the inclusion matrix are coordinates of the sublattice basis. -/
theorem inclusionMatrix_eq_basisCoordinates (b : Basis ι ℤ M) (N : Submodule ℤ M)
    (bN : Basis ι ℤ N) :
    inclusionMatrix b N bN = b.toMatrix (fun i => (bN i : M)) := by
  ext i j
  rw [inclusionMatrix, LinearMap.toMatrix_apply, Basis.toMatrix_apply]
  rfl

/-- The matrix index is the index of the actual underlying additive subgroup. -/
theorem index_eq_natAbs_det_inclusion (b : Basis ι ℤ M) (N : Submodule ℤ M)
    (bN : Basis ι ℤ N) :
    N.toAddSubgroup.index = (inclusionMatrix b N bN).det.natAbs := by
  rw [inclusionMatrix_eq_basisCoordinates, ← Basis.det_apply]
  exact AddSubgroup.index_eq_natAbs_det b N.toAddSubgroup bN

omit [DecidableEq ι] in
/-- Equal finite basis index types imply that the actual quotient is finite. -/
theorem quotient_finite (b : Basis ι ℤ M) (N : Submodule ℤ M)
    (bN : Basis ι ℤ N) : Finite (M ⧸ N) := by
  letI : Module.Free ℤ M := Module.Free.of_basis b
  letI : Module.Finite ℤ M := Module.Finite.of_basis b
  apply Submodule.finiteQuotientOfFreeOfRankEq N
  rw [Module.finrank_eq_card_basis bN, Module.finrank_eq_card_basis b]

omit [DecidableEq ι] in
/-- In particular the subgroup index is positive, including in rank zero. -/
theorem index_pos (b : Basis ι ℤ M) (N : Submodule ℤ M)
    (bN : Basis ι ℤ N) : 0 < N.toAddSubgroup.index := by
  letI : Finite (M ⧸ N) := quotient_finite b N bN
  change 0 < Nat.card (M ⧸ N)
  exact Nat.card_pos

/-- A full-rank inclusion has nonzero coordinate determinant. -/
theorem det_inclusion_ne_zero (b : Basis ι ℤ M) (N : Submodule ℤ M)
    (bN : Basis ι ℤ N) : (inclusionMatrix b N bN).det ≠ 0 := by
  apply Int.natAbs_ne_zero.mp
  rw [← index_eq_natAbs_det_inclusion b N bN]
  exact Nat.ne_of_gt (index_pos b N bN)

/-- Restriction of the actual form gives the expected Gram congruence. -/
theorem gram_restriction_congruence (B : BilinForm ℤ M) (b : Basis ι ℤ M)
    (N : Submodule ℤ M) (bN : Basis ι ℤ N) :
    BilinForm.toMatrix bN (B.comp N.subtype N.subtype) =
      (inclusionMatrix b N bN).transpose * BilinForm.toMatrix b B *
        inclusionMatrix b N bN := by
  exact BilinForm.toMatrix_comp b bN B N.subtype N.subtype

/-- Signed determinant formula before taking the absolute value. -/
theorem det_gram_restriction (B : BilinForm ℤ M) (b : Basis ι ℤ M)
    (N : Submodule ℤ M) (bN : Basis ι ℤ N) :
    (BilinForm.toMatrix bN (B.comp N.subtype N.subtype)).det =
      (inclusionMatrix b N bN).det ^ 2 * (BilinForm.toMatrix b B).det := by
  rw [gram_restriction_congruence B b N bN]
  exact det_congruence _ _

/-- General determinant/index formula for any integral bilinear form. -/
theorem natAbs_det_gram_restriction (B : BilinForm ℤ M) (b : Basis ι ℤ M)
    (N : Submodule ℤ M) (bN : Basis ι ℤ N) :
    (BilinForm.toMatrix bN (B.comp N.subtype N.subtype)).det.natAbs =
      N.toAddSubgroup.index ^ 2 * (BilinForm.toMatrix b B).det.natAbs := by
  rw [det_gram_restriction B b N bN, Int.natAbs_mul, Int.natAbs_pow,
    ← index_eq_natAbs_det_inclusion b N bN]

/-- In a unimodular integral lattice, the sublattice determinant is the index squared. -/
theorem natAbs_det_gram_restriction_of_unimodular (B : BilinForm ℤ M)
    (b : Basis ι ℤ M) (N : Submodule ℤ M) (bN : Basis ι ℤ N)
    (h_unimodular : (BilinForm.toMatrix b B).det.natAbs = 1) :
    (BilinForm.toMatrix bN (B.comp N.subtype N.subtype)).det.natAbs =
      N.toAddSubgroup.index ^ 2 := by
  rw [natAbs_det_gram_restriction B b N bN, h_unimodular, mul_one]

/-- The square forced by unimodularity is a positive integer square. -/
theorem positive_square_det_gram_restriction (B : BilinForm ℤ M)
    (b : Basis ι ℤ M) (N : Submodule ℤ M) (bN : Basis ι ℤ N)
    (h_unimodular : (BilinForm.toMatrix b B).det.natAbs = 1) :
    ∃ I : ℕ, 0 < I ∧
      (BilinForm.toMatrix bN (B.comp N.subtype N.subtype)).det.natAbs = I ^ 2 :=
  ⟨N.toAddSubgroup.index, index_pos b N bN,
    natAbs_det_gram_restriction_of_unimodular B b N bN h_unimodular⟩

end IntegralLattice

end KltDP.Lattices.IndexDeterminant
