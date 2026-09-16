import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic

/-!
# The actual local quadratic cover algebra

For an arbitrary branch coefficient `s`, this module constructs the polynomial
quotient `R[t]/(t²-s)`, its free basis `1,t`, actual multiplication matrix,
trace, norm, and conjugation. When `2` is a unit, the fixed and anti-fixed
parts are exactly the constant and root summands. No square root of `s`,
invertibility of `s`, or irreducibility assumption is used.

These are local algebra constructions. They do not construct the line bundle,
branch section, global cover, or geometric smoothness and intersection maps.
-/

noncomputable section

open Polynomial Matrix
open scoped Matrix

namespace KltDP.Geometry.QuadraticCover

variable {R : Type*} [CommRing R]

/-- The local cover equation, allowing zeros of the branch section. -/
def polynomial (s : R) : R[X] := X ^ 2 - C s

/-- The actual polynomial quotient, before any splitting or normalization. -/
abbrev CoverAlgebra (s : R) := AdjoinRoot (polynomial s)

def root (s : R) : CoverAlgebra s := AdjoinRoot.root (polynomial s)

theorem polynomial_monic (s : R) : (polynomial s).Monic :=
  Polynomial.monic_X_pow_sub_C s (by decide)

theorem free (s : R) : Module.Free R (CoverAlgebra s) :=
  (polynomial_monic s).free_adjoinRoot

theorem finite (s : R) : Module.Finite R (CoverAlgebra s) :=
  (polynomial_monic s).finite_adjoinRoot

/-- The actual quotient is flat over its base ring, even at branch zeros. -/
theorem flat (s : R) : Module.Flat R (CoverAlgebra s) := by
  letI := free s
  infer_instance

@[simp]
theorem root_sq (s : R) : root s ^ 2 = algebraMap R (CoverAlgebra s) s := by
  apply sub_eq_zero.mp
  have h := AdjoinRoot.eval₂_root (polynomial s)
  simpa only [polynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C] using h

/-- The universal quotient map sending the actual root to its negative. -/
def conjugationHom (s : R) : CoverAlgebra s →ₐ[R] CoverAlgebra s :=
  AdjoinRoot.liftHom (polynomial s) (-root s) (by
    simp only [polynomial, map_sub, map_pow, aeval_X, aeval_C, neg_sq,
      root_sq, sub_self])

@[simp]
theorem conjugationHom_root (s : R) : conjugationHom s (root s) = -root s := by
  simp only [conjugationHom, root, AdjoinRoot.liftHom_root]

theorem conjugationHom_comp_self (s : R) :
    (conjugationHom s).comp (conjugationHom s) = AlgHom.id R (CoverAlgebra s) := by
  apply AdjoinRoot.algHom_ext
  change conjugationHom s (conjugationHom s (root s)) = root s
  simp only [conjugationHom_root, map_neg, neg_neg]

/-- The actual deck involution of the quadratic quotient. -/
def conjugation (s : R) : CoverAlgebra s ≃ₐ[R] CoverAlgebra s :=
  AlgEquiv.ofAlgHom (conjugationHom s) (conjugationHom s)
    (conjugationHom_comp_self s) (conjugationHom_comp_self s)

@[simp]
theorem conjugation_root (s : R) : conjugation s (root s) = -root s :=
  conjugationHom_root s

theorem conjugation_involutive (s : R) : Function.Involutive (conjugation s) := by
  intro x
  exact AlgHom.congr_fun (conjugationHom_comp_self s) x

/-- Constants plus a root multiple, as elements of the actual quotient. -/
def ofCoeffs (s a b : R) : CoverAlgebra s :=
  algebraMap R (CoverAlgebra s) a + algebraMap R (CoverAlgebra s) b * root s

@[simp]
theorem ofCoeffs_zero_right (s a : R) :
    ofCoeffs s a 0 = algebraMap R (CoverAlgebra s) a := by
  simp [ofCoeffs]

@[simp]
theorem ofCoeffs_zero_left (s b : R) :
    ofCoeffs s 0 b = algebraMap R (CoverAlgebra s) b * root s := by
  simp [ofCoeffs]

@[simp]
theorem ofCoeffs_zero_one (s : R) : ofCoeffs s 0 1 = root s := by
  simp [ofCoeffs]

@[simp]
theorem conjugation_ofCoeffs (s a b : R) :
    conjugation s (ofCoeffs s a b) = ofCoeffs s a (-b) := by
  simp only [ofCoeffs, map_add, map_mul, AlgEquiv.commutes, conjugation_root,
    map_neg, mul_neg, neg_mul]

theorem ofCoeffs_mul (s a b c d : R) :
    ofCoeffs s a b * ofCoeffs s c d =
      ofCoeffs s (a * c + s * b * d) (a * d + b * c) := by
  simp only [ofCoeffs, map_add, map_mul]
  linear_combination
    (algebraMap R (CoverAlgebra s) b * algebraMap R (CoverAlgebra s) d) * root_sq s

section Coordinates

variable [Nontrivial R]

@[simp]
theorem polynomial_natDegree (s : R) : (polynomial s).natDegree = 2 :=
  Polynomial.natDegree_X_pow_sub_C

/-- The monic power basis, reindexed to the actual two-element index type. -/
def basis (s : R) : Basis (Fin 2) R (CoverAlgebra s) :=
  (AdjoinRoot.powerBasis' (polynomial_monic s)).basis.reindex
    (finCongr (polynomial_natDegree s))

theorem basis_apply (s : R) (i : Fin 2) : basis s i = root s ^ (i : ℕ) := by
  rw [basis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

@[simp]
theorem basis_zero (s : R) : basis s 0 = 1 := by
  rw [basis_apply]
  exact pow_zero _

@[simp]
theorem basis_one (s : R) : basis s 1 = root s := by
  rw [basis_apply]
  exact pow_one _

theorem finrank (s : R) : Module.finrank R (CoverAlgebra s) = 2 := by
  rw [Module.finrank_eq_card_basis (basis s), Fintype.card_fin]

/-- The constant-coordinate map on the actual quotient. -/
def constantCoeff (s : R) : CoverAlgebra s →ₗ[R] R := (basis s).coord 0

/-- The root-coordinate map on the actual quotient. -/
def rootCoeff (s : R) : CoverAlgebra s →ₗ[R] R := (basis s).coord 1

theorem ofCoeffs_eq_smul (s a b : R) :
    ofCoeffs s a b = a • basis s 0 + b • basis s 1 := by
  simp only [ofCoeffs, basis_zero, basis_one, Algebra.smul_def, mul_one]

@[simp]
theorem constantCoeff_ofCoeffs (s a b : R) :
    constantCoeff s (ofCoeffs s a b) = a := by
  rw [ofCoeffs_eq_smul]
  simp only [constantCoeff, map_add, map_smul, Basis.coord_apply, Basis.repr_self_apply]
  norm_num

@[simp]
theorem rootCoeff_ofCoeffs (s a b : R) : rootCoeff s (ofCoeffs s a b) = b := by
  rw [ofCoeffs_eq_smul]
  simp only [rootCoeff, map_add, map_smul, Basis.coord_apply, Basis.repr_self_apply]
  norm_num

@[simp]
theorem constantCoeff_algebraMap (s a : R) :
    constantCoeff s (algebraMap R (CoverAlgebra s) a) = a := by
  simpa only [ofCoeffs_zero_right] using constantCoeff_ofCoeffs s a 0

@[simp]
theorem rootCoeff_algebraMap (s a : R) :
    rootCoeff s (algebraMap R (CoverAlgebra s) a) = 0 := by
  simpa only [ofCoeffs_zero_right] using rootCoeff_ofCoeffs s a 0

@[simp]
theorem constantCoeff_root (s : R) : constantCoeff s (root s) = 0 := by
  simpa only [ofCoeffs_zero_one] using constantCoeff_ofCoeffs s 0 1

@[simp]
theorem rootCoeff_root (s : R) : rootCoeff s (root s) = 1 := by
  simpa only [ofCoeffs_zero_one] using rootCoeff_ofCoeffs s 0 1

theorem root_ne_zero (s : R) : root s ≠ 0 := by
  intro h
  have hc := congrArg (rootCoeff s) h
  rw [rootCoeff_root, map_zero] at hc
  exact one_ne_zero hc

/-- The zero-branch quotient retains a nonzero square-zero root. -/
theorem zero_branch (R : Type*) [CommRing R] [Nontrivial R] :
    root (0 : R) ≠ 0 ∧ root (0 : R) ^ 2 = 0 := by
  exact ⟨root_ne_zero 0, by rw [root_sq, map_zero]⟩

/-- Every quotient element has its uniquely determined two actual coefficients. -/
theorem ofCoeffs_coefficients (s : R) (x : CoverAlgebra s) :
    ofCoeffs s (constantCoeff s x) (rootCoeff s x) = x := by
  simpa only [Fin.sum_univ_two, constantCoeff, rootCoeff, Basis.coord_apply,
    ofCoeffs_eq_smul] using (basis s).sum_repr x

/-- The free rank-two decomposition, with its specified coefficient maps. -/
def coordinatesEquiv (s : R) : CoverAlgebra s ≃ₗ[R] R × R where
  toFun x := (constantCoeff s x, rootCoeff s x)
  invFun p := ofCoeffs s p.1 p.2
  left_inv := ofCoeffs_coefficients s
  right_inv p := by simp
  map_add' x y := by simp
  map_smul' r x := by simp

@[simp]
theorem constantCoeff_conjugation (s : R) (x : CoverAlgebra s) :
    constantCoeff s (conjugation s x) = constantCoeff s x := by
  conv_lhs => rw [← ofCoeffs_coefficients s x]
  rw [conjugation_ofCoeffs, constantCoeff_ofCoeffs]

@[simp]
theorem rootCoeff_conjugation (s : R) (x : CoverAlgebra s) :
    rootCoeff s (conjugation s x) = -rootCoeff s x := by
  conv_lhs => rw [← ofCoeffs_coefficients s x]
  rw [conjugation_ofCoeffs, rootCoeff_ofCoeffs]

/-- Multiplication by the actual quotient element in the specified free basis. -/
theorem leftMulMatrix_ofCoeffs (s a b : R) :
    Algebra.leftMulMatrix (basis s) (ofCoeffs s a b) = !![a, s * b; b, a] := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases i <;> fin_cases j
  · change constantCoeff s (ofCoeffs s a b * basis s 0) = a
    rw [basis_zero, mul_one, constantCoeff_ofCoeffs]
  · change constantCoeff s (ofCoeffs s a b * basis s 1) = s * b
    rw [basis_one, ← ofCoeffs_zero_one s, ofCoeffs_mul]
    simp
  · change rootCoeff s (ofCoeffs s a b * basis s 0) = b
    rw [basis_zero, mul_one, rootCoeff_ofCoeffs]
  · change rootCoeff s (ofCoeffs s a b * basis s 1) = a
    rw [basis_one, ← ofCoeffs_zero_one s, ofCoeffs_mul]
    simp

/-- The intrinsic algebra trace, not an independently defined coordinate formula. -/
theorem trace_ofCoeffs (s a b : R) :
    Algebra.trace R (CoverAlgebra s) (ofCoeffs s a b) = 2 * a := by
  rw [Algebra.trace_eq_matrix_trace (basis s), leftMulMatrix_ofCoeffs,
    Matrix.trace_fin_two_of]
  exact (two_mul a).symm

/-- The intrinsic algebra norm from the determinant of multiplication. -/
theorem norm_ofCoeffs (s a b : R) :
    Algebra.norm R (ofCoeffs s a b) = a ^ 2 - s * b ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (basis s), leftMulMatrix_ofCoeffs,
    Matrix.det_fin_two_of]
  ring

theorem trace_eq (s : R) (x : CoverAlgebra s) :
    Algebra.trace R (CoverAlgebra s) x = 2 * constantCoeff s x := by
  conv_lhs => rw [← ofCoeffs_coefficients s x]
  exact trace_ofCoeffs _ _ _

theorem norm_eq (s : R) (x : CoverAlgebra s) :
    Algebra.norm R x = constantCoeff s x ^ 2 - s * rootCoeff s x ^ 2 := by
  conv_lhs => rw [← ofCoeffs_coefficients s x]
  exact norm_ofCoeffs _ _ _

omit [Nontrivial R] in
private theorem eq_zero_of_neg_eq (h2 : IsUnit (2 : R)) {a : R} (ha : -a = a) :
    a = 0 := by
  apply h2.mul_left_cancel
  rw [mul_zero, two_mul]
  calc
    a + a = -a + a := congrArg (fun z => z + a) ha.symm
    _ = 0 := neg_add_cancel a

/-- The fixed part of the actual involution consists exactly of constants. -/
theorem conjugation_fixed_iff (s : R) (h2 : IsUnit (2 : R)) (x : CoverAlgebra s) :
    conjugation s x = x ↔ ∃ a : R, x = algebraMap R (CoverAlgebra s) a := by
  constructor
  · intro h
    have hcoeff := congrArg (rootCoeff s) h
    rw [rootCoeff_conjugation] at hcoeff
    have hz := eq_zero_of_neg_eq h2 hcoeff
    refine ⟨constantCoeff s x, ?_⟩
    exact (ofCoeffs_coefficients s x).symm.trans (by rw [hz, ofCoeffs_zero_right])
  · rintro ⟨a, rfl⟩
    exact (conjugation s).commutes a

/-- The anti-fixed part is exactly the root summand, including at branch zeros. -/
theorem conjugation_neg_iff (s : R) (h2 : IsUnit (2 : R)) (x : CoverAlgebra s) :
    conjugation s x = -x ↔
      ∃ b : R, x = algebraMap R (CoverAlgebra s) b * root s := by
  constructor
  · intro h
    have hcoeff := congrArg (constantCoeff s) h
    rw [constantCoeff_conjugation, map_neg] at hcoeff
    have hz := eq_zero_of_neg_eq h2 hcoeff.symm
    refine ⟨rootCoeff s x, ?_⟩
    exact (ofCoeffs_coefficients s x).symm.trans (by rw [hz, ofCoeffs_zero_left])
  · rintro ⟨b, rfl⟩
    simp only [map_mul, AlgEquiv.commutes, conjugation_root, mul_neg]

/-- The trace-zero summand is the actual anti-fixed summand when `2` is invertible. -/
theorem trace_zero_iff_conjugation_neg (s : R) (h2 : IsUnit (2 : R))
    (x : CoverAlgebra s) :
    Algebra.trace R (CoverAlgebra s) x = 0 ↔ conjugation s x = -x := by
  rw [trace_eq]
  constructor
  · intro h
    have hz : constantCoeff s x = 0 := h2.mul_left_cancel (by simpa using h)
    apply (conjugation_neg_iff s h2 x).mpr
    refine ⟨rootCoeff s x, ?_⟩
    exact (ofCoeffs_coefficients s x).symm.trans (by rw [hz, ofCoeffs_zero_left])
  · intro h
    obtain ⟨b, rfl⟩ := (conjugation_neg_iff s h2 x).mp h
    have hzero := constantCoeff_ofCoeffs s 0 b
    simp only [ofCoeffs_zero_left] at hzero
    rw [hzero, mul_zero]

end Coordinates

end KltDP.Geometry.QuadraticCover
