import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.Int.Order.Units

/-!
# The actual Gram determinant of a perfect integral pairing

The matrix of the original map to the integral dual, in the supplied basis
and its dual basis, is the transpose of the original Gram matrix. Its
determinant is a unit by Mathlib's determinant theorem for a linear
equivalence. No symmetry or nonzero-rank assumption is needed.
-/

set_option autoImplicit false
noncomputable section

namespace KltDP.Lattices.PerfectIntegralGram

open LinearMap

variable {M ι : Type*} [AddCommGroup M] [Module ℤ M]
  [Fintype ι] [DecidableEq ι]
  (b : Basis ι ℤ M) (B : LinearMap.BilinForm ℤ M)
  (hB : Function.Bijective B)

include hB

/-- The actual Gram matrix of a perfect integral pairing has unit determinant. -/
theorem toMatrix_det_isUnit : IsUnit (BilinForm.toMatrix b B).det := by
  let e : M ≃ₗ[ℤ] Module.Dual ℤ M := LinearEquiv.ofBijective B hB
  have hm : LinearMap.toMatrix b b.dualBasis e =
      (BilinForm.toMatrix b B).transpose := by
    ext i j
    simpa only [LinearMap.toMatrix_apply, Basis.dualBasis_repr,
      Matrix.transpose_apply, BilinForm.toMatrix_apply]
      using (show e (b j) (b i) = B (b j) (b i) from rfl)
  have hu := e.isUnit_det b b.dualBasis
  simpa only [hm, Matrix.det_transpose] using hu

/-- The exact determinant hypothesis used by the integral node obstruction. -/
theorem toMatrix_det_natAbs_eq_one : (BilinForm.toMatrix b B).det.natAbs = 1 :=
  Int.isUnit_iff_natAbs_eq.mp (toMatrix_det_isUnit b B hB)

/-- The same original determinant has integer absolute value one. -/
theorem toMatrix_det_abs_eq_one : |(BilinForm.toMatrix b B).det| = 1 :=
  Int.isUnit_iff_abs_eq.mp (toMatrix_det_isUnit b B hB)

end KltDP.Lattices.PerfectIntegralGram

#check @KltDP.Lattices.PerfectIntegralGram.toMatrix_det_isUnit
#print axioms KltDP.Lattices.PerfectIntegralGram.toMatrix_det_isUnit
#check @KltDP.Lattices.PerfectIntegralGram.toMatrix_det_natAbs_eq_one
#print axioms KltDP.Lattices.PerfectIntegralGram.toMatrix_det_natAbs_eq_one
#check @KltDP.Lattices.PerfectIntegralGram.toMatrix_det_abs_eq_one
#print axioms KltDP.Lattices.PerfectIntegralGram.toMatrix_det_abs_eq_one
