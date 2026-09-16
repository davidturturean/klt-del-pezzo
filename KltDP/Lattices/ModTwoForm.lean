import KltDP.Lattices.ModTwoCoordinates
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Units
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Reduction modulo two of an actual integral Gram matrix

The matrix and vector reductions in this module are entrywise integer
casts to `ZMod 2`. Their bilinear pairing is proved equal to the reduction
of the original integral pairing. The determinant also commutes with this
actual reduction. An integral determinant of absolute value one is a unit,
so its reduction is a unit and the reduced bilinear form is nondegenerate.

The basis adapter uses the Gram matrix of an actual integer-valued bilinear
form and evaluates it on actual basis coordinates. The constructed
coordinate equivalence transports this form to the actual quotient `M / (2 M)`.
Its value on quotient classes is proved equal to the reduced integral
pairing. No nondegeneracy of the reduced form is assumed, and no symmetry
or division by two is used.

These are algebraic adapters for `lem:picard-parity`; they do not identify
the actual Picard group of a surface, establish integral unimodularity of
its intersection pairing, or prove any geometric intersection identity.
-/

namespace KltDP.Lattices.ModTwoForm

variable {ι : Type*}

/-- Entrywise reduction of the supplied integer matrix. -/
def reduceMatrix (Q : Matrix ι ι ℤ) : Matrix ι ι (ZMod 2) :=
  Q.map fun z => (z : ZMod 2)

/-- Entrywise reduction of actual integer coordinate vectors. -/
def reduceVector (x : ι → ℤ) : ι → ZMod 2 := fun i => (x i : ZMod 2)

@[simp]
theorem reduceMatrix_apply (Q : Matrix ι ι ℤ) (i j : ι) :
    reduceMatrix Q i j = (Q i j : ZMod 2) := rfl

@[simp]
theorem reduceVector_apply (x : ι → ℤ) (i : ι) :
    reduceVector x i = (x i : ZMod 2) := rfl

variable [Fintype ι] [DecidableEq ι]

/-- The actual determinant commutes with reduction of all matrix entries. -/
theorem det_reduceMatrix (Q : Matrix ι ι ℤ) :
    (reduceMatrix Q).det = (Q.det : ZMod 2) :=
  (Int.cast_det (R := ZMod 2) Q).symm

/-- The bilinear form on binary coordinate vectors given by the reduced
matrix, with no extra intersection or nondegeneracy premise. -/
def reducedForm (Q : Matrix ι ι ℤ) :
    LinearMap.BilinForm (ZMod 2) (ι → ZMod 2) :=
  (reduceMatrix Q).toBilin'

/-- Pairing the reduced vectors equals reducing their original integer
pairing. This includes all cross terms of the actual supplied matrix. -/
theorem reducedForm_reduceVector (Q : Matrix ι ι ℤ) (x y : ι → ℤ) :
    reducedForm Q (reduceVector x) (reduceVector y) =
      (Q.toBilin' x y : ZMod 2) := by
  simp only [reducedForm, Matrix.toBilin'_apply, reduceVector, reduceMatrix,
    Matrix.map_apply, Int.cast_sum, Int.cast_mul]

/-- An integral unimodular determinant remains a unit after reduction. -/
theorem isUnit_det_reduceMatrix (Q : Matrix ι ι ℤ) (hQ : Q.det.natAbs = 1) :
    IsUnit (reduceMatrix Q).det := by
  rw [det_reduceMatrix]
  exact IsUnit.map (Int.castRingHom (ZMod 2))
    (Int.isUnit_iff_natAbs_eq.mpr hQ)

/-- An integral Gram matrix of determinant absolute value one induces a
nondegenerate binary form. The proof derives this from its unit determinant. -/
theorem reducedForm_nondegenerate (Q : Matrix ι ι ℤ) (hQ : Q.det.natAbs = 1) :
    (reducedForm Q).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  exact (isUnit_det_reduceMatrix Q hQ).ne_zero

section IntegralBasis

variable {M : Type*} [AddCommGroup M]

/-- The actual Gram matrix evaluates on basis coordinates as the original
bilinear form, before reduction modulo two. -/
theorem gramMatrix_toBilin'_coordinates (b : Basis ι ℤ M)
    (B : LinearMap.BilinForm ℤ M) (x y : M) :
    (BilinForm.toMatrix b B).toBilin'
      (fun i => b.repr x i) (fun i => b.repr y i) = B x y := by
  calc
    _ = Matrix.toBilin b (BilinForm.toMatrix b B) x y := by
      rw [Matrix.toBilin'_apply, Matrix.toBilin_apply]
    _ = B x y := by rw [Matrix.toBilin_toMatrix]

/-- Reduction of the Gram matrix of the supplied integral bilinear form. -/
noncomputable def reducedGramForm (b : Basis ι ℤ M)
    (B : LinearMap.BilinForm ℤ M) :
    LinearMap.BilinForm (ZMod 2) (ι → ZMod 2) :=
  reducedForm (BilinForm.toMatrix b B)

/-- The reduced Gram form computes the reduction of the actual integral
pairing on all actual vectors, using their basis coordinates. -/
theorem reducedGramForm_coordinates (b : Basis ι ℤ M)
    (B : LinearMap.BilinForm ℤ M) (x y : M) :
    reducedGramForm b B (reduceVector (fun i => b.repr x i))
      (reduceVector (fun i => b.repr y i)) = (B x y : ZMod 2) := by
  rw [reducedGramForm, reducedForm_reduceVector, gramMatrix_toBilin'_coordinates]

/-- Actual integral Gram unimodularity proves nondegeneracy of its reduced
form, without any symmetry hypothesis. -/
theorem reducedGramForm_nondegenerate (b : Basis ι ℤ M)
    (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1) :
    (reducedGramForm b B).Nondegenerate :=
  reducedForm_nondegenerate (BilinForm.toMatrix b B) hB

/-- Transport the reduced Gram form to the existing quotient by doubles
using its constructed coordinate equivalence. -/
noncomputable def quotientForm (b : Basis ι ℤ M)
    (B : LinearMap.BilinForm ℤ M) :
    LinearMap.BilinForm (ZMod 2) (Codes.ModTwo M) :=
  LinearMap.BilinForm.congr
    (ModTwoCoordinates.modTwoCoordinatesEquiv b).symm (reducedGramForm b B)

/-- On actual quotient representatives, the transported pairing is exactly
the integral pairing reduced modulo two. -/
theorem quotientForm_mk (b : Basis ι ℤ M)
    (B : LinearMap.BilinForm ℤ M) (x y : M) :
    quotientForm b B (Codes.modTwoMk M x) (Codes.modTwoMk M y) =
      (B x y : ZMod 2) := by
  simp only [quotientForm, LinearMap.BilinForm.congr_apply, LinearEquiv.symm_symm,
    ModTwoCoordinates.modTwoCoordinatesEquiv_mk]
  exact reducedGramForm_coordinates b B x y

/-- Integral Gram unimodularity proves nondegeneracy on the actual
quotient by doubles, rather than on an assumed substitute vector space. -/
theorem quotientForm_nondegenerate (b : Basis ι ℤ M)
    (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1) :
    (quotientForm b B).Nondegenerate :=
  (reducedGramForm_nondegenerate b B hB).congr
    (ModTwoCoordinates.modTwoCoordinatesEquiv b).symm

end IntegralBasis

end KltDP.Lattices.ModTwoForm
