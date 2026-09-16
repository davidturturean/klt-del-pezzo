import KltDP.Geometry.QuadraticCoverAlgebra
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change of the actual quadratic quotient

For every commutative `R`-algebra `S`, extension of scalars carries
`R[t]/(t²-s)` to `S[t]/(t²-algebraMap R S s)`. The equivalence is constructed
from the universal properties of the polynomial quotient and tensor product.
It preserves the base scalars and sends `1 ⊗ t` to the actual target root.
No nontriviality, field, unit, splitting, or geometric realization is assumed.

Reuse: pinned `AdjoinRoot.liftHom`, `AdjoinRoot.algHom_ext`,
`Algebra.TensorProduct.lift`, and `Algebra.TensorProduct.ext` supply the
universal maps and their uniqueness. The newer official Mathlib revision
`80cbd0498ab39e21d24d6730b3f932cec672a702`, `Mathlib/RingTheory/AdjoinRoot.lean`
lines 926--957, proves the generic `AdjoinRoot.tensorAlgEquiv` by the same
two universal maps. That source is Apache 2.0 and uses Lean 4.34.0-rc2.
This is its quadratic specialization adapted to the pinned Lean 4.19 APIs;
the newer `mapAlgHom` and `liftAlgHom` infrastructure is not imported or ported.
Source: https://github.com/leanprover-community/mathlib4/blob/80cbd0498ab39e21d24d6730b3f932cec672a702/Mathlib/RingTheory/AdjoinRoot.lean#L926-L957

This module proves the algebraic base-change identification. Identifying
scheme-theoretic fibers via the affine pullback equivalence is separate.
-/

noncomputable section

open Polynomial TensorProduct

namespace KltDP.Geometry.QuadraticCover

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The coefficient-induced map between the actual polynomial quotients. -/
def baseChangeCoeffHom (s : R) :
    CoverAlgebra s →ₐ[R] CoverAlgebra (algebraMap R S s) :=
  AdjoinRoot.liftHom (polynomial s) (root (algebraMap R S s)) (by
    simp only [polynomial, map_sub, map_pow, aeval_X, aeval_C]
    rw [root_sq,
      ← IsScalarTower.algebraMap_apply R S (CoverAlgebra (algebraMap R S s)), sub_self])

@[simp]
theorem baseChangeCoeffHom_root (s : R) :
    baseChangeCoeffHom (S := S) s (root s) = root (algebraMap R S s) := by
  simp only [baseChangeCoeffHom, root, AdjoinRoot.liftHom_root]

@[simp]
theorem baseChangeCoeffHom_algebraMap (s a : R) :
    baseChangeCoeffHom (S := S) s (algebraMap R (CoverAlgebra s) a) =
      algebraMap S (CoverAlgebra (algebraMap R S s)) (algebraMap R S a) :=
  ((baseChangeCoeffHom (S := S) s).commutes a).trans
    (IsScalarTower.algebraMap_apply R S (CoverAlgebra (algebraMap R S s)) a)

@[simp]
theorem baseChangeCoeffHom_ofCoeffs (s a b : R) :
    baseChangeCoeffHom (S := S) s (ofCoeffs s a b) =
      ofCoeffs (algebraMap R S s) (algebraMap R S a) (algebraMap R S b) := by
  simp only [ofCoeffs, map_add, map_mul, baseChangeCoeffHom_algebraMap,
    baseChangeCoeffHom_root]

/-- The tensor universal map induced by changing polynomial coefficients. -/
def baseChangeHom (s : R) :
    S ⊗[R] CoverAlgebra s →ₐ[S] CoverAlgebra (algebraMap R S s) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId S (CoverAlgebra (algebraMap R S s)))
    (baseChangeCoeffHom (S := S) s) (fun _ _ => Commute.all _ _)

@[simp]
theorem baseChangeHom_tmul (s : R) (a : S) (x : CoverAlgebra s) :
    baseChangeHom (S := S) s (a ⊗ₜ[R] x) =
      algebraMap S (CoverAlgebra (algebraMap R S s)) a *
        baseChangeCoeffHom (S := S) s x :=
  rfl

@[simp]
theorem baseChangeHom_one_tmul (s : R) (x : CoverAlgebra s) :
    baseChangeHom (S := S) s (1 ⊗ₜ[R] x) = baseChangeCoeffHom (S := S) s x := by
  rw [baseChangeHom_tmul, map_one, one_mul]

@[simp]
theorem baseChangeHom_one_tmul_root (s : R) :
    baseChangeHom (S := S) s (1 ⊗ₜ[R] root s) = root (algebraMap R S s) := by
  rw [baseChangeHom_one_tmul, baseChangeCoeffHom_root]

/-- The reverse universal map, taking the target root to `1 ⊗ t`. -/
def baseChangeInvHom (s : R) :
    CoverAlgebra (algebraMap R S s) →ₐ[S] S ⊗[R] CoverAlgebra s :=
  AdjoinRoot.liftHom (polynomial (algebraMap R S s))
    ((Algebra.TensorProduct.includeRight :
      CoverAlgebra s →ₐ[R] S ⊗[R] CoverAlgebra s) (root s)) (by
        simp only [polynomial, map_sub, map_pow, aeval_X, aeval_C]
        rw [← map_pow, root_sq, AlgHom.commutes,
          IsScalarTower.algebraMap_apply R S (S ⊗[R] CoverAlgebra s), sub_self])

@[simp]
theorem baseChangeInvHom_root (s : R) :
    baseChangeInvHom (S := S) s (root (algebraMap R S s)) = 1 ⊗ₜ[R] root s := by
  simp only [baseChangeInvHom, root, AdjoinRoot.liftHom_root] <;> rfl

private theorem baseChangeHom_comp_inv (s : R) :
    (baseChangeHom (S := S) s).comp (baseChangeInvHom (S := S) s) =
      AlgHom.id S (CoverAlgebra (algebraMap R S s)) := by
  apply AdjoinRoot.algHom_ext
  change baseChangeHom (S := S) s
    (baseChangeInvHom (S := S) s (root (algebraMap R S s))) = root (algebraMap R S s)
  rw [baseChangeInvHom_root, baseChangeHom_one_tmul_root]

private theorem baseChangeInvHom_comp_hom (s : R) :
    (baseChangeInvHom (S := S) s).comp (baseChangeHom (S := S) s) =
      AlgHom.id S (S ⊗[R] CoverAlgebra s) := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · apply AdjoinRoot.algHom_ext
    change baseChangeInvHom (S := S) s
      (baseChangeHom (S := S) s (1 ⊗ₜ[R] root s)) = 1 ⊗ₜ[R] root s
    rw [baseChangeHom_one_tmul_root, baseChangeInvHom_root]

/-- Scalar extension of the actual quadratic quotient is the quotient by
the polynomial with its branch coefficient mapped to the new base ring. -/
def baseChangeEquiv (s : R) :
    S ⊗[R] CoverAlgebra s ≃ₐ[S] CoverAlgebra (algebraMap R S s) :=
  AlgEquiv.ofAlgHom (baseChangeHom (S := S) s) (baseChangeInvHom (S := S) s)
    (baseChangeHom_comp_inv (S := S) s) (baseChangeInvHom_comp_hom (S := S) s)

@[simp]
theorem baseChangeEquiv_algebraMap (s : R) (a : S) :
    baseChangeEquiv (S := S) s (algebraMap S (S ⊗[R] CoverAlgebra s) a) =
      algebraMap S (CoverAlgebra (algebraMap R S s)) a :=
  (baseChangeEquiv (S := S) s).commutes a

@[simp]
theorem baseChangeEquiv_tmul (s : R) (a : S) (x : CoverAlgebra s) :
    baseChangeEquiv (S := S) s (a ⊗ₜ[R] x) =
      algebraMap S (CoverAlgebra (algebraMap R S s)) a *
        baseChangeCoeffHom (S := S) s x :=
  baseChangeHom_tmul (S := S) s a x

@[simp]
theorem baseChangeEquiv_one_tmul_root (s : R) :
    baseChangeEquiv (S := S) s (1 ⊗ₜ[R] root s) = root (algebraMap R S s) :=
  baseChangeHom_one_tmul_root (S := S) s

@[simp]
theorem baseChangeEquiv_symm_root (s : R) :
    (baseChangeEquiv (S := S) s).symm (root (algebraMap R S s)) = 1 ⊗ₜ[R] root s :=
  baseChangeInvHom_root (S := S) s

@[simp]
theorem baseChangeEquiv_tmul_one (s : R) (a : S) :
    baseChangeEquiv (S := S) s (a ⊗ₜ[R] (1 : CoverAlgebra s)) =
      algebraMap S (CoverAlgebra (algebraMap R S s)) a := by
  rw [baseChangeEquiv_tmul, map_one, mul_one]

@[simp]
theorem baseChangeEquiv_one_tmul_ofCoeffs (s a b : R) :
    baseChangeEquiv (S := S) s (1 ⊗ₜ[R] ofCoeffs s a b) =
      ofCoeffs (algebraMap R S s) (algebraMap R S a) (algebraMap R S b) := by
  rw [baseChangeEquiv_tmul, map_one, one_mul, baseChangeCoeffHom_ofCoeffs]

end KltDP.Geometry.QuadraticCover
