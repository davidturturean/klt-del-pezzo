import KltDP.Geometry.QuadraticCoverAlgebra
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic

/-!
# Changes of generator of the actual local quadratic cover

A relation `s = u² * s'` produces the actual quotient map taking the root
of `s` to `u` times the root of `s'`. For a unit `u` this map is an algebra
equivalence. Its composition, coefficient, conjugation, trace and norm laws
are proved on the quotient elements. These are the local transition maps
needed to glue a quadratic cover algebra under changes of line-bundle frame;
no atlas, cocycle, branch section, or global cover is assumed constructed.
-/

noncomputable section

open Polynomial

namespace KltDP.Geometry.QuadraticCover

variable {R : Type*} [CommRing R]

/-- Multiplication of transition scalars gives the next actual equation change. -/
theorem rescaleCondition_comp (s s' s'' u v : R)
    (h : s = u ^ 2 * s') (h' : s' = v ^ 2 * s'') :
    s = (u * v) ^ 2 * s'' := by
  rw [h, h']
  ring

/-- The actual quotient map changing the adjoined generator by a scalar. -/
def rescaleHom (s s' u : R) (h : s = u ^ 2 * s') :
    CoverAlgebra s →ₐ[R] CoverAlgebra s' :=
  AdjoinRoot.liftHom (polynomial s)
    (algebraMap R (CoverAlgebra s') u * root s') (by
      simp only [polynomial, map_sub, map_pow, aeval_X, aeval_C]
      rw [mul_pow, root_sq, ← map_pow, ← map_mul, ← h, sub_self])

@[simp]
theorem rescaleHom_root (s s' u : R) (h : s = u ^ 2 * s') :
    rescaleHom s s' u h (root s) =
      algebraMap R (CoverAlgebra s') u * root s' := by
  simp only [rescaleHom, root, AdjoinRoot.liftHom_root]

@[simp]
theorem rescaleHom_algebraMap (s s' u : R) (h : s = u ^ 2 * s') (a : R) :
    rescaleHom s s' u h (algebraMap R (CoverAlgebra s) a) =
      algebraMap R (CoverAlgebra s') a :=
  (rescaleHom s s' u h).commutes a

/-- The constant summand is unchanged and the root coefficient changes by `u`. -/
@[simp]
theorem rescaleHom_ofCoeffs (s s' u : R) (h : s = u ^ 2 * s') (a b : R) :
    rescaleHom s s' u h (ofCoeffs s a b) = ofCoeffs s' a (b * u) := by
  simp only [ofCoeffs, map_add, map_mul, rescaleHom_algebraMap, rescaleHom_root,
    mul_assoc]

/-- These quotient maps have the actual transition-map composition law. -/
theorem rescaleHom_comp (s s' s'' u v : R)
    (h : s = u ^ 2 * s') (h' : s' = v ^ 2 * s'') :
    (rescaleHom s' s'' v h').comp (rescaleHom s s' u h) =
      rescaleHom s s'' (u * v) (rescaleCondition_comp s s' s'' u v h h') := by
  apply AdjoinRoot.algHom_ext
  change rescaleHom s' s'' v h' (rescaleHom s s' u h (root s)) =
    rescaleHom s s'' (u * v) (rescaleCondition_comp s s' s'' u v h h') (root s)
  simp only [rescaleHom_root, map_mul, rescaleHom_algebraMap, mul_assoc]

/-- Changing the generator by one is the actual identity map. -/
theorem rescaleHom_one (s : R) :
    rescaleHom s s 1 (by simp) = AlgHom.id R (CoverAlgebra s) := by
  apply AdjoinRoot.algHom_ext
  change rescaleHom s s 1 _ (root s) = root s
  simp only [rescaleHom_root, map_one, one_mul]

/-- Every scalar change of generator intertwines the actual deck involutions. -/
theorem rescaleHom_conjugation (s s' u : R) (h : s = u ^ 2 * s')
    (x : CoverAlgebra s) :
    rescaleHom s s' u h (conjugation s x) =
      conjugation s' (rescaleHom s s' u h x) := by
  have heq : (rescaleHom s s' u h).comp (conjugation s).toAlgHom =
      (conjugation s').toAlgHom.comp (rescaleHom s s' u h) := by
    apply AdjoinRoot.algHom_ext
    change rescaleHom s s' u h (conjugation s (root s)) =
      conjugation s' (rescaleHom s s' u h (root s))
    simp only [conjugation_root, map_neg, rescaleHom_root, map_mul,
      AlgEquiv.commutes, mul_neg]
  exact AlgHom.congr_fun heq x

/-- A unit change of generator gives the reverse equation change. -/
theorem rescaleCondition_inv (s s' : R) (u : Rˣ) (h : s = (u : R) ^ 2 * s') :
    s' = ((u⁻¹ : Rˣ) : R) ^ 2 * s := by
  rw [h, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]

/-- The actual algebra equivalence for a unit change of local frame. -/
def rescaleEquiv (s s' : R) (u : Rˣ) (h : s = (u : R) ^ 2 * s') :
    CoverAlgebra s ≃ₐ[R] CoverAlgebra s' :=
  AlgEquiv.ofAlgHom (rescaleHom s s' (u : R) h)
    (rescaleHom s' s ((u⁻¹ : Rˣ) : R) (rescaleCondition_inv s s' u h))
    (by
      apply AdjoinRoot.algHom_ext
      change rescaleHom s s' (u : R) h
        (rescaleHom s' s ((u⁻¹ : Rˣ) : R) (rescaleCondition_inv s s' u h) (root s')) = root s'
      simp only [rescaleHom_root, map_mul, rescaleHom_algebraMap]
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul])
    (by
      apply AdjoinRoot.algHom_ext
      change rescaleHom s' s ((u⁻¹ : Rˣ) : R) (rescaleCondition_inv s s' u h)
        (rescaleHom s s' (u : R) h (root s)) = root s
      simp only [rescaleHom_root, map_mul, rescaleHom_algebraMap]
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul])

@[simp]
theorem rescaleEquiv_root (s s' : R) (u : Rˣ) (h : s = (u : R) ^ 2 * s') :
    rescaleEquiv s s' u h (root s) =
      algebraMap R (CoverAlgebra s') (u : R) * root s' :=
  rescaleHom_root s s' (u : R) h

@[simp]
theorem rescaleEquiv_symm_root (s s' : R) (u : Rˣ)
    (h : s = (u : R) ^ 2 * s') :
    (rescaleEquiv s s' u h).symm (root s') =
      algebraMap R (CoverAlgebra s) ((u⁻¹ : Rˣ) : R) * root s :=
  rescaleHom_root s' s ((u⁻¹ : Rˣ) : R) (rescaleCondition_inv s s' u h)

@[simp]
theorem rescaleEquiv_algebraMap (s s' : R) (u : Rˣ)
    (h : s = (u : R) ^ 2 * s') (a : R) :
    rescaleEquiv s s' u h (algebraMap R (CoverAlgebra s) a) =
      algebraMap R (CoverAlgebra s') a :=
  (rescaleEquiv s s' u h).commutes a

@[simp]
theorem rescaleEquiv_ofCoeffs (s s' : R) (u : Rˣ)
    (h : s = (u : R) ^ 2 * s') (a b : R) :
    rescaleEquiv s s' u h (ofCoeffs s a b) = ofCoeffs s' a (b * (u : R)) :=
  rescaleHom_ofCoeffs s s' (u : R) h a b

theorem rescaleEquiv_conjugation (s s' : R) (u : Rˣ)
    (h : s = (u : R) ^ 2 * s') (x : CoverAlgebra s) :
    rescaleEquiv s s' u h (conjugation s x) =
      conjugation s' (rescaleEquiv s s' u h x) :=
  rescaleHom_conjugation s s' (u : R) h x

/-- The transition equivalences themselves satisfy composition, not just their coefficients. -/
theorem rescaleEquiv_trans (s s' s'' : R) (u v : Rˣ)
    (h : s = (u : R) ^ 2 * s') (h' : s' = (v : R) ^ 2 * s'') :
    (rescaleEquiv s s' u h).trans (rescaleEquiv s' s'' v h') =
      rescaleEquiv s s'' (u * v)
        (rescaleCondition_comp s s' s'' (u : R) (v : R) h h') := by
  apply AlgEquiv.coe_algHom_injective
  exact rescaleHom_comp s s' s'' (u : R) (v : R) h h'

theorem rescaleEquiv_one (s : R) :
    rescaleEquiv s s 1 (by simp) = (AlgEquiv.refl : CoverAlgebra s ≃ₐ[R] CoverAlgebra s) := by
  apply AlgEquiv.coe_algHom_injective
  exact rescaleHom_one s

/-- Compatibility of the intrinsic algebra trace over every commutative base ring. -/
theorem rescaleEquiv_trace (s s' : R) (u : Rˣ)
    (h : s = (u : R) ^ 2 * s') (x : CoverAlgebra s) :
    Algebra.trace R (CoverAlgebra s') (rescaleEquiv s s' u h x) =
      Algebra.trace R (CoverAlgebra s) x :=
  Algebra.trace_eq_of_algEquiv (rescaleEquiv s s' u h) x

/-- Compatibility of the intrinsic algebra norm over every commutative base ring. -/
theorem rescaleEquiv_norm (s s' : R) (u : Rˣ)
    (h : s = (u : R) ^ 2 * s') (x : CoverAlgebra s) :
    Algebra.norm R (rescaleEquiv s s' u h x) = Algebra.norm R x :=
  Algebra.norm_eq_of_algEquiv (rescaleEquiv s s' u h) x

section Coordinates

variable [Nontrivial R]

@[simp]
theorem constantCoeff_rescaleEquiv (s s' : R) (u : Rˣ)
    (h : s = (u : R) ^ 2 * s') (x : CoverAlgebra s) :
    constantCoeff s' (rescaleEquiv s s' u h x) = constantCoeff s x := by
  conv_lhs => rw [← ofCoeffs_coefficients s x]
  rw [rescaleEquiv_ofCoeffs, constantCoeff_ofCoeffs]

@[simp]
theorem rootCoeff_rescaleEquiv (s s' : R) (u : Rˣ)
    (h : s = (u : R) ^ 2 * s') (x : CoverAlgebra s) :
    rootCoeff s' (rescaleEquiv s s' u h x) = rootCoeff s x * (u : R) := by
  conv_lhs => rw [← ofCoeffs_coefficients s x]
  rw [rescaleEquiv_ofCoeffs, rootCoeff_ofCoeffs]

/-- The local transition on the actual rank-two module is diagonal with entries `1,u`. -/
theorem coordinatesEquiv_rescaleEquiv (s s' : R) (u : Rˣ)
    (h : s = (u : R) ^ 2 * s') (x : CoverAlgebra s) :
    coordinatesEquiv s' (rescaleEquiv s s' u h x) =
      (constantCoeff s x, rootCoeff s x * (u : R)) := by
  apply Prod.ext
  · exact constantCoeff_rescaleEquiv s s' u h x
  · exact rootCoeff_rescaleEquiv s s' u h x

end Coordinates

end KltDP.Geometry.QuadraticCover
