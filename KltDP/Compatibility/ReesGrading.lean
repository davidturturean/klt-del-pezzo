import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Polynomial.Coeff

/-!
# The natural grading on Mathlib's Rees algebra

The carrier is exactly `reesAlgebra I`, the existing subalgebra of
`R[X]` whose degree `n` coefficient lies in `I ^ n`. Its homogeneous
part is the range of the actual degree `n` monomial map. Coefficients
prove uniqueness of the decomposition, and finite monomial expansion
proves existence.

This supplies the grading required by the existing `Proj` construction.
It assumes no geometric property of that scheme.

Reuse: Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b,
`RingTheory/ReesAlgebra.lean` (Andrew Yang, Apache 2.0), and
`RingTheory/GradedAlgebra/Basic.lean` (Eric Wieser, Apache 2.0).
The independent direct-sum Rees grading in ProjConstruction/Proj,
ed778ef92453f1be91988cbcd11dded470eea8d3, was reviewed; this adapter
uses the pinned polynomial carrier and does not copy that implementation.
-/

noncomputable section

open scoped DirectSum
open Polynomial

namespace KltDP.ReesGrading

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- An element of `I ^ n`, placed in degree `n` of the actual Rees algebra. -/
def single (n : ℕ) : ↥(I ^ n) →ₗ[R] reesAlgebra I where
  toFun r := ⟨monomial n (r : R), reesAlgebra.monomial_mem.mpr r.property⟩
  map_add' r s := Subtype.ext
    (map_add (monomial n : R →ₗ[R] R[X]) (r : R) (s : R))
  map_smul' r s := Subtype.ext
    (map_smul (monomial n : R →ₗ[R] R[X]) r (s : R))

theorem single_val (n : ℕ) (r : ↥(I ^ n)) :
    (single I n r : R[X]) = monomial n (r : R) := rfl

/-- The degree `n` homogeneous submodule of the actual polynomial Rees algebra. -/
def component (n : ℕ) : Submodule R (reesAlgebra I) :=
  LinearMap.range (single I n)

theorem single_mem_component (n : ℕ) (r : ↥(I ^ n)) :
    single I n r ∈ component I n := ⟨r, rfl⟩

/-- A homogeneous Rees element is determined by its coefficient in its degree. -/
theorem homogeneous_eq_monomial {n : ℕ} (x : component I n) :
    ((x : reesAlgebra I) : R[X]) =
      monomial n (((x : reesAlgebra I) : R[X]).coeff n) := by
  obtain ⟨r, hr⟩ := x.property
  change single I n r = (x : reesAlgebra I) at hr
  rw [← hr, single_val, coeff_monomial]
  simp

theorem homogeneous_coeff_eq_zero {n m : ℕ} (x : component I n) (h : n ≠ m) :
    (((x : reesAlgebra I) : R[X]).coeff m) = 0 := by
  rw [homogeneous_eq_monomial I x, coeff_monomial]
  simp [h]

instance : SetLike.GradedOne (component I) where
  one_mem := by
    refine ⟨⟨1, by simp⟩, ?_⟩
    apply Subtype.ext
    simp [single, Polynomial.monomial_zero_left]

instance : SetLike.GradedMul (component I) where
  mul_mem := by
    rintro n m _ _ ⟨r, rfl⟩ ⟨s, rfl⟩
    refine ⟨⟨(r : R) * (s : R), ?_⟩, ?_⟩
    · rw [pow_add]
      exact Ideal.mul_mem_mul r.property s.property
    · apply Subtype.ext
      exact (monomial_mul_monomial n m (r : R) (s : R)).symm

instance : SetLike.GradedMonoid (component I) where

/-- Taking a coefficient of the canonical sum recovers the corresponding
homogeneous summand's coefficient. -/
theorem coefficient_sum (f : ⨁ n, component I n) (m : ℕ) :
    ((DirectSum.coeAddMonoidHom (component I) f : reesAlgebra I) : R[X]).coeff m =
      (((f m : component I m) : reesAlgebra I) : R[X]).coeff m := by
  classical
  induction f using DirectSum.induction_on with
  | zero => simp
  | of n x =>
      rw [DirectSum.coeAddMonoidHom_of]
      by_cases h : n = m
      · subst m
        rw [DirectSum.of_eq_same]
      · rw [DirectSum.of_eq_of_ne _ _ _ h]
        simpa only [Submodule.coe_zero, Subalgebra.coe_zero, coeff_zero] using
          homogeneous_coeff_eq_zero I x h
  | add f g hf hg =>
      simpa only [map_add, Subalgebra.coe_add, Polynomial.coeff_add,
        DirectSum.add_apply, Submodule.coe_add] using congrArg₂ (· + ·) hf hg

/-- The existing Rees algebra is the internal direct sum of its actual
monomial homogeneous components. -/
theorem isInternal : DirectSum.IsInternal (component I) := by
  classical
  constructor
  · intro f g h
    apply DFinsupp.ext
    intro n
    apply Subtype.ext
    apply Subtype.ext
    rw [homogeneous_eq_monomial I (f n), homogeneous_eq_monomial I (g n)]
    apply congrArg (monomial n)
    rw [← coefficient_sum I f n, ← coefficient_sum I g n, h]
  · intro p
    let x (n : ℕ) : component I n :=
      ⟨single I n ⟨(p : R[X]).coeff n, p.property n⟩,
        single_mem_component I n _⟩
    refine ⟨∑ n ∈ (p : R[X]).support, DirectSum.of _ n (x n), ?_⟩
    apply Subtype.ext
    change (reesAlgebra I).val
      (DirectSum.coeAddMonoidHom (component I)
        (∑ n ∈ (p : R[X]).support, DirectSum.of _ n (x n))) = (p : R[X])
    simp only [map_sum, DirectSum.coeAddMonoidHom_of]
    change (∑ n ∈ (p : R[X]).support, monomial n ((p : R[X]).coeff n)) = (p : R[X])
    exact (p : R[X]).sum_monomial_eq

/-- The natural grading of the pinned polynomial Rees algebra. -/
instance gradedAlgebra : GradedAlgebra (component I) :=
  (isInternal I).gradedAlgebra

end KltDP.ReesGrading
