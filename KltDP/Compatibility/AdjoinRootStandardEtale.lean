/-
Copyright (c) 2026 The KltDelPezzoLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Reuse correspondence: Mathlib at 80cbd0498ab39e21d24d6730b3f932cec672a702,
Mathlib/RingTheory/Etale/StandardEtale.lean:260–296 (Andrew Yang, Apache 2.0),
constructs an actual polynomial-quotient presentation and proves that its
Jacobian is a unit. That newer file uses reorganized presentation APIs and
two variables for a localization. Here the same presentation/Jacobian
criterion is specialized to the unlocalized one-variable quotient, using
the pinned bundled-variable presentation API. The principal-kernel and
one-variable derivative calculations are proved below from pinned APIs.
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# A derivative criterion for standard smoothness of an adjoined root

The actual quotient `R[X]/(f)` has a presentation with one generator and
one relation. Its Jacobian is `f'` evaluated at the quotient root. Thus an
invertible evaluated derivative gives standard smoothness of relative
dimension zero, in the predicate used by the pinned scheme etale API.
No monicity, field, or nontriviality assumption is needed.
-/

noncomputable section

namespace KltDP.Compatibility.AdjoinRootStandardEtale

universe u

variable {R : Type u} [CommRing R]

private theorem aeval_singleton (f : Polynomial R) (p : MvPolynomial Unit R) :
    MvPolynomial.aeval (fun _ : Unit => AdjoinRoot.root f) p =
      Polynomial.aeval (AdjoinRoot.root f) (MvPolynomial.pUnitAlgEquiv R p) := by
  have h : MvPolynomial.aeval (fun _ : Unit => AdjoinRoot.root f) =
      (Polynomial.aeval (AdjoinRoot.root f)).comp
        (MvPolynomial.pUnitAlgEquiv R).toAlgHom := by
    ext i
    cases i
    simp [MvPolynomial.pUnitAlgEquiv]
  exact AlgHom.congr_fun h p

private theorem aeval_singleton_surjective (f : Polynomial R) :
    Function.Surjective (MvPolynomial.aeval (R := R) (fun _ : Unit => AdjoinRoot.root f)) := by
  intro x
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (g := f) x
  refine ⟨(MvPolynomial.pUnitAlgEquiv R).symm p, ?_⟩
  rw [aeval_singleton, AlgEquiv.apply_symm_apply, AdjoinRoot.aeval_eq, hp]

private theorem pderiv_pUnitAlgEquiv_symm (p : Polynomial R) :
    MvPolynomial.pderiv () ((MvPolynomial.pUnitAlgEquiv R).symm p) =
      (MvPolynomial.pUnitAlgEquiv R).symm p.derivative := by
  have hm (n : ℕ) (a : R) :
      (MvPolynomial.pUnitAlgEquiv R).symm (Polynomial.monomial n a) =
        MvPolynomial.monomial (Finsupp.single () n) a := by
    simpa using (MvPolynomial.pUnitAlgEquiv_symm_monomial
      (R := R) (d := Finsupp.single () n) (r := a))
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
      rw [hm, MvPolynomial.pderiv_monomial_single, Polynomial.derivative_monomial, hm]

/-- The actual principal quotient has one generator and one defining relation. -/
def presentation (f : Polynomial R) : Algebra.Presentation.{0, 0} R (AdjoinRoot f) where
  toGenerators := Algebra.Generators.ofSurjective
    (fun _ : Unit => AdjoinRoot.root f) (aeval_singleton_surjective f)
  rels := Unit
  relation _ := (MvPolynomial.pUnitAlgEquiv R).symm f
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    ext p
    change p ∈ Ideal.span (Set.range (fun _ : Unit =>
      (MvPolynomial.pUnitAlgEquiv R).symm f)) ↔
        MvPolynomial.aeval (fun _ : Unit => AdjoinRoot.root f) p = 0
    rw [Set.range_const, Ideal.mem_span_singleton, aeval_singleton,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    simpa only [AlgEquiv.apply_symm_apply] using (map_dvd_iff (MvPolynomial.pUnitAlgEquiv R)
      (a := (MvPolynomial.pUnitAlgEquiv R).symm f) (b := p)).symm

/-- The unique relation is differentiated in the unique variable. -/
def preSubmersivePresentation (f : Polynomial R) :
    Algebra.PreSubmersivePresentation.{0, 0} R (AdjoinRoot f) where
  toPresentation := presentation f
  map := id
  map_inj := Function.injective_id
  relations_finite := inferInstanceAs (Finite Unit)

/-- The determinant of the actual singleton Jacobian is the evaluated derivative. -/
theorem jacobian_eq_aeval_derivative (f : Polynomial R) :
    (preSubmersivePresentation f).jacobian =
      Polynomial.aeval (AdjoinRoot.root f) f.derivative := by
  letI : Fintype (preSubmersivePresentation f).rels := inferInstanceAs (Fintype Unit)
  letI : DecidableEq (preSubmersivePresentation f).rels :=
    inferInstanceAs (DecidableEq Unit)
  letI : Unique (preSubmersivePresentation f).rels := inferInstanceAs (Unique Unit)
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique, Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
    Algebra.Generators.algebraMap_apply]
  change MvPolynomial.aeval (fun _ : Unit => AdjoinRoot.root f)
    (MvPolynomial.pderiv () ((MvPolynomial.pUnitAlgEquiv R).symm f)) = _
  rw [pderiv_pUnitAlgEquiv_symm, aeval_singleton, AlgEquiv.apply_symm_apply]

/-- An invertible evaluated derivative makes the actual singleton presentation submersive. -/
def submersivePresentation (f : Polynomial R)
    (hf : IsUnit (Polynomial.aeval (AdjoinRoot.root f) f.derivative)) :
    Algebra.SubmersivePresentation.{0, 0} R (AdjoinRoot f) where
  toPreSubmersivePresentation := preSubmersivePresentation f
  jacobian_isUnit := (jacobian_eq_aeval_derivative f).symm ▸ hf
  isFinite := {
    finite_vars := inferInstanceAs (Finite Unit)
    finite_rels := inferInstanceAs (Finite Unit) }

/-- An adjoined root is standard smooth of relative dimension zero when its
evaluated derivative is a unit. This is the pinned scheme etale predicate. -/
theorem adjoinRoot_isStandardSmoothOfRelativeDimension_zero (f : Polynomial R)
    (hf : IsUnit (Polynomial.aeval (AdjoinRoot.root f) f.derivative)) :
    Algebra.IsStandardSmoothOfRelativeDimension 0 R (AdjoinRoot f) := by
  apply (submersivePresentation f hf).isStandardSmoothOfRelativeDimension
  simp [Algebra.Presentation.dimension, submersivePresentation,
    preSubmersivePresentation, presentation, Algebra.Generators.ofSurjective]

end KltDP.Compatibility.AdjoinRootStandardEtale
