/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The empty-relation presentation proof adapts the bounded slice in
Vilin97/TauCeti, commit a74dfee78f800df63f085a19006f7d502eee365e,
TauCeti/AlgebraicGeometry/ProjectiveLine/Smooth.lean:425–458.
The project pin bundles the generator and relation types as fields;
the newer source takes them as parameters. The actual presentation and
empty Jacobian proof are retained. The coefficient-ring map is unchanged.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Polynomial schemes are smooth over their coefficient ring

The pin's scheme smoothness uses standard-smooth presentations, rather
than the separate `Algebra.Smooth` predicate. We supply its actual
empty-relation presentation through a polynomial algebra equivalence.
The existing scheme/ring-hom adapter then applies without identifying
these two predicates by assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Compatibility.PolynomialStandardSmooth

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type w} [Finite ι] (e : MvPolynomial ι R ≃ₐ[R] S)

omit [Finite ι] in
/-- Evaluation on the images of the variables is the given actual algebra isomorphism. -/
theorem aeval_variables :
    MvPolynomial.aeval (fun i => e (MvPolynomial.X i)) = e.toAlgHom := by
  ext i
  simp

/-- An actual polynomial algebra equivalence gives a presentation with no relations. -/
def freePresentation : Algebra.Presentation.{0, w} R S where
  vars := ι
  val i := e (MvPolynomial.X i)
  σ' := e.symm
  aeval_val_σ' s := by rw [aeval_variables]; exact e.apply_symm_apply s
  rels := PEmpty.{1}
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    rw [Set.range_eq_empty, Ideal.span_empty, Algebra.Generators.ker_eq_ker_aeval_val]
    symm
    rw [← RingHom.injective_iff_ker_eq_bot]
    simpa only [aeval_variables] using e.injective

/-- The empty relation set embeds into the actual variable set. -/
def freePreSubmersivePresentation : Algebra.PreSubmersivePresentation.{0, w} R S where
  toPresentation := freePresentation e
  map := PEmpty.elim
  map_inj a := PEmpty.elim a
  relations_finite := inferInstanceAs (Finite PEmpty.{1})

/-- The Jacobian of the empty relation matrix is the unit determinant. -/
def freeSubmersivePresentation : Algebra.SubmersivePresentation.{0, w} R S where
  toPreSubmersivePresentation := freePreSubmersivePresentation e
  jacobian_isUnit := by
    letI : Fintype (freePreSubmersivePresentation e).rels :=
      inferInstanceAs (Fintype PEmpty.{1})
    letI : DecidableEq (freePreSubmersivePresentation e).rels :=
      inferInstanceAs (DecidableEq PEmpty.{1})
    letI : IsEmpty (freePreSubmersivePresentation e).rels :=
      inferInstanceAs (IsEmpty PEmpty.{1})
    have hd : (freePreSubmersivePresentation e).jacobiMatrix.det = 1 := Matrix.det_isEmpty
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hd, map_one]
    exact isUnit_one
  isFinite := {
    finite_vars := inferInstanceAs (Finite ι)
    finite_rels := inferInstanceAs (Finite PEmpty.{1}) }

/-- Polynomial coordinates prove standard smoothness of their actual relative dimension. -/
theorem of_polynomialEquiv (e : MvPolynomial ι R ≃ₐ[R] S) :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) R S := by
  apply (freeSubmersivePresentation e).isStandardSmoothOfRelativeDimension
  simp [Algebra.Presentation.dimension, freeSubmersivePresentation,
    freePreSubmersivePresentation, freePresentation]

/-- The ordinary polynomial ring has the required one-generator presentation. -/
theorem polynomial_standardSmooth (R : Type*) [CommRing R] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (Polynomial R) := by
  simpa using of_polynomialEquiv (ι := PUnit.{1}) (MvPolynomial.pUnitAlgEquiv R)

/-- The literal polynomial constants ring homomorphism is standard smooth. -/
theorem polynomialC_standardSmooth (R : Type*) [CommRing R] :
    RingHom.IsStandardSmoothOfRelativeDimension 1 (Polynomial.C : R →+* Polynomial R) := by
  have h : (Polynomial.C : R →+* Polynomial R).toAlgebra =
      (inferInstance : Algebra R (Polynomial R)) :=
    Algebra.algebra_ext _ _ (fun _ => rfl)
  change @Algebra.IsStandardSmoothOfRelativeDimension 1 R (Polynomial R) _ _
    (Polynomial.C : R →+* Polynomial R).toAlgebra
  rw [h]
  exact polynomial_standardSmooth R

/-- The actual affine-line structure morphism is smooth of relative dimension one. -/
instance polynomialSpec_smooth (R : Type*) [CommRing R] :
    IsSmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) := by
  apply (HasRingHomProperty.Spec_iff (P := @IsSmoothOfRelativeDimension 1)).mpr
  exact RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))
    _ (polynomialC_standardSmooth R)

end KltDP.Compatibility.PolynomialStandardSmooth
