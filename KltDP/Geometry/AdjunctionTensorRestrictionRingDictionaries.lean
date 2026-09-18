import KltDP.Geometry.AdjunctionTensorRestrictionRingEquation

/-!
# Normalize quotient ring dictionaries before specializing chart section rings

The compiled ring equation already contains the literal original quotient map.
Normalize its two remaining quotient dictionary presentations to the projection
from `Ideal.Quotient.commSemiring`, matching the original chart-source expansion.
All normalization takes place over abstract ambient rings and their actual map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.AdjunctionTensorRestrictionRingDictionaries

private theorem quotient_semiring_eq (A : Type u) [CommRing A] (J : Ideal A) :
    Ideal.Quotient.semiring J = (Ideal.Quotient.commSemiring J).toSemiring := rfl

private theorem quotient_commSemiring_eq (A : Type u) [CommRing A] (J : Ideal A) :
    (Ideal.Quotient.commRing J).toCommSemiring = Ideal.Quotient.commSemiring J := rfl

/-- The original generic equation with the quotient dictionaries in the same
normal form as the original Kähler refinement hom. -/
def ring_square (R : Type u) [CommRing R] {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    {φ : A →+* B} {J : Ideal A} {J' : Ideal B} (hφ : J ≤ J'.comap φ)
    (d : J) (hJ : Ideal.span {(d : A)} = J)
    (hd : (d : A) ∈ nonZeroDivisors A)
    (hJ' : Ideal.span {φ (d : A)} = J')
    (hd' : φ (d : A) ∈ nonZeroDivisors B) :=
  let _ : Algebra A B := φ.toAlgebra
  fun (hTower : IsScalarTower R A B)
      (hA : Algebra.IsStandardSmoothOfRelativeDimension 2 R A)
      (hB : Algebra.IsStandardSmoothOfRelativeDimension 2 R B)
      (hQ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J))
      (hQ' : Algebra.IsStandardSmoothOfRelativeDimension 1 R (B ⧸ J'))
      (hOpen : IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap J' φ hφ)))) => by
    have h := AdjunctionTensorRestrictionRingEquation.ring_square R hφ
      d hJ hd hJ' hd' hTower hA hB hQ hQ' hOpen
    simp only [quotient_semiring_eq, quotient_commSemiring_eq] at h
    exact h

end KltDP.Geometry.AdjunctionTensorRestrictionRingDictionaries
