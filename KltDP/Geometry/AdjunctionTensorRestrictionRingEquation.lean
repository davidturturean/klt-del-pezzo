import KltDP.Geometry.NormalTwistedAdjunctionTensorChartRestriction

/-!
# Normalize the original restriction equation before specializing section rings

The original generic tensor-chart theorem is used with the algebra induced
by its actual ambient ring homomorphism. Normalize only the two quotient-map
presentations in that generic equation. No scheme chart or section-ring
carrier is substituted in this producer.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.AdjunctionTensorRestrictionRingEquation

open KltDP.RingTheory.SmoothPrincipalDeterminantRestriction

private theorem native_equation {α : Sort*} {a b : α} (h : a = b) : a = b := h

/-- The original generic adjunction restriction equation with the literal
ideal quotient of its original ambient ring homomorphism. -/
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
    letI : IsScalarTower R A B := hTower
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 R A := hA
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 R B := hB
    letI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J) := hQ
    letI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (B ⧸ J') := hQ'
    letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (quotientMap A B J J' hφ))) := hOpen
    have h := native_equation (NormalTwistedAdjunctionTensorChartRestriction.iso_restriction
      R A B J J' hφ d hJ hd hJ' hd')
    simp only [quotientMap, RingHom.algebraMap_toAlgebra] at h
    exact h

end KltDP.Geometry.AdjunctionTensorRestrictionRingEquation
