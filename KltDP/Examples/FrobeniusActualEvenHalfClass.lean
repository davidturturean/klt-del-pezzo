import KltDP.Examples.FrobeniusMultiCentreProjectiveSevenConfiguration

/-!
# The explicit half-class in the original Picard group

Expand the already proved half-vector through the original class realization.
The ruling is the actual pulled ruling line, and the last total exceptional
class is the original exterior component class by `newestClass_SPn`.
Projectivity is supplied by its proved original-surface producer.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusActualEvenHalfClass

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptionalGlobalClasses
  FrobeniusMultiCentrePicardRealization FrobeniusMultiCentreRealizedCurveClasses
  FrobeniusMultiCentreProjectiveSevenConfiguration FrobeniusProjectivityProved

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
  (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

/-- The literal original prime-divisor sum has half-class
`(|A| / 2) b - ∑ i ∈ A, Pᵢ` in the original integral Picard group. -/
theorem selected_prime_divisor_explicit_half (A : Finset (Fin n)) (hA : Even A.card) :
    (2 : ℤ) • (((A.card / 2 : ℕ) : ℤ) • multiSecondFiberClass 2 n a -
      ∑ i ∈ A, exceptionalClass 2 n a i (1 : Fin 2)) =
      cartierPicardHom (surface n a ha).toScheme
        ((∑ i ∈ A, primeDivisor n a ha (.inr (.inl i))) +
          ∑ i ∈ A, primeDivisor n a ha (.inr (.inr i))) := by
  obtain ⟨m, hm⟩ := hA
  have hdiv : A.card / 2 = m := by omega
  have h := FrobeniusMultiCentrePrimeEvenSelections.selectedPrimeNodeDivisor_explicit_half
    n a ha (originalMultiStructureProjective k 2 n a) A m hm
  simpa only [map_sub, map_zsmul, map_sum, realization_secondFiber,
    FrobeniusPicard.lastVectorTwo, realization_exceptional, hdiv,
    FrobeniusMultiCentrePrimeEvenSelections.selectedPrimeNodeDivisor, primeDivisor] using h

end KltDP.Examples.FrobeniusActualEvenHalfClass
