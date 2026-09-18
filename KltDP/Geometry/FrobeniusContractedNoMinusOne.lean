import KltDP.Examples.FrobeniusContractedPrimeSelfIntersection
import KltDP.Geometry.FrobeniusMultiCentreNormalNullPrimes

/-!
For the same original Frobenius contraction, its proved all-prime label
criterion and the actual intrinsic self-intersections show that every
contracted prime has square at most minus two. Original projectivity and
regularity are supplied by their existing producers. This is only the
no-contracted-minus-one-prime conclusion; no singularity classification
or minimal-resolution assertion is made.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreExceptionalPrime FrobeniusContractedPrimeSelfIntersection

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
  {Y : Scheme.{u}} (σ : Y ⟶ Spec (CommRingCat.of k))
  (π : multiSurface (q + 1) n a ⟶ Y)
  (hlabels : ∀ C : (multiSurfaceSurface (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
    (∃ p : Spec (CommRingCat.of k) ⟶ Y,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) ↔
    C = graphPrimeCurve q n a ha (originalMultiStructureProjective k (q + 1) n a) ∨
    (∃ i : Fin n, C = fiberPrimeCurve q n a ha
      (originalMultiStructureProjective k (q + 1) n a) i) ∨
    ∃ (i : Fin n) (j : Fin q), C = exceptionalPrimeCurveSPn q n a ha i (.inl j)
      (originalMultiStructureProjective k (q + 1) n a))

include hn hlabels

/-- Every actually contracted original prime has intrinsic square at most minus two. -/
theorem contracted_selfIntersectionNumber_le_neg_two
    (C : (multiSurfaceSurface (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve)
    (hC : ∃ p : Spec (CommRingCat.of k) ⟶ Y,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) :
    C.selfIntersectionNumber (multiSurfaceSurface_regularPoints (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a)) ≤ -2 :=
  selfIntersectionNumber_le_neg_two_of_labels q n a ha
    (originalMultiStructureProjective k (q + 1) n a) hn C ((hlabels C).mp hC)

/-- In particular the same original map contracts no prime of square minus one. -/
theorem contracted_selfIntersectionNumber_ne_neg_one
    (C : (multiSurfaceSurface (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve)
    (hC : ∃ p : Spec (CommRingCat.of k) ⟶ Y,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) :
    C.selfIntersectionNumber (multiSurfaceSurface_regularPoints (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a)) ≠ -1 := by
  have h := contracted_selfIntersectionNumber_le_neg_two q n a ha hn σ π hlabels C hC
  omega

/-- There is no contracted minus-one prime among the original surface's primes. -/
theorem no_contracted_minus_one_prime :
    ¬ ∃ C : (multiSurfaceSurface (q + 1) n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) ∧
      C.selfIntersectionNumber (multiSurfaceSurface_regularPoints (q + 1) n a ha
        (originalMultiStructureProjective k (q + 1) n a)) = -1 := by
  rintro ⟨C, hC, hself⟩
  exact contracted_selfIntersectionNumber_ne_neg_one q n a ha hn σ π hlabels C hC hself

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
