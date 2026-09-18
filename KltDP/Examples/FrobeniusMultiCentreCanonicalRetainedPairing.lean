import KltDP.Examples.FrobeniusMultiCentreCanonicalExplicit
import KltDP.Examples.FrobeniusMultiCentreRetainedGram

/-!
# Actual canonical intersections with the original retained curves

The original global canonical formula identifies the actual atlas canonical
class with the realization of the existing integral canonical vector. The
already proved geometric realization and retained-curve class comparisons
then compute its intersections. No canonical formula or pairing is supplied
as an assumption. For three characteristic-two clusters the actual canonical
and anticanonical classes are orthogonal to all seven original retained curves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalRetainedPairing

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreGraphExceptionalPairing FrobeniusMultiCentreGraphFiberNumericalValues
open FrobeniusMultiCentreRulingPairing FrobeniusMultiCentrePicardRealization
open FrobeniusMultiCentreCanonicalOpenComparison FrobeniusMultiCentreCanonicalExplicit
open FrobeniusMultiCentreRetainedGram

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The actual canonical class realizes the original integral canonical vector. -/
theorem multiCanonicalClass_eq_realization (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) :
    multiCanonicalClass (q + 1) n a ha =
      realization q n a (FrobeniusPicard.canonicalVector (q + 1) n) := by
  rw [multiCanonicalClass_eq_fibers_exceptionals, pullback_firstFiberClass,
    pullback_secondFiberClass, realization_apply]
  simp only [FrobeniusPicard.canonicalVector, one_zsmul]

private theorem canonicalVector_retained_pairing (n : ℕ)
    (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    FrobeniusPicard.pairing (FrobeniusPicard.canonicalVector 2 n)
        (FrobeniusCharacteristicTwo.retainedVector n r) =
      FrobeniusCharacteristicTwo.retainedWeight n r - 2 := by
  rcases r with r | (i | i)
  · simpa only [FrobeniusCharacteristicTwo.retainedVector,
      FrobeniusCharacteristicTwo.retainedWeight] using
      FrobeniusPicard.pairing_canonical_graph 2 n
  · simpa only [FrobeniusCharacteristicTwo.retainedVector,
      FrobeniusCharacteristicTwo.retainedWeight] using
      FrobeniusPicard.pairing_canonical_fiber 2 n i
  · rw [FrobeniusCharacteristicTwo.retainedVector, FrobeniusPicard.pairing_comm,
      FrobeniusPicard.nodeVector, FrobeniusPicard.pairing_difference_left]
    norm_num [FrobeniusPicard.canonicalVector, FrobeniusCharacteristicTwo.retainedWeight]

variable [CharP k 2]

local instance canonicalRetainedPrimeTwo : Fact (1 + 1).Prime := ⟨Nat.prime_two⟩

/-- The actual canonical degree of each original retained class is its weight minus two. -/
theorem canonical_retained_pairing (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure 2 n a))
    (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    multiPairing 2 n a ha hproj (multiCanonicalClass 2 n a ha) (retainedClass n a ha r) =
      FrobeniusCharacteristicTwo.retainedWeight n r - 2 := by
  rw [multiCanonicalClass_eq_realization 1 n a ha, retainedClass_eq_realization,
    realization_preserves_pairing]
  exact canonicalVector_retained_pairing n r

/-- The opposite actual canonical class has the opposite original retained degrees. -/
theorem anticanonical_retained_pairing (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure 2 n a))
    (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    multiPairing 2 n a ha hproj (-multiCanonicalClass 2 n a ha) (retainedClass n a ha r) =
      2 - FrobeniusCharacteristicTwo.retainedWeight n r := by
  change multiPairingHom 1 n a ha hproj (retainedClass n a ha r)
    (-multiCanonicalClass 2 n a ha) = _
  rw [map_neg, multiPairingHom_apply, canonical_retained_pairing]
  omega

/-- Every one of the seven original retained classes has actual canonical degree zero. -/
theorem seven_canonical_retained_pairing (a : Fin 3 → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure 2 3 a))
    (r : FrobeniusCharacteristicTwo.RetainedLabel 3) :
    multiPairing 2 3 a ha hproj (multiCanonicalClass 2 3 a ha) (retainedClass 3 a ha r) = 0 := by
  rw [canonical_retained_pairing]
  rcases r with r | r <;> norm_num [FrobeniusCharacteristicTwo.retainedWeight]

/-- The actual anticanonical class is orthogonal to the seven original retained classes. -/
theorem seven_anticanonical_retained_pairing (a : Fin 3 → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure 2 3 a))
    (r : FrobeniusCharacteristicTwo.RetainedLabel 3) :
    multiPairing 2 3 a ha hproj (-multiCanonicalClass 2 3 a ha) (retainedClass 3 a ha r) = 0 := by
  rw [anticanonical_retained_pairing]
  rcases r with r | r <;> norm_num [FrobeniusCharacteristicTwo.retainedWeight]

end KltDP.Examples.FrobeniusMultiCentreCanonicalRetainedPairing
