import KltDP.Examples.FrobeniusMultiCentreRealizedCurveClasses
import KltDP.Examples.FrobeniusCharacteristicTwo

/-!
# The actual characteristic-two retained curves have negative definite Gram matrix

The graph, strict fibres and old exceptional components are independently
constructed embedded curves. Their original kernel classes realize the accepted
retained vectors, so their geometric matrix is the proved diagonal matrix.
For three clusters, all seven diagonal entries are minus two.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreRetainedGram

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptionalGlobalClasses
  FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreFiberGlobalClass
  FrobeniusMultiCentreGraphExceptionalPairing FrobeniusMultiCentrePicardRealization
  FrobeniusMultiCentreRealizedCurveClasses

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

local instance primeTwo : Fact (1 + 1).Prime := ⟨Nat.prime_two⟩

variable (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

/-- The original kernel classes of the graph, fibres and old exceptional components. -/
def retainedClass : FrobeniusCharacteristicTwo.RetainedLabel n → Additive (multiSurface 2 n a).Pic
  | .inl _ => -Additive.ofMul (multiGraphStrictKernelLine 1 n a ha).toPic
  | .inr (.inl i) => -Additive.ofMul (fiberKernelLine 1 n a ha i).toPic
  | .inr (.inr i) => -Additive.ofMul (exceptionalKernelLine 1 n a ha i (.inl (0 : Fin 1))).toPic

/-- The geometric retained classes have exactly the accepted integral vectors. -/
theorem retainedClass_eq_realization (i : FrobeniusCharacteristicTwo.RetainedLabel n) :
    retainedClass n a ha i = realization 1 n a (FrobeniusCharacteristicTwo.retainedVector n i) := by
  rcases i with i | (i | i)
  · exact (realization_graphVector 1 n a ha).symm
  · exact (realization_fiberVector 1 n a ha i).symm
  · exact (realization_nodeVector n a ha i).symm

variable (hproj : IsProjectiveOverField (multiStructure 2 n a))

/-- Every entry of the actual retained-curve intersection matrix. -/
theorem retainedClass_pairing (i j : FrobeniusCharacteristicTwo.RetainedLabel n) :
    multiPairing 2 n a ha hproj (retainedClass n a ha i) (retainedClass n a ha j) =
      if i = j then -FrobeniusCharacteristicTwo.retainedWeight n i else 0 := by
  rw [retainedClass_eq_realization, retainedClass_eq_realization,
    realization_preserves_pairing]
  exact FrobeniusCharacteristicTwo.retained_pairing n i j

/-- The rational matrix formed from the actual geometric intersection numbers. -/
def retainedGram : Matrix (FrobeniusCharacteristicTwo.RetainedLabel n)
    (FrobeniusCharacteristicTwo.RetainedLabel n) ℚ :=
  fun i j => (multiPairing 2 n a ha hproj (retainedClass n a ha i) (retainedClass n a ha j) : ℚ)

theorem retainedGram_eq : retainedGram n a ha hproj = FrobeniusCharacteristicTwo.retainedGram n := by
  ext i j
  simp only [retainedGram, FrobeniusCharacteristicTwo.retainedGram,
    retainedClass_pairing, FrobeniusCharacteristicTwo.retained_pairing]

/-- Negative definiteness of the actual retained-curve matrix for at least three clusters. -/
theorem retainedGram_negative_definite (hn : 3 ≤ n) : (-retainedGram n a ha hproj).PosDef := by
  rw [retainedGram_eq]
  exact FrobeniusCharacteristicTwo.retainedGram_negative_definite hn

variable (b : Fin 3 → k) (hb : Function.Injective b)
  (hproj3 : IsProjectiveOverField (multiStructure 2 3 b))

/-- The seven original retained curves have geometric pairing minus twice the identity. -/
theorem seven_retainedClass_pairing (i j : FrobeniusCharacteristicTwo.RetainedLabel 3) :
    multiPairing 2 3 b hb hproj3 (retainedClass 3 b hb i) (retainedClass 3 b hb j) =
      if i = j then -2 else 0 := by
  rw [retainedClass_pairing]
  rcases i with i | (i | i) <;> norm_num [FrobeniusCharacteristicTwo.retainedWeight]

end KltDP.Examples.FrobeniusMultiCentreRetainedGram
