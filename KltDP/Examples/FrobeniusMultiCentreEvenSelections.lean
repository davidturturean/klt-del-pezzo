import KltDP.Examples.FrobeniusMultiCentrePicardCoordinates
import KltDP.Examples.FrobeniusMultiCentreRealizedCurveClasses

/-!
# Even selections of the actual characteristic-two graph, fibres and old exceptional curves

The selections here are sums of the independently constructed original curve
kernel classes in the global Picard group. Their proved realization identities
and the integral intersection-coordinate retraction transport the accepted
lattice parity classification in both directions. The explicit half-vectors
therefore yield actual Picard half-classes. No contraction or singular-surface
correspondence is asserted by these Picard calculations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreEvenSelections

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptionalGlobalClasses
  FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreFiberGlobalClass
  FrobeniusMultiCentrePicardRealization FrobeniusMultiCentrePicardCoordinates
  FrobeniusMultiCentreRealizedCurveClasses

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

local instance primeTwo : Fact (1 + 1).Prime := ⟨Nat.prime_two⟩

variable (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

/-- Independent selections of the original strict fibres and original old exceptional curves. -/
def selectedNodeClass (A B : Finset (Fin n)) : Additive (multiSurface 2 n a).Pic :=
  (∑ i ∈ A, -Additive.ofMul (fiberKernelLine 1 n a ha i).toPic) +
    ∑ i ∈ B, -Additive.ofMul (exceptionalKernelLine 1 n a ha i (.inl (0 : Fin 1))).toPic

/-- The independently defined geometric selection has the accepted integral selection vector. -/
theorem selectedNodeClass_eq_realization (A B : Finset (Fin n)) :
    selectedNodeClass n a ha A B =
      realization 1 n a (FrobeniusEvenSets.selectedNodes n A B) := by
  rw [FrobeniusEvenSets.selectedNodes, map_add]
  simp only [map_sum, realization_fiberVector 1 n a ha, realization_nodeVector n a ha]
  rfl

/-- Actual Picard divisibility holds exactly for matched selections of even cardinality. -/
theorem selectedNodeClass_two_divisible_iff
    (hproj : IsProjectiveOverField (multiStructure 2 n a)) (A B : Finset (Fin n)) :
    (∃ c : Additive (multiSurface 2 n a).Pic, (2 : ℤ) • c = selectedNodeClass n a ha A B) ↔
      A = B ∧ Even A.card := by
  rw [selectedNodeClass_eq_realization, realization_divisible_iff 1 n a ha hproj]
  exact FrobeniusEvenSets.selectedNodes_two_divisible_iff n A B

variable (b : Fin 3 → k) (hb : Function.Injective b)

/-- A selection among the original graph and the six original fibre/old-exceptional curves. -/
def sevenSelectionClass (s : FrobeniusSevenNodes.Selection) : Additive (multiSurface 2 3 b).Pic :=
  (if s.1 then -Additive.ofMul (multiGraphStrictKernelLine 1 3 b hb).toPic else 0) +
    selectedNodeClass 3 b hb s.2.1 s.2.2

/-- All seven original curve classes have the accepted selection-vector coordinates. -/
theorem sevenSelectionClass_eq_realization (s : FrobeniusSevenNodes.Selection) :
    sevenSelectionClass b hb s = realization 1 3 b (FrobeniusSevenNodes.selectionVector s) := by
  cases hs : s.1 <;>
    simp [sevenSelectionClass, FrobeniusSevenNodes.selectionVector, hs, map_add,
      realization_graphVector 1 3 b hb, selectedNodeClass_eq_realization]

/-- The complete seven-selection parity classification in the actual global Picard group. -/
theorem sevenSelectionClass_two_divisible_iff
    (hproj : IsProjectiveOverField (multiStructure 2 3 b)) (s : FrobeniusSevenNodes.Selection) :
    (∃ c : Additive (multiSurface 2 3 b).Pic, (2 : ℤ) • c = sevenSelectionClass b hb s) ↔
      FrobeniusSevenNodes.parityConditions s := by
  rw [sevenSelectionClass_eq_realization, realization_divisible_iff 1 3 b hb hproj]
  exact FrobeniusSevenNodes.selection_two_divisible_iff s

/-- The accepted explicit half-vector gives an actual Picard half-class of every even selection. -/
theorem sevenSelectionClass_explicit_half (s : FrobeniusSevenNodes.Selection)
    (hs : FrobeniusSevenNodes.parityConditions s) :
    (2 : ℤ) • realization 1 3 b (FrobeniusSevenNodes.halfCoordinates
      (FrobeniusSevenNodes.selectionVector s)) = sevenSelectionClass b hb s := by
  rw [← map_zsmul, FrobeniusSevenNodes.selection_explicit_half s hs,
    sevenSelectionClass_eq_realization]

end KltDP.Examples.FrobeniusMultiCentreEvenSelections
