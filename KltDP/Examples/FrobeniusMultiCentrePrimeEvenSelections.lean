import KltDP.Examples.FrobeniusMultiCentreRetainedPrimeCurves
import KltDP.Examples.FrobeniusMultiCentreEvenSelections

/-!
# Integral Picard half-classes of the actual retained prime-curve selections

Every divisor here is a literal sum of the original prime curves' Cartier
divisors on the original smooth surface. Their proved class identities
transport the integral Picard parity classification and its explicit halves.
For three clusters the actual divisibility predicate selects precisely the
eight accepted binary selections, seven of them nonempty and all of weight
four. No contraction or singular-point correspondence is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentrePrimeEvenSelections

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreGraphExceptionalPairing FrobeniusMultiCentreRetainedGram
  FrobeniusMultiCentreRetainedPrimeCurves FrobeniusMultiCentreEvenSelections
  FrobeniusMultiCentrePicardRealization

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

section General

variable (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure 2 n a))

/-- The actual Cartier divisor of an original retained prime curve. -/
def retainedPrimeDivisor (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    CartierDivisor (multiSurfaceSurface 2 n a ha hproj).toScheme :=
  (multiSurfaceSurface 2 n a ha hproj).primeCurveCartier
    (multiSurfaceSurface_regularPoints 2 n a ha hproj) (retainedPrimeCurve n a ha hproj r)

theorem retainedPrimeDivisor_class (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    cartierPicardHom (multiSurfaceSurface 2 n a ha hproj).toScheme
      (retainedPrimeDivisor n a ha hproj r) = retainedClass n a ha r :=
  retainedPrimeCurve_cartierClass n a ha hproj r

/-- Independent selections of the original fibre and old-exceptional prime Cartier divisors. -/
def selectedPrimeNodeDivisor (A B : Finset (Fin n)) :
    CartierDivisor (multiSurfaceSurface 2 n a ha hproj).toScheme :=
  (∑ i ∈ A, retainedPrimeDivisor n a ha hproj (.inr (.inl i))) +
    ∑ i ∈ B, retainedPrimeDivisor n a ha hproj (.inr (.inr i))

theorem selectedPrimeNodeDivisor_class (A B : Finset (Fin n)) :
    cartierPicardHom (multiSurfaceSurface 2 n a ha hproj).toScheme
      (selectedPrimeNodeDivisor n a ha hproj A B) = selectedNodeClass n a ha A B := by
  rw [selectedPrimeNodeDivisor, map_add]
  simp only [map_sum, retainedPrimeDivisor_class n a ha hproj]
  rfl

/-- Actual prime-divisor selections are even exactly for matched even-cardinality branches. -/
theorem selectedPrimeNodeDivisor_even_iff (A B : Finset (Fin n)) :
    (∃ c : Additive (multiSurfaceSurface 2 n a ha hproj).toScheme.Pic,
      (2 : ℤ) • c = cartierPicardHom (multiSurfaceSurface 2 n a ha hproj).toScheme
        (selectedPrimeNodeDivisor n a ha hproj A B)) ↔ A = B ∧ Even A.card := by
  rw [selectedPrimeNodeDivisor_class]
  exact selectedNodeClass_two_divisible_iff n a ha hproj A B

/-- The accepted integral vector gives an explicit actual Picard half-class. -/
theorem selectedPrimeNodeDivisor_explicit_half (A : Finset (Fin n))
    (m : ℕ) (hm : A.card = m + m) :
    (2 : ℤ) • realization 1 n a
      ((m : ℤ) • FrobeniusPicard.b - ∑ i ∈ A, FrobeniusPicard.lastVectorTwo n i) =
      cartierPicardHom (multiSurfaceSurface 2 n a ha hproj).toScheme
        (selectedPrimeNodeDivisor n a ha hproj A A) := by
  rw [selectedPrimeNodeDivisor_class, selectedNodeClass_eq_realization, ← map_zsmul,
    FrobeniusEvenSets.selectedNodes_explicit_half n A m hm]

end General

section Seven

variable (a : Fin 3 → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure 2 3 a))

/-- A literal selection among the seven original retained prime Cartier divisors. -/
def sevenPrimeDivisor (s : FrobeniusSevenNodes.Selection) :
    CartierDivisor (multiSurfaceSurface 2 3 a ha hproj).toScheme :=
  (if s.1 then retainedPrimeDivisor 3 a ha hproj (.inl ()) else 0) +
    selectedPrimeNodeDivisor 3 a ha hproj s.2.1 s.2.2

theorem sevenPrimeDivisor_class (s : FrobeniusSevenNodes.Selection) :
    cartierPicardHom (multiSurfaceSurface 2 3 a ha hproj).toScheme
      (sevenPrimeDivisor a ha hproj s) = sevenSelectionClass a ha s := by
  cases hs : s.1 <;>
    simp [sevenPrimeDivisor, hs, map_add, sevenSelectionClass, retainedClass]
  · exact selectedPrimeNodeDivisor_class 3 a ha hproj s.2.1 s.2.2
  · exact congrArg₂ (fun x y : Additive (multiSurface 2 3 a).Pic => x + y)
      (retainedPrimeDivisor_class 3 a ha hproj (.inl ()))
      (selectedPrimeNodeDivisor_class 3 a ha hproj s.2.1 s.2.2)

/-- Complete integral Picard divisibility for the actual seven-prime Cartier selections. -/
theorem sevenPrimeDivisor_even_iff (s : FrobeniusSevenNodes.Selection) :
    (∃ c : Additive (multiSurfaceSurface 2 3 a ha hproj).toScheme.Pic,
      (2 : ℤ) • c = cartierPicardHom (multiSurfaceSurface 2 3 a ha hproj).toScheme
        (sevenPrimeDivisor a ha hproj s)) ↔ FrobeniusSevenNodes.parityConditions s := by
  rw [sevenPrimeDivisor_class]
  exact sevenSelectionClass_two_divisible_iff a ha hproj s

/-- An explicit integral Picard half-class for each even actual seven-prime selection. -/
theorem sevenPrimeDivisor_explicit_half (s : FrobeniusSevenNodes.Selection)
    (hs : FrobeniusSevenNodes.parityConditions s) :
    (2 : ℤ) • realization 1 3 a
      (FrobeniusSevenNodes.halfCoordinates (FrobeniusSevenNodes.selectionVector s)) =
      cartierPicardHom (multiSurfaceSurface 2 3 a ha hproj).toScheme
        (sevenPrimeDivisor a ha hproj s) := by
  rw [sevenPrimeDivisor_class]
  exact sevenSelectionClass_explicit_half a ha s hs

/-- The finite set defined by actual Picard divisibility of these original Cartier sums. -/
def evenPrimeSelections : Finset FrobeniusSevenNodes.Selection := by
  classical
  exact Finset.univ.filter (fun s =>
    ∃ c : Additive (multiSurfaceSurface 2 3 a ha hproj).toScheme.Pic,
      (2 : ℤ) • c = cartierPicardHom (multiSurfaceSurface 2 3 a ha hproj).toScheme
        (sevenPrimeDivisor a ha hproj s))

theorem evenPrimeSelections_eq :
    evenPrimeSelections a ha hproj = FrobeniusSevenNodes.divisibleSelections := by
  classical
  ext s
  simp only [evenPrimeSelections, FrobeniusSevenNodes.divisibleSelections,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact sevenPrimeDivisor_even_iff a ha hproj s

/-- Exactly eight binary selections, including the empty one, have actual Picard half-classes. -/
theorem evenPrimeSelections_card : (evenPrimeSelections a ha hproj).card = 8 := by
  rw [evenPrimeSelections_eq]
  exact FrobeniusSevenNodes.divisibleSelections_card

/-- Seven nonempty selections have actual integral Picard half-classes. -/
theorem nonempty_evenPrimeSelections_card :
    ((evenPrimeSelections a ha hproj).erase FrobeniusSevenNodes.emptySelection).card = 7 := by
  rw [evenPrimeSelections_eq]
  exact FrobeniusSevenNodes.nonempty_divisibleSelections_card

/-- Every nonempty even selection among these original prime curves contains four labels. -/
theorem nonempty_evenPrimeSelection_weight (s : FrobeniusSevenNodes.Selection)
    (hs : s ∈ evenPrimeSelections a ha hproj) (hne : s ≠ FrobeniusSevenNodes.emptySelection) :
    FrobeniusSevenNodes.selectionWeight s = 4 := by
  rw [evenPrimeSelections_eq] at hs
  have hp : FrobeniusSevenNodes.parityConditions s := by
    simpa only [FrobeniusSevenNodes.divisibleSelections, Finset.mem_filter,
      Finset.mem_univ, true_and] using hs
  rcases FrobeniusSevenNodes.selectionWeight_eq_zero_or_four s hp with hz | hf
  · exact (hne ((FrobeniusSevenNodes.selectionWeight_eq_zero_iff s).mp hz)).elim
  · exact hf

end Seven

end KltDP.Examples.FrobeniusMultiCentrePrimeEvenSelections
