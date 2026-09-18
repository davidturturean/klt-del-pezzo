import KltDP.Examples.FrobeniusProjectivityProved
import KltDP.Examples.FrobeniusMultiCentreSevenPrimeCurves
import KltDP.Examples.FrobeniusMultiCentrePrimeEvenSelections

/-!
# Original seven curves and integral even sets with proved projectivity

The original multi-centre projectivity producer supplies the projectivity
argument in the already proved prime-curve and integral Picard constructions.
The surfaces, structure maps, embedded curves and Cartier classes are the
original objects. No projectivity premise remains in the definitions or
theorems below. The original field, characteristic and distinct-centre
hypotheses are retained.

This consumes the separately reviewed projectivity source. It proves a
configuration on the original smooth projective surface, without asserting
a contraction, a singular surface, or a singular-point count.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreProjectiveSevenConfiguration

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreGraphExceptionalPairing FrobeniusMultiCentreRetainedCurves
open FrobeniusMultiCentreRetainedGram FrobeniusMultiCentrePicardRealization
open FrobeniusProjectivityProved

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

section General

variable (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

/-- The original characteristic-two multi-centre surface, now with its
projectivity supplied by the actual original-surface producer. -/
def surface : NormalProjectiveSurface k :=
  multiSurfaceSurface 2 n a ha (originalMultiStructureProjective k 2 n a)

theorem surface_toScheme : (surface n a ha).toScheme = multiSurface 2 n a := rfl

theorem surface_structureMorphism :
    (surface n a ha).structureMorphism = multiStructure 2 n a := rfl

theorem surface_smoothTwo :
    IsSmoothOfRelativeDimension 2 (surface n a ha).structureMorphism :=
  multiStructure_smoothTwo 2 n a ha

theorem surface_regularPoints :
    ∀ x : (surface n a ha).Point, RegularPoint (surface n a ha).toScheme x :=
  multiSurfaceSurface_regularPoints 2 n a ha (originalMultiStructureProjective k 2 n a)

/-- The previously constructed original retained prime curve. -/
def primeCurve (r : FrobeniusCharacteristicTwo.RetainedLabel n) : (surface n a ha).PrimeCurve :=
  FrobeniusMultiCentreRetainedPrimeCurves.retainedPrimeCurve n a ha
    (originalMultiStructureProjective k 2 n a) r

/-- Its support is the range of the original retained closed immersion. -/
theorem primeCurve_support (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (primeCurve n a ha r : Set (surface n a ha).toScheme) =
      Set.range (retainedInclusion n a r).base := rfl

theorem primeCurve_injective : Function.Injective (primeCurve n a ha) :=
  FrobeniusMultiCentreRetainedPrimeCurves.retainedPrimeCurve_injective n a ha
    (originalMultiStructureProjective k 2 n a)

def primeCurveIsoProjectiveLine (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (primeCurve n a ha r).toScheme ≅ projectiveSpace k 1 :=
  FrobeniusMultiCentreRetainedPrimeCurves.retainedPrimeIsoProjectiveLine n a ha
    (originalMultiStructureProjective k 2 n a) r

theorem primeCurveIsoProjectiveLine_hom_structure
    (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (primeCurveIsoProjectiveLine n a ha r).hom ≫ projectiveSpaceToSpec k 1 =
      (primeCurve n a ha r).toSpec :=
  FrobeniusMultiCentreRetainedPrimeCurves.retainedPrimeIsoProjectiveLine_hom_structure
    n a ha (originalMultiStructureProjective k 2 n a) r

/-- The actual intrinsic Cartier divisor of this original prime curve. -/
def primeDivisor (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    CartierDivisor (surface n a ha).toScheme :=
  FrobeniusMultiCentrePrimeEvenSelections.retainedPrimeDivisor n a ha
    (originalMultiStructureProjective k 2 n a) r

theorem primeDivisor_eq (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    primeDivisor n a ha r =
      (surface n a ha).primeCurveCartier (surface_regularPoints n a ha)
        (primeCurve n a ha r) := rfl

/-- The intrinsic Cartier class is the independently computed original class. -/
theorem primeDivisor_class (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    cartierPicardHom (surface n a ha).toScheme (primeDivisor n a ha r) =
      retainedClass n a ha r :=
  FrobeniusMultiCentrePrimeEvenSelections.retainedPrimeDivisor_class n a ha
    (originalMultiStructureProjective k 2 n a) r

end General

section Seven

variable (a : Fin 3 → k) (ha : Function.Injective a)

/-- The actual original seven-prime intersection matrix is minus twice the identity. -/
theorem sevenCurve_intersectionNumber (r s : FrobeniusCharacteristicTwo.RetainedLabel 3) :
    (primeCurve 3 a ha r).intersectionNumber (primeDivisor 3 a ha s) =
      if r = s then -2 else 0 :=
  FrobeniusMultiCentreSevenPrimeCurves.sevenPrimeCurve_intersectionNumber a ha
    (originalMultiStructureProjective k 2 3 a) r s

/-- Seven distinct original curves have disjoint supports, are smooth over
the original field, are projective lines over that field, and have square -2. -/
theorem sevenCurve_configuration :
    Fintype.card (FrobeniusCharacteristicTwo.RetainedLabel 3) = 7 ∧
    Function.Injective (primeCurve 3 a ha) ∧
    (∀ r s : FrobeniusCharacteristicTwo.RetainedLabel 3, r ≠ s →
      Disjoint (primeCurve 3 a ha r : Set (surface 3 a ha).toScheme)
        (primeCurve 3 a ha s : Set (surface 3 a ha).toScheme)) ∧
    (∀ r : FrobeniusCharacteristicTwo.RetainedLabel 3,
      IsSmooth (primeCurve 3 a ha r).toSpec ∧
      (∃ e : (primeCurve 3 a ha r).toScheme ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = (primeCurve 3 a ha r).toSpec) ∧
      (primeCurve 3 a ha r).selfIntersectionNumber (surface_regularPoints 3 a ha) = -2) :=
  FrobeniusMultiCentreSevenPrimeCurves.sevenPrimeCurve_configuration a ha
    (originalMultiStructureProjective k 2 3 a)

/-- A literal binary selection of the seven original prime Cartier divisors. -/
def sevenDivisor (s : FrobeniusSevenNodes.Selection) : CartierDivisor (surface 3 a ha).toScheme :=
  FrobeniusMultiCentrePrimeEvenSelections.sevenPrimeDivisor a ha
    (originalMultiStructureProjective k 2 3 a) s

theorem sevenDivisor_eq (s : FrobeniusSevenNodes.Selection) :
    sevenDivisor a ha s =
      (if s.1 then primeDivisor 3 a ha (.inl ()) else 0) +
        ((∑ i ∈ s.2.1, primeDivisor 3 a ha (.inr (.inl i))) +
          ∑ i ∈ s.2.2, primeDivisor 3 a ha (.inr (.inr i))) := rfl

/-- Integral Picard divisibility of the actual Cartier selection is classified
by the proved binary parity conditions, without a projectivity premise. -/
theorem sevenDivisor_even_iff (s : FrobeniusSevenNodes.Selection) :
    (∃ c : Additive (surface 3 a ha).toScheme.Pic,
      (2 : ℤ) • c = cartierPicardHom (surface 3 a ha).toScheme (sevenDivisor a ha s)) ↔
        FrobeniusSevenNodes.parityConditions s :=
  FrobeniusMultiCentrePrimeEvenSelections.sevenPrimeDivisor_even_iff a ha
    (originalMultiStructureProjective k 2 3 a) s

/-- The original explicit integral half-vector realized in the actual Picard group. -/
def halfClass (s : FrobeniusSevenNodes.Selection) : Additive (surface 3 a ha).toScheme.Pic :=
  realization 1 3 a
    (FrobeniusSevenNodes.halfCoordinates (FrobeniusSevenNodes.selectionVector s))

theorem two_smul_halfClass (s : FrobeniusSevenNodes.Selection)
    (hs : FrobeniusSevenNodes.parityConditions s) :
    (2 : ℤ) • halfClass a ha s =
      cartierPicardHom (surface 3 a ha).toScheme (sevenDivisor a ha s) :=
  FrobeniusMultiCentrePrimeEvenSelections.sevenPrimeDivisor_explicit_half a ha
    (originalMultiStructureProjective k 2 3 a) s hs

/-- This finite set is defined by actual integral Picard divisibility. -/
def evenSelections : Finset FrobeniusSevenNodes.Selection :=
  FrobeniusMultiCentrePrimeEvenSelections.evenPrimeSelections a ha
    (originalMultiStructureProjective k 2 3 a)

theorem evenSelections_eq : evenSelections a ha = FrobeniusSevenNodes.divisibleSelections :=
  FrobeniusMultiCentrePrimeEvenSelections.evenPrimeSelections_eq a ha
    (originalMultiStructureProjective k 2 3 a)

theorem evenSelections_card : (evenSelections a ha).card = 8 :=
  FrobeniusMultiCentrePrimeEvenSelections.evenPrimeSelections_card a ha
    (originalMultiStructureProjective k 2 3 a)

theorem nonempty_evenSelections_card :
    ((evenSelections a ha).erase FrobeniusSevenNodes.emptySelection).card = 7 :=
  FrobeniusMultiCentrePrimeEvenSelections.nonempty_evenPrimeSelections_card a ha
    (originalMultiStructureProjective k 2 3 a)

theorem nonempty_evenSelection_weight (s : FrobeniusSevenNodes.Selection)
    (hs : s ∈ evenSelections a ha) (hne : s ≠ FrobeniusSevenNodes.emptySelection) :
    FrobeniusSevenNodes.selectionWeight s = 4 :=
  FrobeniusMultiCentrePrimeEvenSelections.nonempty_evenPrimeSelection_weight a ha
    (originalMultiStructureProjective k 2 3 a) s hs hne

end Seven

end KltDP.Examples.FrobeniusMultiCentreProjectiveSevenConfiguration
