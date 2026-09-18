import KltDP.Geometry.FrobeniusTargetSmoothDivisorOpen
import KltDP.Geometry.SmoothOpenCanonicalWeil
import KltDP.Geometry.PrimeCurveExistence

/-!
The same original Frobenius target has a canonical Weil representative
constructed from its actual smooth image-complement open. Nonemptiness,
integrality and relative smoothness of this open are all derived. The
Cartier representative is built from the actual differential sheaf, then
its actual local equations give the target Weil coefficients. No desired
ample expression or pushforward divisor defines the result.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
  (Y : NormalProjectiveSurface k) (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
  [IsProper π]

include hn in
/-- An existing actual target prime supplies a point of the original open;
no nonemptiness premise is required of the contraction. -/
theorem nullImageComplement_nonempty
    (hcriterion : ∀ C : (multiSurfaceSurface (q + 1) n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine q n a ha) = 0) :
    Nonempty (nullImageComplement q n a ha π).toScheme := by
  obtain ⟨C⟩ := Y.primeCurve_nonempty
  exact ⟨⟨C.genericPoint,
    genericPoint_mem_nullImageComplement q n a ha hn Y π hcriterion C⟩⟩

section Construction

variable [Surjective π] [IsIso π.c]

variable (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
  (hbir : letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    IsBirationalScheme π)
  (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
  (hcriterion : ∀ C : (multiSurfaceSurface (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
    (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
      C.restrictionDegree (originalLine q n a ha) = 0)

include hπ hbir hconnected hcriterion

/-- The actual canonical Cartier representative on the derived smooth open. -/
def targetCanonicalCartier :
    letI : Nonempty (nullImageComplement q n a ha π).toScheme :=
      nullImageComplement_nonempty q n a ha hn Y π hcriterion
    letI : IsIntegral (nullImageComplement q n a ha π).toScheme :=
      isIntegral_of_isOpenImmersion (nullImageComplement q n a ha π).ι
    CartierDivisor (nullImageComplement q n a ha π).toScheme := by
  letI : Nonempty (nullImageComplement q n a ha π).toScheme :=
    nullImageComplement_nonempty q n a ha hn Y π hcriterion
  letI : IsIntegral (nullImageComplement q n a ha π).toScheme :=
    isIntegral_of_isOpenImmersion (nullImageComplement q n a ha π).ι
  letI : IsSmoothOfRelativeDimension 2
      ((nullImageComplement q n a ha π).ι ≫ Y.structureMorphism) :=
    (nullImageComplement_smoothTwo_contains_primeGenericPoints
      q n a ha hn Y π hπ hbir hconnected hcriterion).1
  exact SmoothOpenCanonicalWeil.cartierRepresentative Y (nullImageComplement q n a ha π)

/-- The actual canonical Weil representative on the original target surface. -/
def targetCanonicalWeil : Y.WeilDivisor := by
  letI : Nonempty (nullImageComplement q n a ha π).toScheme :=
    nullImageComplement_nonempty q n a ha hn Y π hcriterion
  letI : IsSmoothOfRelativeDimension 2
      ((nullImageComplement q n a ha π).ι ≫ Y.structureMorphism) :=
    (nullImageComplement_smoothTwo_contains_primeGenericPoints
      q n a ha hn Y π hπ hbir hconnected hcriterion).1
  exact SmoothOpenCanonicalWeil.weilRepresentative Y (nullImageComplement q n a ha π)

/-- The chosen original Cartier sheaf is the intrinsic second exterior
power of relative differentials on the original image-complement open. -/
def targetCanonicalCartierIsoExterior :
    letI : Nonempty (nullImageComplement q n a ha π).toScheme :=
      nullImageComplement_nonempty q n a ha hn Y π hcriterion
    letI : IsIntegral (nullImageComplement q n a ha π).toScheme :=
      isIntegral_of_isOpenImmersion (nullImageComplement q n a ha π).ι
    cartierDivisorModule (nullImageComplement q n a ha π).toScheme
      (targetCanonicalCartier q n a ha hn Y π hπ hbir hconnected hcriterion) ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        ((nullImageComplement q n a ha π).ι ≫ Y.structureMorphism) 2 := by
  letI : Nonempty (nullImageComplement q n a ha π).toScheme :=
    nullImageComplement_nonempty q n a ha hn Y π hcriterion
  letI : IsIntegral (nullImageComplement q n a ha π).toScheme :=
    isIntegral_of_isOpenImmersion (nullImageComplement q n a ha π).ι
  letI : IsSmoothOfRelativeDimension 2
      ((nullImageComplement q n a ha π).ι ≫ Y.structureMorphism) :=
    (nullImageComplement_smoothTwo_contains_primeGenericPoints
      q n a ha hn Y π hπ hbir hconnected hcriterion).1
  exact SmoothOpenCanonicalWeil.representativeIsoExterior Y (nullImageComplement q n a ha π)

/-- The target representative uses exactly the original local-equation
Cartier-to-Weil map on the original smooth open. -/
theorem targetCanonicalWeil_eq_restrictedWeilHom :
    letI : Nonempty (nullImageComplement q n a ha π).toScheme :=
      nullImageComplement_nonempty q n a ha hn Y π hcriterion
    letI : IsIntegral (nullImageComplement q n a ha π).toScheme :=
      isIntegral_of_isOpenImmersion (nullImageComplement q n a ha π).ι
    targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion =
      OpenCartierWeil.restrictedWeilHom (nullImageComplement q n a ha π)
        (targetCanonicalCartier q n a ha hn Y π hπ hbir hconnected hcriterion) := rfl

/-- Every original target coefficient is an order of an actual transported
local equation of the canonical Cartier representative. -/
theorem targetCanonicalWeil_apply (C : Y.PrimeCurve) :
    letI : Nonempty (nullImageComplement q n a ha π).toScheme :=
      nullImageComplement_nonempty q n a ha hn Y π hcriterion
    letI : IsIntegral (nullImageComplement q n a ha π).toScheme :=
      isIntegral_of_isOpenImmersion (nullImageComplement q n a ha π).ι
    targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion C =
      C.order (OpenCartierWeil.restrictedEquation (nullImageComplement q n a ha π)
        (targetCanonicalCartier q n a ha hn Y π hπ hbir hconnected hcriterion)
        ⟨C.genericPoint,
          genericPoint_mem_nullImageComplement q n a ha hn Y π hcriterion C⟩) := by
  letI : Nonempty (nullImageComplement q n a ha π).toScheme :=
    nullImageComplement_nonempty q n a ha hn Y π hcriterion
  letI : IsSmoothOfRelativeDimension 2
      ((nullImageComplement q n a ha π).ι ≫ Y.structureMorphism) :=
    (nullImageComplement_smoothTwo_contains_primeGenericPoints
      q n a ha hn Y π hπ hbir hconnected hcriterion).1
  exact SmoothOpenCanonicalWeil.weilRepresentative_apply Y (nullImageComplement q n a ha π) C
    (genericPoint_mem_nullImageComplement q n a ha hn Y π hcriterion C)

end Construction

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
