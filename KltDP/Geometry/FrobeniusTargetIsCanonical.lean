import KltDP.Geometry.CanonicalWeilDivisor
import KltDP.Geometry.FrobeniusTargetCanonicalWeil

/-!
# The original Frobenius target divisor is canonical

Use its actual smooth image-complement open, actual top-differential Cartier
representative and original restricted Cartier-to-Weil map. No formula for
an ample or numerical class enters the canonical-divisor definition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved

/-- The previously constructed original target Weil divisor represents
the actual top differential sheaf on its proved smooth large open. -/
theorem targetCanonicalWeil_isCanonical
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k) (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hbir : letI : IsIntegral (multiSurface (q + 1) n a) :=
        multiSurface_isIntegral (q + 1) n a ha
      IsBirationalScheme π)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (hcriterion : ∀ C : (multiSurfaceSurface (q + 1) n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine q n a ha) = 0) :
    IsCanonicalWeilDivisor Y
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion) := by
  letI : Nonempty (nullImageComplement q n a ha π).toScheme :=
    nullImageComplement_nonempty q n a ha hn Y π hcriterion
  letI : IsIntegral (nullImageComplement q n a ha π).toScheme :=
    isIntegral_of_isOpenImmersion (nullImageComplement q n a ha π).ι
  have hU := nullImageComplement_smoothTwo_contains_primeGenericPoints
    q n a ha hn Y π hπ hbir hconnected hcriterion
  letI : IsSmoothOfRelativeDimension 2
      ((nullImageComplement q n a ha π).ι ≫ Y.structureMorphism) := hU.1
  have hcan := IsCanonicalWeilDivisor.of_smooth_open Y (nullImageComplement q n a ha π)
    hU.2 (targetCanonicalCartier q n a ha hn Y π hπ hbir hconnected hcriterion)
    (targetCanonicalCartierIsoExterior q n a ha hn Y π hπ hbir hconnected hcriterion)
  have hEq : targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion =
      OpenCartierWeil.restrictedWeilHom (nullImageComplement q n a ha π)
        (targetCanonicalCartier q n a ha hn Y π hπ hbir hconnected hcriterion) :=
    targetCanonicalWeil_eq_restrictedWeilHom q n a ha hn Y π hπ hbir hconnected hcriterion
  exact hEq.symm ▸ hcan

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

#check @KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.targetCanonicalWeil_isCanonical
#print axioms KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.targetCanonicalWeil_isCanonical
