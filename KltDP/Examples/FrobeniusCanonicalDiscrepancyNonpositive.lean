import KltDP.Examples.FrobeniusDiscrepancyNonpositive
import KltDP.Examples.FrobeniusDiscrepancyFormula

/-!
# Nonpositive coefficients of the actual compatible canonical difference

The original divisor equality applies to every source canonical Cartier
representative with the same exact original target pushforward. Its actual
Q-Cartier pullback difference has nonpositive coefficients at every prime.
This does not assert that a contracted image is singular.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusDiscrepancyFormula

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusMultiCentreSemiampleConstruction SmoothCanonicalExteriorComparison
open InvertibleSheafSectionPowers BirationalWeilPushforward

/-- Every coefficient of the actual original compatible canonical difference
is nonpositive, including the zero-coefficient old exceptional chains. -/
theorem discrepancy_coeff_nonpos
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hbir : IsBirationalScheme π)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (hcriterion : ∀ C : (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine q n a ha) = 0)
    (A : InvertibleSheaf Y.toScheme) (m : ℕ) (hm : 0 < m)
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj)
    (D : CartierDivisor (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme)
    (eD : cartierDivisorModule (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).toScheme D ≅
      relativeDifferentialExterior (multiStructure (q + 1) n a) 2)
    (hK : Y.QCartier (rationalizeWeilDivisor Y
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)))
    (hpush : pushforward
        (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
        (X := Y) π hbir
        ((sourceSurface q n a ha
          (originalMultiStructureProjective k (q + 1) n a)).cartierToWeilHom D) =
      targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    let source := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)
    let K := targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion
    ∀ C : source.PrimeCurve,
      (source.rationalCartierToWeilHom D -
        QCartierPullback.pullback (X := source) (Y := Y) π
          (rationalizeWeilDivisor Y K) hK) C ≤ 0 := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  intro source K C
  rw [discrepancy_formula q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e D eD hK hpush]
  exact FrobeniusDiscrepancyBounds.candidate_coeff_nonpos q n a ha
    (originalMultiStructureProjective k (q + 1) n a) hn C

end KltDP.Examples.FrobeniusDiscrepancyFormula

#print axioms KltDP.Examples.FrobeniusDiscrepancyFormula.discrepancy_coeff_nonpos
