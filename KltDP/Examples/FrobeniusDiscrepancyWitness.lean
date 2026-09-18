import KltDP.Examples.FrobeniusDiscrepancyFormula
import KltDP.Examples.FrobeniusDiscrepancyBounds
import KltDP.Examples.FrobeniusMultiCentreCompatibleCanonical
import KltDP.Examples.FrobeniusMultiCentreTargetQCartier

/-!
The actual original contraction supplies the source canonical Cartier
representative and target Q-Cartier proof used in the discrepancy formula.
The resulting actual discrepancy has every coefficient greater than -1
and coefficient zero on every original old exceptional component.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusDiscrepancyWitness

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusMultiCentreSemiampleConstruction FrobeniusMultiCentreExceptionalPrime
open SmoothCanonicalExteriorComparison InvertibleSheafSectionPowers
open BirationalWeilPushforward

/-- The original positive-power contraction has an actual compatible canonical
representative with the exact discrepancy formula and strict coefficient bounds. -/
theorem exists_discrepancy_witness
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
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    let source := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)
    let K := targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion
    ∃ (D : CartierDivisor source.toScheme)
      (hK : Y.QCartier (rationalizeWeilDivisor Y K)),
      Nonempty (cartierDivisorModule source.toScheme D ≅
        relativeDifferentialExterior (multiStructure (q + 1) n a) 2) ∧
      pushforward (S := source) (X := Y) π hbir (source.cartierToWeilHom D) = K ∧
      let Δ := source.rationalCartierToWeilHom D -
        QCartierPullback.pullback (X := source) (Y := Y) π (rationalizeWeilDivisor Y K) hK
      Δ = FrobeniusDiscrepancyBounds.candidate q n a ha
          (originalMultiStructureProjective k (q + 1) n a) ∧
      (∀ C : source.PrimeCurve, (-1 : ℚ) < Δ C) ∧
      (∀ (i : Fin n) (j : Fin q),
        Δ (exceptionalPrimeCurveSPn q n a ha i (.inl j)
          (originalMultiStructureProjective k (q + 1) n a)) = 0) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let hproj := originalMultiStructureProjective k (q + 1) n a
  obtain ⟨D, ⟨eD⟩, hpush⟩ :=
    FrobeniusMultiCentreCompatibleCanonical.exists_compatible_canonical_cartier
      q n a ha hn Y π hπ hbir hconnected hcriterion
  let hK := FrobeniusMultiCentreTargetQCartier.targetCanonicalWeil_qCartier
    q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
  have hformula := FrobeniusDiscrepancyFormula.discrepancy_formula
    q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e D eD hK hpush
  refine ⟨D, hK, ⟨eD⟩, hpush, hformula, ?_, ?_⟩
  · intro C
    rw [hformula]
    exact FrobeniusDiscrepancyBounds.candidate_coeff_gt_neg_one q n a ha hproj hn C
  · intro i j
    rw [hformula]
    exact FrobeniusDiscrepancyBounds.candidate_old_exceptional_eq_zero q n a ha hproj i j

end KltDP.Examples.FrobeniusDiscrepancyWitness

#check @KltDP.Examples.FrobeniusDiscrepancyWitness.exists_discrepancy_witness

#print axioms KltDP.Examples.FrobeniusDiscrepancyWitness.exists_discrepancy_witness
