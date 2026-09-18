import KltDP.Examples.FrobeniusCanonicalRationalRelation
import KltDP.Examples.FrobeniusTargetCanonicalPullbackClass
import KltDP.Examples.FrobeniusDiscrepancyPushforward
import KltDP.Geometry.DiscrepancyRationalRelation
import KltDP.Geometry.BirationalDifferencePushforward
import KltDP.Geometry.BirationalQLinearRigidity

/-!
The actual source exterior-square representative and actual Q-Cartier
target pullback have the stated original finite discrepancy divisor.
The source and target class formulas give rational linear equivalence;
both actual rational pushforwards are zero, so proved principal rigidity
gives equality of the original divisors, coefficient by coefficient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusDiscrepancyFormula

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreSemiampleConstruction SmoothCanonicalExteriorComparison
open InvertibleSheafSectionPowers BirationalWeilPushforward

/-- The actual canonical discrepancy is rationally linearly equivalent
to the explicit original graph and special-fibre divisor. -/
theorem discrepancy_qLinearlyEquivalent_candidate
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
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion))) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    let source := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)
    let K := targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion
    source.QLinearlyEquivalent
      (source.rationalCartierToWeilHom D -
        QCartierPullback.pullback (X := source) (Y := Y) π (rationalizeWeilDivisor Y K) hK)
      (FrobeniusDiscrepancyBounds.candidate q n a ha
        (originalMultiStructureProjective k (q + 1) n a)) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let hproj := originalMultiStructureProjective k (q + 1) n a
  let source := sourceSurface q n a ha hproj
  apply (source.rationalWeilClassMap_eq_iff _ _).mp
  simp only [FrobeniusDiscrepancyBounds.candidate, map_sub, map_smul]
  have hsource := FrobeniusCanonicalRationalRelation.canonical_module_rational_relation
    q n a ha hproj D eD
  have htarget := FrobeniusTargetCanonicalPullbackClass.target_canonical_pullback_class
    q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hK
  have hp0 : ((q + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero q)
  have hnQ : (2 : ℚ) < n := by exact_mod_cast hn
  have hr0 : (n : ℚ) - 2 ≠ 0 := ne_of_gt (sub_pos.mpr hnQ)
  exact DiscrepancyRationalRelation.solve ((q + 1 : ℕ) : ℚ) ((n : ℚ) - 2)
    (2 - (((q + 1 : ℕ) : ℚ) - 2) * ((n : ℚ) - 2)) hp0 hr0 _ _ _
    (source.rationalWeilClassMap (rationalizeWeilDivisor source (contractingWeil q n a ha hproj))) _
    (by simpa only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat] using hsource)
    (by simpa only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat] using htarget)

set_option Elab.async false in
/-- The equality is of actual rational Weil divisors. The only representative
data are the actual exterior-square isomorphism and exact original pushed divisor. -/
theorem discrepancy_formula
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
    source.rationalCartierToWeilHom D -
        QCartierPullback.pullback (X := source) (Y := Y) π (rationalizeWeilDivisor Y K) hK =
      FrobeniusDiscrepancyBounds.candidate q n a ha
        (originalMultiStructureProjective k (q + 1) n a) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let hproj : IsProjectiveOverField (multiStructure (q + 1) n a) :=
    originalMultiStructureProjective k (q + 1) n a
  let source : NormalProjectiveSurface k := sourceSurface q n a ha hproj
  let K : Y.WeilDivisor := targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion
  have hlin : source.QLinearlyEquivalent
      (source.rationalCartierToWeilHom D -
        QCartierPullback.pullback (X := source) (Y := Y) π (rationalizeWeilDivisor Y K) hK)
      (FrobeniusDiscrepancyBounds.candidate q n a ha hproj) :=
    discrepancy_qLinearlyEquivalent_candidate
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e D eD hK
  have hpush' : pushforward (S := source) (X := Y) π hbir
      (source.cartierToWeilHom D) = K := hpush
  have hzero : rationalPushforward (S := source) (X := Y) π hbir
      (rationalizeWeilDivisor source (source.cartierToWeilHom D) -
        QCartierPullback.pullback (X := source) (Y := Y) π (rationalizeWeilDivisor Y K) hK) = 0 :=
    rationalPushforward_difference_pullback_eq_zero
      (S := source) (X := Y) π hbir (source.cartierToWeilHom D) K hK hpush'
  have hcandidate : rationalPushforward (S := source) (X := Y) π hbir
      (FrobeniusDiscrepancyBounds.candidate q n a ha hproj) = 0 :=
    FrobeniusDiscrepancyPushforward.candidate_pushforward_eq_zero
      q n a ha hproj π hbir hcriterion
  exact eq_of_qLinearlyEquivalent_of_rationalPushforward_eq
    (S := source) (X := Y) π hbir
    (source.rationalCartierToWeilHom D -
      QCartierPullback.pullback (X := source) (Y := Y) π (rationalizeWeilDivisor Y K) hK)
    (FrobeniusDiscrepancyBounds.candidate q n a ha hproj)
    hlin (hzero.trans hcandidate.symm)

end KltDP.Examples.FrobeniusDiscrepancyFormula

#check @KltDP.Examples.FrobeniusDiscrepancyFormula.discrepancy_qLinearlyEquivalent_candidate
#check @KltDP.Examples.FrobeniusDiscrepancyFormula.discrepancy_formula

#print axioms KltDP.Examples.FrobeniusDiscrepancyFormula.discrepancy_qLinearlyEquivalent_candidate
#print axioms KltDP.Examples.FrobeniusDiscrepancyFormula.discrepancy_formula
