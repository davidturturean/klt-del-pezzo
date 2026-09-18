import KltDP.Examples.FrobeniusDiscrepancyCandidate
import KltDP.Examples.FrobeniusMultiCentreContractedWeilClasses
import KltDP.Geometry.BirationalRationalWeilPushforward

/-!
The proposed actual discrepancy is supported on the original graph and
strict special fibres. Their proved original line degrees and the actual
contraction criterion give field-point factorizations, so the original
rational Weil pushforward kills this actual finite divisor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusDiscrepancyPushforward

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreSpecialNullCurves FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusMultiCentreContractedWeilClasses BirationalWeilPushforward

/-- The original criterion kills the rationalized singleton of each actual degree-zero prime. -/
theorem rationalPushforward_of_degree_zero
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))
    {Y : NormalProjectiveSurface k}
    (π : (sourceSurface q n a ha hproj).toScheme ⟶ Y.toScheme)
    [IsProper π] (hbir : IsBirationalScheme π)
    (hcriterion : ∀ C : (sourceSurface q n a ha hproj).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (contractingLine q n a ha hproj) = 0)
    (C : (sourceSurface q n a ha hproj).PrimeCurve)
    (hC : C.restrictionDegree (contractingLine q n a ha hproj) = 0) :
    rationalPushforward (S := sourceSurface q n a ha hproj) (X := Y) π hbir
      (rationalizeWeilDivisor (sourceSurface q n a ha hproj) (Finsupp.single C 1)) = 0 := by
  obtain ⟨p, hp, hpk⟩ := (hcriterion C).mpr hC
  exact (rationalPushforward_rationalize
      (S := sourceSurface q n a ha hproj) (X := Y) π hbir (Finsupp.single C 1)).trans
    ((congrArg (rationalizeWeilDivisor Y)
      (pushforward_single_contracted
        (S := sourceSurface q n a ha hproj) (X := Y) π hbir C 1 p hp hpk)).trans
        (rationalizeWeilDivisor Y).map_zero)

/-- The actual candidate finite divisor has zero original rational pushforward. -/
theorem candidate_pushforward_eq_zero
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))
    {Y : NormalProjectiveSurface k}
    (π : (sourceSurface q n a ha hproj).toScheme ⟶ Y.toScheme)
    [IsProper π] (hbir : IsBirationalScheme π)
    (hcriterion : ∀ C : (sourceSurface q n a ha hproj).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (contractingLine q n a ha hproj) = 0) :
    rationalPushforward (S := sourceSurface q n a ha hproj) (X := Y) π hbir
      (FrobeniusDiscrepancyBounds.candidate q n a ha hproj) = 0 := by
  let source : NormalProjectiveSurface k := sourceSurface q n a ha hproj
  have hB : rationalPushforward (S := source) (X := Y) π hbir
      (rationalizeWeilDivisor source (Finsupp.single (graphPrimeCurve q n a ha hproj) 1)) = 0 :=
    rationalPushforward_of_degree_zero q n a ha hproj π hbir hcriterion
      (graphPrimeCurve q n a ha hproj) (graph_restrictionDegree_eq_zero q n a ha hproj)
  have hF : ∀ i : Fin n, rationalPushforward (S := source) (X := Y) π hbir
      (rationalizeWeilDivisor source (Finsupp.single (fiberPrimeCurve q n a ha hproj i) 1)) = 0 :=
    fun i => rationalPushforward_of_degree_zero q n a ha hproj π hbir hcriterion
      (fiberPrimeCurve q n a ha hproj i) (fiber_restrictionDegree_eq_zero q n a ha hproj i)
  dsimp only [source] at hB hF
  simp only [FrobeniusDiscrepancyBounds.candidate, map_sub, map_smul, map_sum,
    hB, hF, Finset.sum_const_zero, smul_zero, sub_self]

end KltDP.Examples.FrobeniusDiscrepancyPushforward

#check @KltDP.Examples.FrobeniusDiscrepancyPushforward.rationalPushforward_of_degree_zero
#check @KltDP.Examples.FrobeniusDiscrepancyPushforward.candidate_pushforward_eq_zero
#print axioms KltDP.Examples.FrobeniusDiscrepancyPushforward.rationalPushforward_of_degree_zero
#print axioms KltDP.Examples.FrobeniusDiscrepancyPushforward.candidate_pushforward_eq_zero
