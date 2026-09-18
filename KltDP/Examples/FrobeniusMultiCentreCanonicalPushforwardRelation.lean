import KltDP.Examples.FrobeniusMultiCentreContractedWeilClasses
import KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRelation
import KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

/-!
# Pushforward of the original integral canonical Weil relation

Apply the established class pushforward to the actual source divisor
relation. The original graph and special-fibre classes vanish by their
proved degrees and the unchanged all-prime contraction criterion. This
leaves only the pushforwards of the actual canonical and M representatives.
The final endpoint supplies original source projectivity and uses the
original contracting line. Target canonical identification and ample-line
pullback compatibility are separate subsequent statements.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalPushforwardRelation

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusMultiCentreCanonicalWeilRelation
open FrobeniusMultiCentreContractedWeilClasses
open FrobeniusProjectivityProved FrobeniusMultiCentreSemiampleConstruction

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

section General

variable (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))
    {Y : NormalProjectiveSurface k}
    (π : (sourceSurface q n a ha hproj).toScheme ⟶ Y.toScheme) [IsProper π]
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hbir : IsBirationalScheme π)
    (hcriterion : ∀ C : (sourceSurface q n a ha hproj).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
      C.restrictionDegree (contractingLine q n a ha hproj) = 0)

include hπ hcriterion in
/-- The actual source relation pushes to the two retained target Weil classes.
The graph and fibre terms are eliminated by proved factorizations, not hypotheses. -/
theorem pushforward_canonical_relation :
    let p : ℤ := (q + 1 : ℕ)
    let r : ℤ := (n : ℤ) - 2
    let s : ℤ := p * r
    let d : ℤ := 2 - (p - 2) * r
    s • BirationalWeilClassPushforward.pushforward
        (S := sourceSurface q n a ha hproj) (X := Y) π hbir
        ((sourceSurface q n a ha hproj).weilClassMap (canonicalWeil q n a ha hproj)) +
      d • BirationalWeilClassPushforward.pushforward
        (S := sourceSurface q n a ha hproj) (X := Y) π hbir
        ((sourceSurface q n a ha hproj).weilClassMap (contractingWeil q n a ha hproj)) = 0 := by
  have h := congrArg (BirationalWeilClassPushforward.pushforward
      (S := sourceSurface q n a ha hproj) (X := Y) π hbir)
    (canonicalRelationDivisor_class_eq_zero q n a ha hproj)
  simpa only [canonicalRelationDivisor, map_add, map_zsmul, map_sum, map_zero,
    graph_class_pushforward_eq_zero q n a ha hproj π hπ hbir hcriterion,
    fiber_class_pushforward_eq_zero q n a ha hproj π hπ hbir hcriterion,
    Finset.sum_const_zero, smul_zero, add_zero] using h

end General

section Original

variable {Y : NormalProjectiveSurface k}
    (π : (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ Y.toScheme) [IsProper π]
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hbir : IsBirationalScheme π)
    (hcriterion : ∀ C : (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
      C.restrictionDegree (originalLine q n a ha) = 0)

include hπ hcriterion in
/-- The same original contraction satisfies the pushed canonical relation with
source projectivity supplied and its original all-prime criterion unchanged. -/
theorem original_pushforward_canonical_relation :
    let hproj := originalMultiStructureProjective k (q + 1) n a
    let p : ℤ := (q + 1 : ℕ)
    let r : ℤ := (n : ℤ) - 2
    let s : ℤ := p * r
    let d : ℤ := 2 - (p - 2) * r
    s • BirationalWeilClassPushforward.pushforward
        (S := sourceSurface q n a ha hproj) (X := Y) π hbir
        ((sourceSurface q n a ha hproj).weilClassMap (canonicalWeil q n a ha hproj)) +
      d • BirationalWeilClassPushforward.pushforward
        (S := sourceSurface q n a ha hproj) (X := Y) π hbir
        ((sourceSurface q n a ha hproj).weilClassMap (contractingWeil q n a ha hproj)) = 0 :=
  pushforward_canonical_relation q n a ha
    (originalMultiStructureProjective k (q + 1) n a) π hπ hbir hcriterion

end Original

end KltDP.Examples.FrobeniusMultiCentreCanonicalPushforwardRelation
