import KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRepresentatives
import KltDP.Geometry.BirationalWeilClassPushforward

/-!
# The actual graph and fibre classes vanish under the original contraction

The previously computed M-degrees of the original embedded primes are
zero. The original all-prime criterion therefore supplies actual
factorizations through k-points for these same primes and the same map.
The established class pushforward then kills their singleton classes.
The original source, target, field triangle and criterion are retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreContractedWeilClasses

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreCanonicalWeilRepresentatives

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The actual contracting line has its already computed zero degree on the graph. -/
theorem graph_restrictionDegree_eq_zero :
    (graphPrimeCurve q n a ha hproj).restrictionDegree
      (contractingLine q n a ha hproj) = 0 := by
  have h := contractingClass_graph_degree q n a ha hproj
  rw [← contractingLine_class q n a ha hproj] at h
  change (graphPrimeCurve q n a ha hproj).picardRestrictionDegree
    (contractingLine q n a ha hproj).toPic = 0 at h
  simpa only [(graphPrimeCurve q n a ha hproj).picardRestrictionDegree_toPic] using h

/-- Each original strict special fibre has its already computed zero M-degree. -/
theorem fiber_restrictionDegree_eq_zero (i : Fin n) :
    (fiberPrimeCurve q n a ha hproj i).restrictionDegree
      (contractingLine q n a ha hproj) = 0 := by
  have h := fiberPrimeCurve_degree q n a ha hproj i
  rw [← contractingLine_class q n a ha hproj] at h
  change (fiberPrimeCurve q n a ha hproj i).picardRestrictionDegree
    (contractingLine q n a ha hproj).toPic = 0 at h
  simpa only [(fiberPrimeCurve q n a ha hproj i).picardRestrictionDegree_toPic] using h

variable {Y : NormalProjectiveSurface k}
    (π : (sourceSurface q n a ha hproj).toScheme ⟶ Y.toScheme) [IsProper π]
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hbir : IsBirationalScheme π)
    (hcriterion : ∀ C : (sourceSurface q n a ha hproj).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
      C.restrictionDegree (contractingLine q n a ha hproj) = 0)

include hπ hcriterion in
/-- The same original map kills the class of the actual embedded graph prime. -/
theorem graph_class_pushforward_eq_zero (z : ℤ) :
    BirationalWeilClassPushforward.pushforward
      (S := sourceSurface q n a ha hproj) (X := Y) π hbir
      ((sourceSurface q n a ha hproj).weilClassMap
        (Finsupp.single (graphPrimeCurve q n a ha hproj) z)) = 0 := by
  obtain ⟨p, hp, hpk⟩ := (hcriterion (graphPrimeCurve q n a ha hproj)).mpr
    (graph_restrictionDegree_eq_zero q n a ha hproj)
  exact BirationalWeilClassPushforward.pushforward_weilClassMap_single_contracted
    π hbir (graphPrimeCurve q n a ha hproj) z p hp hpk

include hπ hcriterion in
/-- The same original map kills each actual embedded special-fibre prime class. -/
theorem fiber_class_pushforward_eq_zero (i : Fin n) (z : ℤ) :
    BirationalWeilClassPushforward.pushforward
      (S := sourceSurface q n a ha hproj) (X := Y) π hbir
      ((sourceSurface q n a ha hproj).weilClassMap
        (Finsupp.single (fiberPrimeCurve q n a ha hproj i) z)) = 0 := by
  obtain ⟨p, hp, hpk⟩ := (hcriterion (fiberPrimeCurve q n a ha hproj i)).mpr
    (fiber_restrictionDegree_eq_zero q n a ha hproj i)
  exact BirationalWeilClassPushforward.pushforward_weilClassMap_single_contracted
    π hbir (fiberPrimeCurve q n a ha hproj i) z p hp hpk

end KltDP.Examples.FrobeniusMultiCentreContractedWeilClasses
