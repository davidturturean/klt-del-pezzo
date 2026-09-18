import KltDP.Examples.FrobeniusMultiCentreNullFiberReduction
import KltDP.Examples.FrobeniusMultiCentreSpecialNullCurves
import KltDP.Examples.ProjectiveLineClosedPoints
import KltDP.Examples.FrobeniusNonspecialRulingPrimeCurve
import KltDP.Examples.FrobeniusInfinityRulingPrimeCurve

/-!
# The complete original M-null prime-curve classification

Every original off-graph M-null prime has a closed ruling image and is
geometrically disjoint from the original strict graph. Closed points of
the original projective line are finite or infinity. Nonspecial finite
and infinity fibers meet the graph, so their actual prime curves cannot
be null. The proved special-fiber classification leaves exactly the
original strict fibers and the old exceptional components. The reverse
implication uses the previously computed actual restriction degrees.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusMultiCentreNullCurveClassification

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusGraphClosed FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreExceptionalPrime FrobeniusMultiCentreContractingClass
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreNullFiberReduction
open FrobeniusMultiCentreSpecialNullCurves ProjectiveLineClosedPoints
open FrobeniusNonspecialRulingPrimeCurve FrobeniusInfinityRulingPrimeCurve

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The complete list of actual original prime curves with zero M-degree. -/
theorem null_degree_iff (hn : 2 < n)
    (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve) :
    (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom C
        (contractingClass q n a ha) = 0 ↔
      C = graphPrimeCurve q n a ha hproj ∨
      (∃ i : Fin n, C = fiberPrimeCurve q n a ha hproj i) ∨
      ∃ (i : Fin n) (j : Fin q),
        C = exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj := by
  classical
  constructor
  · intro hnull
    by_cases hgraph : C = graphPrimeCurve q n a ha hproj
    · exact Or.inl hgraph
    obtain ⟨z, hz, hheight, hdisj⟩ :=
      null_curve_closed_fiber_and_disjoint q n a ha hproj C hn hgraph hnull
    rcases eq_point_or_eq_infinity z hz with ⟨c, rfl⟩ | rfl
    · by_cases hselected : ∃ i : Fin n, c = a i ^ (q + 1)
      · obtain ⟨i, rfl⟩ := hselected
        rcases null_curve_over_selected_height q n a ha hproj i C hheight hnull with
          hF | ⟨j, hE⟩
        · exact Or.inr (Or.inl ⟨i, hF⟩)
        · exact Or.inr (Or.inr ⟨i, j, hE⟩)
      · exact (finite_primeCurve_not_disjoint_graphStrict q n a ha hproj C c
          (fun i hi => hselected ⟨i, hi⟩) hheight hdisj).elim
    · exact (infinity_primeCurve_not_disjoint_graphStrict q n a ha hproj C
        hheight hdisj).elim
  · rintro (rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩)
    · exact contractingClass_graph_degree q n a ha hproj
    · exact fiberPrimeCurve_degree q n a ha hproj i
    · exact exceptionalPrimeCurve_degree q n a ha hproj i (.inl j)

/-- The same classification uses the independently defined actual line-bundle degree. -/
theorem restrictionDegree_eq_zero_iff (hn : 2 < n)
    (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve) :
    C.restrictionDegree (contractingLine q n a ha hproj) = 0 ↔
      C = graphPrimeCurve q n a ha hproj ∨
      (∃ i : Fin n, C = fiberPrimeCurve q n a ha hproj i) ∨
      ∃ (i : Fin n) (j : Fin q),
        C = exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj := by
  have h := null_degree_iff q n a ha hproj hn C
  rw [← contractingLine_class q n a ha hproj] at h
  change C.picardRestrictionDegree (contractingLine q n a ha hproj).toPic = 0 ↔ _ at h
  simpa only [C.picardRestrictionDegree_toPic] using h

end KltDP.Examples.FrobeniusMultiCentreNullCurveClassification
