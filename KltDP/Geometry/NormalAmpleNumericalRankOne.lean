import KltDP.Geometry.NormalNumericalRankOne
import KltDP.Geometry.AmpleCurveRestrictionPositive
import KltDP.Geometry.PrimeCurveExistence

/-!
An original ample invertible sheaf supplies the nonzero numerical class:
there is an actual prime curve, and its original restriction degree is
strictly positive. Only the rational Weil spanning statement remains as
input for the separately proved construction-specific consumer.
-/

noncomputable section

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- An actual ample generator of rational Weil classes gives rank one
and finite dimensionality for the original numerical Picard quotient. -/
theorem numericalRankOne_of_ample_weilClass_span
    (A : InvertibleSheaf X.toScheme) (hA : AmpleSerre.IsAmple A)
    (hspan : ∀ w : X.RationalWeilClassGroup, ∃ q : ℚ,
      w = q • X.weilClassRationalization
        (X.picardToWeilClassHom (Additive.ofMul A.toPic))) :
    X.NumericalSpaceFiniteDimensional ∧ X.picardRank = 1 := by
  obtain ⟨C⟩ := X.primeCurve_nonempty
  have hdegree : 0 < C.picardRestrictionDegree A.toPic := by
    rw [C.picardRestrictionDegree_toPic]
    exact AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple X A hA C
  exact X.numericalRankOne_of_weilClass_span (Additive.ofMul A.toPic) hspan C
    (ne_of_gt hdegree)

end KltDP.Geometry.NormalProjectiveSurface
