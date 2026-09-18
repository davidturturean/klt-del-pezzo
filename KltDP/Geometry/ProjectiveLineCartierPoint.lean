import KltDP.Geometry.IntegralRegularClosedPoint
import KltDP.Geometry.RegularCurvePointCartier
import KltDP.Geometry.CartierRationalPointDegree
import KltDP.Geometry.ProjectiveLineActualDegreeOne
import KltDP.Geometry.ProjectivePlane
import KltDP.Geometry.ProjectiveProper

/-! An actual original rational point on P1 whose Cartier divisor line
is the exact homogeneous O(1). The closed point, original section, kernel
identity, and sheaf comparison are constructed together for later
comparison with the actual finite fiber of a curve morphism. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveLineCartierPoint

variable (k : Type u) [Field k] [IsAlgClosed k]

local instance integral : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1

/-- The original rational point is a Cartier point with the actual O(1) line. -/
theorem exists_point :
    ∃ x : projectiveSpace k 1, ∃ hclosed : IsClosed ({x} : Set (projectiveSpace k 1)),
      ∃ E : CartierDivisor (projectiveSpace k 1),
      ∃ hE : HasRegularCartierEquations (projectiveSpace k 1) E,
        IsClosedImmersion (closedPointSection (projectiveSpaceToSpec k 1) x hclosed) ∧
        closedPointSection (projectiveSpaceToSpec k 1) x hclosed ≫
          projectiveSpaceToSpec k 1 = 𝟙 _ ∧
        (closedPointSection (projectiveSpaceToSpec k 1) x hclosed).ker =
          effectiveCartierIdealDataOfRegularEquations (projectiveSpace k 1) E hE ∧
        Nonempty (cartierDivisorModule (projectiveSpace k 1) E ≅
          (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1).obj) := by
  have hdim : topologicalKrullDim (projectiveSpace k 1) = 1 :=
    projectiveSpace_topologicalKrullDim k 1
  have hdim₂ : topologicalKrullDim (projectiveSpace k 1) ≤ 2 := by rw [hdim]; norm_num
  obtain ⟨x, hclosed, hregular⟩ :=
    IntegralRegularClosedPoint.exists_closed_regularPoint (projectiveSpaceToSpec k 1) hdim₂
  obtain ⟨E, hE, hker⟩ := RegularCurvePointCartier.exists_cartierDivisor
    (projectiveSpaceToSpec k 1) x hclosed hregular hdim
  let i := closedPointSection (projectiveSpaceToSpec k 1) x hclosed
  letI : IsClosedImmersion ((projectiveSpace k 1).fromSpecResidueField x) :=
    fromSpecResidueField_isClosedImmersion (projectiveSpace k 1) x hclosed
  letI : IsClosedImmersion i := by
    dsimp [i, closedPointSection]
    infer_instance
  have hi : i ≫ projectiveSpaceToSpec k 1 = 𝟙 _ :=
    closedPointSection_over_base (projectiveSpaceToSpec k 1) x hclosed
  refine ⟨x, hclosed, E, hE, inferInstance, hi, hker, ?_⟩
  apply ProjectiveLineActualDegreeOne.exists_iso_of_degree_one k
    (cartierDivisorInvertibleSheaf (projectiveSpace k 1) E)
  exact CartierRationalPoint.eulerDegree_eq_one E hE i hker
    (projectiveSpaceToSpec k 1) hdim.le hi

#print axioms exists_point

end KltDP.Geometry.ProjectiveLineCartierPoint
