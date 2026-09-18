import KltDP.Geometry.RegularCurvePointCartier
import KltDP.Geometry.CartierRationalPointDegree
import KltDP.Geometry.ProjectiveLineActualDegreeOne
import KltDP.Geometry.ProjectivePlane
import KltDP.Geometry.ProjectiveProper

/-! Every original closed point of P1 has its canonical Cartier divisor
and the exact homogeneous O(1) line. Normality, Noetherianity, and the
actual dimension prove regularity at every point; no chosen regular
locus or field-J2 input is needed for this target-curve adapter. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveLineClosedPointCartier

variable (k : Type u) [Field k]

local instance integral : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1

/-- All actual P1 stalks are regular by their normality and dimension. -/
theorem regularPoint (x : projectiveSpace k 1) : RegularPoint (projectiveSpace k 1) x := by
  letI : IsLocallyNoetherian (projectiveSpace k 1) := projectiveSpace_isLocallyNoetherian k 1
  letI : IsNoetherianRing ((projectiveSpace k 1).presheaf.stalk x) :=
    isNoetherianRing_stalk_of_isLocallyNoetherian (projectiveSpace k 1) x
  apply regularPoint_of_normal_of_ringKrullDim_le_one (projectiveSpace k 1)
    (projectiveSpace_isNormalScheme k 1) x
  exact (ringKrullDim_stalk_le_topologicalKrullDim (projectiveSpace k 1) x).trans
    (ProjectiveLineDegree.dim_le_one k)

/-- The exact given closed point, with its original kernel and actual O(1) line. -/
theorem exists_cartierDivisor [IsAlgClosed k] (x : projectiveSpace k 1)
    (hclosed : IsClosed ({x} : Set (projectiveSpace k 1))) :
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
  obtain ⟨E, hE, hker⟩ := RegularCurvePointCartier.exists_cartierDivisor
    (projectiveSpaceToSpec k 1) x hclosed (regularPoint k x) hdim
  let i := closedPointSection (projectiveSpaceToSpec k 1) x hclosed
  letI : IsClosedImmersion ((projectiveSpace k 1).fromSpecResidueField x) :=
    fromSpecResidueField_isClosedImmersion (projectiveSpace k 1) x hclosed
  letI : IsClosedImmersion i := by
    dsimp [i, closedPointSection]
    infer_instance
  have hi : i ≫ projectiveSpaceToSpec k 1 = 𝟙 _ :=
    closedPointSection_over_base (projectiveSpaceToSpec k 1) x hclosed
  refine ⟨E, hE, inferInstance, hi, hker, ?_⟩
  apply ProjectiveLineActualDegreeOne.exists_iso_of_degree_one k
    (cartierDivisorInvertibleSheaf (projectiveSpace k 1) E)
  exact CartierRationalPoint.eulerDegree_eq_one E hE i hker
    (projectiveSpaceToSpec k 1) hdim.le hi

#print axioms regularPoint
#print axioms exists_cartierDivisor

end KltDP.Geometry.ProjectiveLineClosedPointCartier
