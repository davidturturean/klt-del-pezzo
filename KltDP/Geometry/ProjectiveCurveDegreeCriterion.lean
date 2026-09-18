import KltDP.Geometry.ProjectiveCurveDegreeZero
import KltDP.Geometry.ProjectiveConstantDegree

/-!
# Degree zero exactly detects a projective map through a field point

Both implications refer to the original morphism and the original
Euler-difference degree of its pullback of degree one.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf
universe u

namespace KltDP.Geometry.ProjectiveCurveDegreeCriterion

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} [IsIntegral Y]
  (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hdim : topologicalKrullDim Y ≤ 1) {n : ℕ}
  (g : Y ⟶ projectiveSpace k n) (hgf : g ≫ projectiveSpaceToSpec k n = f)

include hdim hgf in
/-- The original pulled-back degree vanishes exactly when the original
projective morphism factors through a point over the original field. -/
theorem degree_zero_iff_factors_through_structure :
    (eulerCharacteristic f (pullbackInvertibleSheaf g (degreeOne k n)).obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0) ↔
    ∃ p : Spec (CommRingCat.of k) ⟶ projectiveSpace k n,
      g = f ≫ p ∧ p ≫ projectiveSpaceToSpec k n = 𝟙 _ := by
  constructor
  · exact ProjectiveCurveDegreeZero.factors_through_structure_of_degree_zero f hdim g hgf
  · rintro ⟨p, hg, _⟩
    exact ProjectiveConstantDegree.eulerDifference_eq_zero_of_factor f p g hg

end KltDP.Geometry.ProjectiveCurveDegreeCriterion
