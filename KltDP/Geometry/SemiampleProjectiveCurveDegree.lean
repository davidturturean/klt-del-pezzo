import KltDP.Geometry.SemiampleProjectiveRestriction
import KltDP.Geometry.ProjectiveCurveDegreeCriterion
import KltDP.Geometry.CurvePositiveDegreeBig

/-!
# The numerical criterion for a curve under an actual semiample power map

The degree of the original projective degree-one pullback is the positive
power exponent times the original restriction degree of L. The original
curve map factors through a k-point exactly when this restriction degree
vanishes. The map and all coefficient sheaves are the already constructed ones.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.SemiampleProjectiveMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSheafSectionPowersPullback ProjectiveSpaceDegreeOneSheaf ModuleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : InvertibleSheaf X)
  (f : X ⟶ Spec (CommRingCat.of k)) (D : PowerSystem L)
  {Y : Scheme.{u}} (j : Y ⟶ X) [IsProper (j ≫ f)]
  (hdim : topologicalKrullDim Y ≤ 1)

include hdim in
/-- The actual pullback of projective degree one has the original
restriction degree multiplied by the actual power exponent. -/
theorem PowerSystem.restricted_degreeOne_degree :
    eulerCharacteristic (j ≫ f)
        (pullbackInvertibleSheaf (j ≫ PowerSystem.toProjective L f D)
          (degreeOne k D.dimension)).obj -
      eulerCharacteristic (j ≫ f) (_root_.SheafOfModules.unit Y.ringCatSheaf) =
    (D.exponent : ℤ) *
      (eulerCharacteristic (j ≫ f) (pullbackInvertibleSheaf j L).obj -
        eulerCharacteristic (j ≫ f) (_root_.SheafOfModules.unit Y.ringCatSheaf)) := by
  let e := PowerSystem.restrictedDegreeOneIso L f D j ≪≫
    powerPullbackIso j L D.exponent
  rw [eulerCharacteristic_eq_of_iso (j ≫ f) e,
    CurvePositiveDegreeBig.eulerCharacteristic_power (j ≫ f) hdim]
  ring

include hdim in
/-- On an original integral proper curve, the actual power-system map
factors through a point exactly when the original L restriction has degree zero. -/
theorem PowerSystem.restriction_factors_iff_degree_zero [IsAlgClosed k] [IsIntegral Y] :
    (∃ p : Spec (CommRingCat.of k) ⟶ projectiveSpace k D.dimension,
      j ≫ PowerSystem.toProjective L f D = (j ≫ f) ≫ p ∧
        p ≫ projectiveSpaceToSpec k D.dimension = 𝟙 _) ↔
    eulerCharacteristic (j ≫ f) (pullbackInvertibleSheaf j L).obj -
      eulerCharacteristic (j ≫ f) (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0 := by
  have hgf : (j ≫ PowerSystem.toProjective L f D) ≫
      projectiveSpaceToSpec k D.dimension = j ≫ f := by
    rw [Category.assoc, PowerSystem.toProjective_structure]
  have hc := ProjectiveCurveDegreeCriterion.degree_zero_iff_factors_through_structure
    (j ≫ f) hdim (j ≫ PowerSystem.toProjective L f D) hgf
  rw [← hc, PowerSystem.restricted_degreeOne_degree L f D j hdim, mul_eq_zero]
  have hm : (D.exponent : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt D.positive)
  simp only [hm, false_or]

end KltDP.Geometry.SemiampleProjectiveMap
