import KltDP.Geometry.SemiampleProjectiveRealization
import KltDP.Geometry.ProjectiveMapTrivialPullback
import KltDP.Geometry.InvertibleSheafSectionPowersPullback

/-!
# The actual power-system map on a trivial restriction

The original pullback composition identifies degree one along a restricted
power-system map with the actual restricted power. A unit frame for the
original restriction tensors to a unit frame for this power. On a connected
reduced proper source, the restricted map therefore factors through a k-point.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.SemiampleProjectiveMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSheafSectionPowers InvertibleSheafSectionPowersPullback
open ProjectiveSpaceDegreeOneSheaf

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : InvertibleSheaf X)
  (f : X ⟶ Spec (CommRingCat.of k)) (D : PowerSystem L)

/-- Restricting the original projective map realizes the original restricted power. -/
def PowerSystem.restrictedDegreeOneIso {Y : Scheme.{u}} (j : Y ⟶ X) :
    (pullbackInvertibleSheaf (j ≫ PowerSystem.toProjective L f D)
      (degreeOne k D.dimension)).obj ≅
        (pullbackInvertibleSheaf j (power L D.exponent)).obj :=
  ((schemeModulePullbackCompIso j (PowerSystem.toProjective L f D)).app
    (degreeOne k D.dimension).obj).symm ≪≫
      (schemeModulePullback j).mapIso (PowerSystem.toProjective_pullbackDegreeOneIso L f D)

/-- A trivial original restriction forces the actual power-system map on
that connected reduced proper scheme to factor through a point over k. -/
theorem PowerSystem.restriction_factors_through_structure [IsAlgClosed k]
    {Y : Scheme.{u}} [IsReduced Y] [ConnectedSpace Y] (j : Y ⟶ X)
    [IsProper (j ≫ f)]
    (e : (pullbackInvertibleSheaf j L).obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) :
    ∃ p : Spec (CommRingCat.of k) ⟶ projectiveSpace k D.dimension,
      j ≫ PowerSystem.toProjective L f D = (j ≫ f) ≫ p ∧
        p ≫ projectiveSpaceToSpec k D.dimension = 𝟙 _ := by
  let ePower := powerPullbackIso j L D.exponent ≪≫
    powerFrame (pullbackInvertibleSheaf j L) e D.exponent
  apply ProjectiveMapTrivialPullback.factors_through_structure (j ≫ f)
    (j ≫ PowerSystem.toProjective L f D)
    (PowerSystem.restrictedDegreeOneIso L f D j ≪≫ ePower)
  rw [Category.assoc, PowerSystem.toProjective_structure]

end KltDP.Geometry.SemiampleProjectiveMap
