import KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf
import KltDP.Geometry.AffinePIDInvertibleTrivial
import KltDP.Geometry.PicardEulerValue

/-!
# The original degree-one pullback of a map through a field point

An invertible sheaf on the original field spectrum has an actual unit
frame by the existing affine PID theorem. Original pullback composition
then gives a unit frame along every map factoring through that spectrum.
Its original Euler difference is consequently zero.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ProjectiveConstantDegree

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open ProjectiveSpaceDegreeOneSheaf ModuleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) {n : ℕ}
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k n)

/-- The actual degree-one sheaf restricts trivially along a map through
the original field spectrum. -/
def pullbackDegreeOneUnitIso :
    (pullbackInvertibleSheaf (f ≫ p) (degreeOne k n)).obj ≅
      _root_.SheafOfModules.unit X.ringCatSheaf :=
  ((schemeModulePullbackCompIso f p).app (degreeOne k n).obj).symm ≪≫
    (schemeModulePullback f).mapIso
      (AffineModuleTilde.pidInvertibleUnitIso (pullbackInvertibleSheaf p (degreeOne k n))) ≪≫
        schemeModulePullbackUnitIso f

/-- The original Euler difference vanishes for the original constant map. -/
theorem eulerDifference_comp_point :
    eulerCharacteristic f (pullbackInvertibleSheaf (f ≫ p) (degreeOne k n)).obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 0 := by
  rw [eulerCharacteristic_eq_of_iso f (pullbackDegreeOneUnitIso f p), sub_self]

/-- Any original projective map with this actual factorization has degree zero. -/
theorem eulerDifference_eq_zero_of_factor (g : X ⟶ projectiveSpace k n)
    (hg : g = f ≫ p) :
    eulerCharacteristic f (pullbackInvertibleSheaf g (degreeOne k n)).obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 0 := by
  rw [hg]
  exact eulerDifference_comp_point f p

end KltDP.Geometry.ProjectiveConstantDegree
