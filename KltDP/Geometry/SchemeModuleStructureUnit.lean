import KltDP.Geometry.SheafPicard
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# The original structure module and the scheme tensor unit

Name the accepted sheafification-counit comparison on an arbitrary scheme
before specializing it to an actual affine chart.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.SchemeModuleStructureUnit

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The accepted original unit comparison, with all site instances supplied on the scheme. -/
def iso (X : Scheme.{u}) : _root_.SheafOfModules.unit X.ringCatSheaf ≅ 𝟙_ X.Modules :=
  (_root_.PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).symm

end KltDP.Geometry.SchemeModuleStructureUnit
