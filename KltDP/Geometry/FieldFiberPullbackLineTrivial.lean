import KltDP.Geometry.AffinePIDInvertibleTrivial
import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Geometry.SchemeInvertibleSheafPullback
import Mathlib.AlgebraicGeometry.Limits

/-! Every line pulled back from the base becomes trivial on the ORIGINAL
field-valued fiber. The actual field may be the base function field or any
extension; neither a closed point nor a rational point is required. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.FieldFiberPullbackLineTrivial

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (π : X ⟶ Y)
  {K : Type u} [Field K] (q : Spec (CommRingCat.of K) ⟶ Y)
  (L : InvertibleSheaf Y)

/-- An actual unit frame on the complete original scheme fiber, obtained
from the field-line frame and the literal pullback square. -/
def unitIso :
    (pullbackInvertibleSheaf (pullback.fst π q) (pullbackInvertibleSheaf π L)).obj ≅
      _root_.SheafOfModules.unit (pullback π q).ringCatSheaf :=
  (schemeModulePullbackCompIso (pullback.fst π q) π).app L.obj ≪≫
    eqToIso (congrArg (fun f : pullback π q ⟶ Y =>
      (schemeModulePullback f).obj L.obj) (pullback.condition (f := π) (g := q))) ≪≫
    ((schemeModulePullbackCompIso (pullback.snd π q) q).app L.obj).symm ≪≫
    (schemeModulePullback (pullback.snd π q)).mapIso
      (AffineModuleTilde.pidInvertibleUnitIso (pullbackInvertibleSheaf q L)) ≪≫
    schemeModulePullbackUnitIso (pullback.snd π q)

/-- Transport the actual fiber frame to an original isomorphic source line. -/
def sourceLineUnitIso (M : InvertibleSheaf X)
    (e : (pullbackInvertibleSheaf π L).obj ≅ M.obj) :
    (pullbackInvertibleSheaf (pullback.fst π q) M).obj ≅
      _root_.SheafOfModules.unit (pullback π q).ringCatSheaf :=
  (schemeModulePullback (pullback.fst π q)).mapIso e.symm ≪≫ unitIso π q L

end KltDP.Geometry.FieldFiberPullbackLineTrivial

#check @KltDP.Geometry.FieldFiberPullbackLineTrivial.unitIso
#print axioms KltDP.Geometry.FieldFiberPullbackLineTrivial.sourceLineUnitIso
