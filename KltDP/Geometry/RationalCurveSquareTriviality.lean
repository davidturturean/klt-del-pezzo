import KltDP.Geometry.ProjectiveLineSquareTriviality
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.SchemeModuleFunctorial

/-!
# A square-trivial line on the original rational curve is trivial

Transport the actual line and its tensor-square isomorphism along the given
original curve isomorphism. The projective-line trivialization is pulled
back through that same isomorphism, retaining the original module sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.RationalCurveSquareTriviality

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- No coordinate, Picard triviality, or chosen frame is a premise. -/
def unitIsoOfSquareIso (k : Type u) [Field k] {C : Scheme.{u}}
    (eC : C ≅ projectiveSpace k 1) (L : InvertibleSheaf C)
    (e : L.obj ⊗ L.obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf) :
    L.obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf := by
  let LP := pullbackInvertibleSheaf eC.inv L
  let eP : LP.obj ⊗ LP.obj ≅
      _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf :=
    (schemeModulePullbackTensorIso eC.inv L.obj L.obj).symm ≪≫
      (schemeModulePullback eC.inv).mapIso e ≪≫ schemeModulePullbackUnitIso eC.inv
  let tP := ProjectiveLineSquareTriviality.invertibleUnitIsoOfSquareIso k LP eP
  let back : (schemeModulePullback eC.hom).obj LP.obj ≅ L.obj :=
    (schemeModulePullbackCompIso eC.hom eC.inv).app L.obj ≪≫
      eqToIso (congrArg (fun f : C ⟶ C => (schemeModulePullback f).obj L.obj)
        eC.hom_inv_id) ≪≫ (schemeModulePullbackIdIso C).app L.obj
  exact back.symm ≪≫ (schemeModulePullback eC.hom).mapIso tP ≪≫
    schemeModulePullbackUnitIso eC.hom

end KltDP.Geometry.RationalCurveSquareTriviality
