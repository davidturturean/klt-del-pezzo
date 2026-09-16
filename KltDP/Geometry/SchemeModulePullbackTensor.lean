import KltDP.Compatibility.PresheafPullbackTensor
import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Geometry.SheafPicard

/-!
# Actual scheme-module pullback preserves tensor products

The proved tensor comparison on actual module presheaves descends through
the pinned pullback/sheafification isomorphism. The existing monoidal
sheafification and pullback construction supply the remaining comparisons.
The unit comparison uses the separately proved pullback of the structure
sheaf. No tensor compatibility is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The actual presheaf comparison, already proved invertible on every pair. -/
def schemeModulePresheafPullbackTensorIso
    (P Q : PresheafOfModules.{u} X.ringCatSheaf.val) :
    letI : MonoidalCategory (PresheafOfModules.{u} X.ringCatSheaf.val) :=
      PresheafOfModules.monoidalCategory (R := X.sheaf.val)
    letI : MonoidalCategory (PresheafOfModules.{u} Y.ringCatSheaf.val) :=
      PresheafOfModules.monoidalCategory (R := Y.sheaf.val)
    (PresheafOfModules.pullback (schemeRingSheafHom f).val).obj (P ⊗ Q) ≅
      (PresheafOfModules.pullback (schemeRingSheafHom f).val).obj P ⊗
        (PresheafOfModules.pullback (schemeRingSheafHom f).val).obj Q := by
  letI : MonoidalCategory (PresheafOfModules.{u} X.ringCatSheaf.val) :=
      PresheafOfModules.monoidalCategory (R := X.sheaf.val)
  letI : MonoidalCategory (PresheafOfModules.{u} Y.ringCatSheaf.val) :=
      PresheafOfModules.monoidalCategory (R := Y.sheaf.val)
  letI := PresheafOfModules.pullbackOplaxMonoidal
    (PresheafOfModules.schemeRingPresheafHom f)
  letI := PresheafOfModules.isIso_pullback_δ f P Q
  exact asIso (Functor.OplaxMonoidal.δ
    (PresheafOfModules.pullback (PresheafOfModules.schemeRingPresheafHom f)) P Q)

/-- The original pullback is the sheafification of the actual presheaf
pullback of the underlying module presheaf. -/
def schemeModulePullbackSheafificationIso (M : X.Modules) :
    (schemeModulePullback f).obj M ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj M.val) :=
  (_root_.SheafOfModules.pullbackIso (schemeRingSheafHom f)).app M

/-- Pullback of the actual tensor is the tensor of the actual pullbacks,
for every pair of module sheaves and every scheme morphism. -/
def schemeModulePullbackTensorIso (M N : X.Modules) :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y
    (schemeModulePullback f).obj (M ⊗ N) ≅
      (schemeModulePullback f).obj M ⊗ (schemeModulePullback f).obj N := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  letI : MonoidalCategory (PresheafOfModules.{u} X.ringCatSheaf.val) :=
      PresheafOfModules.monoidalCategory (R := X.sheaf.val)
  letI : MonoidalCategory (PresheafOfModules.{u} Y.ringCatSheaf.val) :=
      PresheafOfModules.monoidalCategory (R := Y.sheaf.val)
  letI : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).Monoidal :=
    PresheafOfModules.sheafificationMonoidal Y.sheaf.val Y.ringCatSheaf.cond
  exact (schemeModulePullback f).mapIso
      (PresheafOfModules.sheafTensorIsoSheafification
        X.sheaf.val X.ringCatSheaf.cond M N) ≪≫
    (_root_.SheafOfModules.sheafificationCompPullback
      (schemeRingSheafHom f)).app (M.val ⊗ N.val) ≪≫
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).mapIso
      (schemeModulePresheafPullbackTensorIso f M.val N.val) ≪≫
    (Functor.Monoidal.μIso
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val))
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj M.val)
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj N.val)).symm ≪≫
    tensorIso (schemeModulePullbackSheafificationIso f M).symm
      (schemeModulePullbackSheafificationIso f N).symm

/-- The chosen monoidal units are compared through the actual structure
sheaves and their proved pullback isomorphism. -/
def schemeModulePullbackTensorUnitIso :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y
    (schemeModulePullback f).obj (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  exact (schemeModulePullback f).mapIso
      (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond) ≪≫
    schemeModulePullbackUnitIso f ≪≫
    (PresheafOfModules.sheafTensorUnitIso Y.sheaf.val Y.ringCatSheaf.cond).symm

end KltDP.Geometry
