import KltDP.Compatibility.TopologicalSheafIso
import KltDP.Compatibility.SheafLocalQuotient
import KltDP.Compatibility.HomComplexGlobalSections
import KltDP.Geometry.SchemeModulePushforwardScalars

/-!
# Original abelian-sheaf pushforward and global sections

Forgetting the scalars of the original scheme-module pushforward gives
the original topological sheaf pushforward. The latter is additive and,
along a scheme isomorphism, is an equivalence.

The canonical global-sections functor is a chosen right adjoint. Its
comparison under pushforward uses the pinned comparisons with top-open
sections on both schemes. Only the intermediate top-open comparison is
the identity. The original coefficient multiplication maps are retained
for the subsequent comparison of derived cohomology.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

open KltDP.SheafCochainComparison ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}}

/-- Pushforward of original abelian sheaves on the two Zariski spaces. -/
abbrev schemeAbelianSheafPushforward (f : X ⟶ Y) :
    (X : TopCat.{u}).Sheaf AddCommGrp.{u} ⥤ (Y : TopCat.{u}).Sheaf AddCommGrp.{u} :=
  TopCat.Sheaf.pushforward AddCommGrp.{u} f.base

/-- Original coefficient addition is unchanged by inverse-image precomposition. -/
instance schemeAbelianSheafPushforward_additive (f : X ⟶ Y) :
    (schemeAbelianSheafPushforward f).Additive where
  map_add := by
    intro F G a b
    rfl

/-- Forgetting original module scalars commutes with the original pushforward. -/
def schemeModulePushforwardToSheafIso (f : X ⟶ Y) :
    schemeModulePushforward f ⋙ _root_.SheafOfModules.toSheaf Y.ringCatSheaf ≅
      _root_.SheafOfModules.toSheaf X.ringCatSheaf ⋙ schemeAbelianSheafPushforward f :=
  Iso.refl _

/-- A scheme isomorphism gives an equivalence with the literal original
abelian-sheaf pushforward as its forward functor. -/
def schemeAbelianSheafIsoEquivalence (e : X ≅ Y) :
    (X : TopCat.{u}).Sheaf AddCommGrp.{u} ≌ (Y : TopCat.{u}).Sheaf AddCommGrp.{u} :=
  KltDP.TopologicalSheafIso.pushforwardEquivalence AddCommGrp.{u}
    (Scheme.forgetToTop.mapIso e)

theorem schemeAbelianSheafIsoEquivalence_functor (e : X ≅ Y) :
    (schemeAbelianSheafIsoEquivalence e).functor = schemeAbelianSheafPushforward e.hom := rfl

/-- The actual top-open section functors agree under pushforward. -/
def schemeAbelianPushforwardTopSectionsIso (f : X ⟶ Y) :
    schemeAbelianSheafPushforward f ⋙
        (sheafSections (Opens.grothendieckTopology Y) AddCommGrp.{u}).obj
          (op (⊤ : Y.Opens)) ≅
      (sheafSections (Opens.grothendieckTopology X) AddCommGrp.{u}).obj
        (op (⊤ : X.Opens)) := Iso.refl _

/-- Compare the original chosen global-sections functors using their
original adjunction comparisons with sections at the top open. -/
def schemeAbelianPushforwardGlobalSectionsIso (f : X ⟶ Y) :
    schemeAbelianSheafPushforward f ⋙ globalSectionsFunctor (Y : TopCat.{u}) ≅
      globalSectionsFunctor (X : TopCat.{u}) :=
  isoWhiskerLeft (schemeAbelianSheafPushforward f)
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) AddCommGrp.{u}
        (Limits.isTerminalTop : Limits.IsTerminal (⊤ : Y.Opens))) ≪≫
    schemeAbelianPushforwardTopSectionsIso f ≪≫
    (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) AddCommGrp.{u}
      (Limits.isTerminalTop : Limits.IsTerminal (⊤ : X.Opens))).symm

/-- The comparison commutes with both original top-section comparisons. -/
theorem schemeAbelianPushforwardGlobalSectionsIso_hom_sections
    (f : X ⟶ Y) (F : (X : TopCat.{u}).Sheaf AddCommGrp.{u}) :
    (schemeAbelianPushforwardGlobalSectionsIso f).hom.app F ≫
        (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) AddCommGrp.{u}
          (Limits.isTerminalTop : Limits.IsTerminal (⊤ : X.Opens))).hom.app F =
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology Y) AddCommGrp.{u}
        (Limits.isTerminalTop : Limits.IsTerminal (⊤ : Y.Opens))).hom.app
          ((schemeAbelianSheafPushforward f).obj F) := by
  simp only [schemeAbelianPushforwardGlobalSectionsIso,
    schemeAbelianPushforwardTopSectionsIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, whiskerLeft_app, NatTrans.comp_app, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

/-- After forgetting scalars, the exact original multiplication maps
still agree under pushforward on every original open. -/
theorem schemeAbelianPushforward_globalSmulHom
    (f : X ⟶ Y) (M : X.Modules) (r : Γ(Y, ⊤)) :
    (schemeAbelianSheafPushforward f).map
        ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
          (globalSmulHom M (f.appTop r))) =
      (_root_.SheafOfModules.toSheaf Y.ringCatSheaf).map
        (globalSmulHom ((schemeModulePushforward f).obj M) r) :=
  congrArg ((_root_.SheafOfModules.toSheaf Y.ringCatSheaf).map)
    (globalSmulHom_pushforward f M r).symm

end KltDP.Geometry
