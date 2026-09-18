import KltDP.Geometry.SchemeModulePullbackTensorUnit

/-!
# The original pullback/sheafification comparison preserves the actual counit

Both original adjoint comparisons are normalized by their defining adjunctions.
Cancelling those adjunctions identifies the original counit square for every
actual module sheaf. This is the non-unit part of the structure-action square.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem adjoint_map {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) {M N : C} (t : M ⟶ N) :
    a.homEquiv M (F.obj N) (F.map t) = t ≫ a.unit.app N := by
  simpa only [Category.comp_id, Adjunction.homEquiv_id] using
    a.homEquiv_naturality_left t (𝟙 (F.obj N))

/-- The two chosen adjoint comparisons give the original pulled-back counit. -/
@[reassoc] theorem schemeModuleSheafificationCompPullback_forgetIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) :
    (_root_.SheafOfModules.sheafificationCompPullback (schemeRingSheafHom f)).hom.app
        M.val ≫ (schemeModulePullbackSheafificationIso f M).inv =
      (schemeModulePullback f).map
        (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M).hom := by
  apply ((schemeModulePullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.val)).homEquiv _ _).injective
  rw [schemeModuleSheafificationCompPullback_homEquiv, adjoint_map,
    Adjunction.homEquiv_naturality_right, schemeSheafificationForgetIso_homEquiv,
    Category.id_comp]
  simpa only [Iso.hom_inv_id, Adjunction.homEquiv_id] using
    (schemeModulePullbackSheafificationIso_homEquiv f M
      ((schemeModulePullback f).obj M)
      (schemeModulePullbackSheafificationIso f M).inv).symm

end KltDP.Geometry
