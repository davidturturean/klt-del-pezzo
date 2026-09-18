import KltDP.Geometry.SchemeModuleFunctorial
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Composite adjunction normalization with its original pushforward comparison

The output retains the original pushforward composition isomorphism.
Consequently both sides are morphisms into the composite pushforward,
without identifying that sheaf with an iterated pushforward by reduction.
The proof is the pinned left-adjoint uniqueness calculation underlying
the existing original pullback composition isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

private theorem homEquiv_leftAdjointUniq_comp_explicit
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    (M : C) (N : D) (h : F'.obj M ⟶ N) :
    a.homEquiv M N ((Adjunction.leftAdjointUniq a b).hom.app M ≫ h) =
      b.homEquiv M N h := by
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

private theorem homEquiv_ofNatIsoRight_apply_explicit
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (e : G ≅ H)
    (M : C) (N : D) (h : F.obj M ⟶ N) :
    (a.ofNatIsoRight e).homEquiv M N h =
      a.homEquiv M N h ≫ e.hom.app N := by
  rw [Adjunction.ofNatIsoRight, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

variable {X Y Z : Scheme.{u}}

/-- The original composite adjunction identity, with the original
pushforward comparison retained as an explicit final morphism. -/
theorem schemeModulePullbackCompIso_homEquiv_pushforward
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (N : X.Modules)
    (a : (schemeModulePullback (f ≫ g)).obj M ⟶ N) :
    (schemeModulePullbackPushforwardAdjunction g).homEquiv M
        ((schemeModulePushforward f).obj N)
      ((schemeModulePullbackPushforwardAdjunction f).homEquiv
        ((schemeModulePullback g).obj M) N
        ((schemeModulePullbackCompIso f g).hom.app M ≫ a)) ≫
          (schemeModulePushforwardCompIso f g).hom.app N =
      (schemeModulePullbackPushforwardAdjunction (f ≫ g)).homEquiv M N a := by
  have h := homEquiv_leftAdjointUniq_comp_explicit
    (((schemeModulePullbackPushforwardAdjunction g).comp
      (schemeModulePullbackPushforwardAdjunction f)).ofNatIsoRight
        (schemeModulePushforwardCompIso f g))
    (schemeModulePullbackPushforwardAdjunction (f ≫ g)) M N a
  change (((schemeModulePullbackPushforwardAdjunction g).comp
      (schemeModulePullbackPushforwardAdjunction f)).ofNatIsoRight
        (schemeModulePushforwardCompIso f g)).homEquiv M N
      ((schemeModulePullbackCompIso f g).hom.app M ≫ a) = _ at h
  rw [homEquiv_ofNatIsoRight_apply_explicit, Adjunction.comp_homEquiv] at h
  simpa only [Equiv.trans_apply] using h

end KltDP.Geometry

#check @KltDP.Geometry.schemeModulePullbackCompIso_homEquiv_pushforward
#print axioms KltDP.Geometry.schemeModulePullbackCompIso_homEquiv_pushforward
