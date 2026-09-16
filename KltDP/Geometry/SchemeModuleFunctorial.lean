/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang

The actual pushforward identity/composition comparisons follow Mathlib
5aedf732b6987e8c26ab3c9ebc855314f82b045f,
AlgebraicGeometry/Modules/Sheaf.lean:204-238. Their section maps are identities.
The pullback comparisons below use the pinned adjunction uniqueness API
directly, with the project's original schemeModulePullback definition.
-/
import KltDP.Geometry.SchemeConormal

/-!
# Identity and composition for actual scheme module pullback

These comparisons apply to arbitrary scheme morphisms. No tensor comparison,
local freeness, dominance, or condition on rational functions is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y Z : Scheme.{u}}

/-- The pinned adjunction for the original scheme module functors. -/
def schemeModulePullbackPushforwardAdjunction (f : X ⟶ Y) :
    schemeModulePullback f ⊣ schemeModulePushforward f :=
  _root_.SheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f)

/-- Identity pushforward leaves actual module sections and maps unchanged. -/
def schemeModulePushforwardIdIso (X : Scheme.{u}) :
    schemeModulePushforward (𝟙 X) ≅ 𝟭 X.Modules :=
  Iso.refl _

set_option maxHeartbeats 800000 in
/-- Iterated pushforward has the actual composite scheme structure map. -/
def schemeModulePushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    schemeModulePushforward f ⋙ schemeModulePushforward g ≅
      schemeModulePushforward (f ≫ g) :=
  Iso.refl _

/-- The identity comparison acts by the identity on every section. -/
@[simp]
theorem schemeModulePushforwardIdIso_hom_app (X : Scheme.{u})
    (M : X.Modules) (U : X.Opens)
    (m : ((schemeModulePushforward (𝟙 X)).obj M).val.obj (op U)) :
    ((schemeModulePushforwardIdIso X).hom.app M).val.app (op U) m = m := rfl

/-- The composition comparison acts by the identity on every section. -/
@[simp]
theorem schemeModulePushforwardCompIso_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) (U : Z.Opens)
    (m : ((schemeModulePushforward f ⋙ schemeModulePushforward g).obj M).val.obj
      (op U)) :
    ((schemeModulePushforwardCompIso f g).hom.app M).val.app (op U) m = m := rfl

/-- Pullback along the identity identifies with the identity functor by
uniqueness of the actual left adjoint. -/
def schemeModulePullbackIdIso (X : Scheme.{u}) :
    schemeModulePullback (𝟙 X) ≅ 𝟭 X.Modules :=
  Adjunction.leftAdjointUniq
    ((schemeModulePullbackPushforwardAdjunction (𝟙 X)).ofNatIsoRight
      (schemeModulePushforwardIdIso X))
    Adjunction.id

/-- Iterated actual pullback identifies with pullback of the composite. -/
def schemeModulePullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    schemeModulePullback g ⋙ schemeModulePullback f ≅
      schemeModulePullback (f ≫ g) :=
  Adjunction.leftAdjointUniq
    (((schemeModulePullbackPushforwardAdjunction g).comp
      (schemeModulePullbackPushforwardAdjunction f)).ofNatIsoRight
        (schemeModulePushforwardCompIso f g))
    (schemeModulePullbackPushforwardAdjunction (f ≫ g))

end KltDP.Geometry
