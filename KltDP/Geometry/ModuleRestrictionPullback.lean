/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang

Adapted from Mathlib 5aedf732b6987e8c26ab3c9ebc855314f82b045f,
AlgebraicGeometry/Modules/Sheaf.lean:415-423. The project uses its existing
actual restriction and pullback functors and the pinned sheaf projections.
-/
import KltDP.Geometry.ModuleOpenRestriction
import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Compatibility.ModulePushforwardAdjunction

/-!
# Open restriction is the actual scheme-module pullback

The inverse section-ring maps of an open immersion make its image-open
restriction left adjoint to the original scheme module pushforward. The
comparison with pullback follows from uniqueness of that left adjoint.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

local instance : f.opensFunctor.IsContinuous
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
  f.isOpenEmbedding.functor_isContinuous

/-- The actual open restriction functor is left adjoint to the original
scheme module pushforward. -/
def restrictionAdjunction : restriction f ⊣ schemeModulePushforward f := by
  refine KltDP.SheafModuleAdjunction.pushforwardPushforwardAdj
    (F := f.opensFunctor) (G := Opens.map f.base)
    (by exact f.isOpenEmbedding.isOpenMap.adjunction)
    (restrictionRingSheafHom f) (schemeRingSheafHom f) ?_ ?_
  · ext U x
    exact ConcreteCategory.congr_hom (f.app_appIso_inv U.unop).symm x
  · ext U x
    have h : (f.appIso U.unop).inv ≫ f.app (f ''ᵁ U.unop) ≫
        Y.presheaf.map (eqToHom (f.preimage_image_eq U.unop).symm).op = 𝟙 _ := by
      rw [Scheme.Hom.appIso_inv_app_assoc, ← Functor.map_comp,
        ← Y.presheaf.map_id]
      rfl
    exact ConcreteCategory.congr_hom h x

/-- Image-open restriction and the existing actual pullback are naturally
isomorphic for every actual open immersion. -/
def restrictionIsoPullback : restriction f ≅ schemeModulePullback f :=
  Adjunction.leftAdjointUniq (restrictionAdjunction f)
    (schemeModulePullbackPushforwardAdjunction f)

end KltDP.Geometry.SchemeModuleRestriction
