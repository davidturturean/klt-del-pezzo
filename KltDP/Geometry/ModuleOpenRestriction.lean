/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Actual module restriction along an open immersion

This is the bounded restriction construction from official Mathlib
`AlgebraicGeometry/Modules/Sheaf.lean`, revision
`5aedf732b6987e8c26ab3c9ebc855314f82b045f`, lines 339–354.
The complete upstream file has SHA-256
`9758ce92e5962b74e1bc9eaba5fd95fe1e34c0bf41e11f0c31312f411e2e1b38`.
The original Apache-2.0 attribution is retained above. This port uses
the project's unchanged Lean 4.19 / Mathlib c44 pin, makes naturality
and site continuity explicit, and uses the pinned sheaf projections.

For an actual open immersion f:Y→X, restriction sends an actual module
sheaf on X to a module sheaf on Y. Sections over V are the original
sections over f(V), with scalars transported by the actual section-ring
isomorphism. This constructs the actual functor; tensor preservation,
the induced Picard homomorphism, and Cartier compatibility are subsequent
proved adapters, not assumptions in this definition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeModuleRestriction

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- The image-open functor of the actual open immersion is continuous
for the actual small Zariski sites. -/
local instance imageFunctorContinuous : f.opensFunctor.IsContinuous
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
  f.isOpenEmbedding.functor_isContinuous

/-- The inverse actual section-ring isomorphisms form the scalar map
for restriction. The direction is O_Y→restriction(O_X). -/
def restrictionRingHom : Y.ringCatSheaf.val ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.val where
  app V := (forget₂ CommRingCat RingCat).map (f.appIso V.unop).inv
  naturality {U V} i :=
    ((forget₂ CommRingCat RingCat).map_comp _ _).symm.trans
      ((congrArg (fun g => (forget₂ CommRingCat RingCat).map g)
        (f.appIso_inv_naturality i)).trans
        ((forget₂ CommRingCat RingCat).map_comp _ _))

/-- The same actual scalar comparison as a morphism of ring sheaves. -/
def restrictionRingSheafHom : Y.ringCatSheaf ⟶
    (f.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
  ⟨restrictionRingHom f⟩

/-- Restrict actual structure-sheaf modules to the actual source scheme
of an open immersion, using the proved ring-sheaf comparison. -/
def restriction : X.Modules ⥤ Y.Modules :=
  _root_.SheafOfModules.pushforward (F := f.opensFunctor) (restrictionRingSheafHom f)

/-- The additive group of sections on the source open V is the original
additive group of sections over the actual image open f(V). -/
def restrictionSectionsIso (M : X.Modules) (V : Y.Opens) :
    ((restriction f).obj M).val.presheaf.obj (op V) ≅
      M.val.presheaf.obj (op (f ''ᵁ V)) := Iso.refl _

local instance (M : X.Modules) (U : X.Opens) :
    SMul Γ(X, U) (M.val.presheaf.obj (op U)) :=
  inferInstanceAs (SMul (X.ringCatSheaf.val.obj (op U)) (M.val.obj (op U)))

/-- Scalar multiplication in the restricted module is the original
scalar multiplication transported by the actual inverse section-ring map. -/
theorem restriction_smul (M : X.Modules) (V : Y.Opens) (r : Γ(Y, V))
    (m : ((restriction f).obj M).val.obj (op V)) :
    (restrictionSectionsIso f M V).hom (r • m) =
      (f.appIso V).inv r • (restrictionSectionsIso f M V).hom m := rfl

/-- Restriction maps of the new actual sheaf are the original maps
between the actual image opens. -/
theorem restriction_map (M : X.Modules) {V W : Y.Opens} (i : op V ⟶ op W)
    (m : ((restriction f).obj M).val.obj (op V)) :
    (restrictionSectionsIso f M W).hom (((restriction f).obj M).val.map i m) =
      M.val.map (f.opensFunctor.op.map i) ((restrictionSectionsIso f M V).hom m) := rfl

end KltDP.Geometry.SchemeModuleRestriction
