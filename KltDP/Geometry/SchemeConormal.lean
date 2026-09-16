/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

The small ring-sheaf morphism wrapper follows Mathlib
f15b4f161f6ff698ab91b4494faa75925856d0f5,
AlgebraicGeometry/Modules/Presheaf.lean:40-45, adapted to the pinned
sheaf morphism field name `val`. All categorical constructions below
reuse the existing pinned module-sheaf functors and kernels.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Actual kernel ideals and conormal module sheaves

A scheme morphism determines an actual morphism of ring sheaves. The
structure sheaf maps to the pushforward of the source structure sheaf as
a module sheaf. Its categorical kernel is the actual kernel ideal module;
evaluation preserves this kernel and identifies its sections with the
usual linear kernel of the section map.

Pulling this kernel back defines the actual conormal module sheaf of a
closed immersion. No local freeness, affine cotangent identification,
gluing equivalence, or normal-bundle comparison is assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual scheme structure map, with only its ring-sheaf structure retained. -/
def schemeRingSheafHom : Y.ringCatSheaf ⟶
    ((Opens.map f.base).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj X.ringCatSheaf where
  val := whiskerRight f.c (forget₂ CommRingCat RingCat)

/-- Pushforward of actual module sheaves along the original scheme morphism. -/
def schemeModulePushforward : X.Modules ⥤ Y.Modules :=
  _root_.SheafOfModules.pushforward (schemeRingSheafHom f)

/-- Pullback of actual module sheaves, using the pinned sheafified left
adjoint to the actual pushforward. -/
def schemeModulePullback : Y.Modules ⥤ X.Modules :=
  _root_.SheafOfModules.pullback (schemeRingSheafHom f)

/-- The actual structural map as a morphism of module sheaves. -/
def structureToPushforwardUnit : _root_.SheafOfModules.unit Y.ringCatSheaf ⟶
    (schemeModulePushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf) :=
  _root_.SheafOfModules.Hom.mk <|
    _root_.PresheafOfModules.homMk
      (whiskerRight (schemeRingSheafHom f).val (forget₂ RingCat AddCommGrp))
      (fun U a b => ((schemeRingSheafHom f).val.app U).hom.map_mul a b)

/-- On actual open sections this is precisely the original scheme map. -/
@[simp]
theorem structureToPushforwardUnit_app (U : Y.Opens) (s : Γ(Y, U)) :
    (structureToPushforwardUnit f).val.app (op U) s = f.app U s := rfl

/-- The actual kernel ideal module of the structural map. -/
def schemeKernelIdeal : Y.Modules := kernel (structureToPushforwardUnit f)

/-- The actual inclusion of the kernel ideal module into the structure sheaf. -/
def schemeKernelIdealι : schemeKernelIdeal f ⟶ _root_.SheafOfModules.unit Y.ringCatSheaf :=
  kernel.ι (structureToPushforwardUnit f)

/-- The kernel inclusion is killed by the actual structural section map. -/
@[simp]
theorem schemeKernelIdealι_comp :
    schemeKernelIdealι f ≫ structureToPushforwardUnit f = 0 :=
  kernel.condition (structureToPushforwardUnit f)

/-- Sections of the actual kernel sheaf are the ordinary linear kernel of
the actual structural section map. Only preservation of limits is used. -/
def schemeKernelIdealSectionsIso (U : Y.Opens) :
    (_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U)).obj (schemeKernelIdeal f) ≅
      ModuleCat.of Γ(Y, U) (LinearMap.ker ((structureToPushforwardUnit f).val.app (op U)).hom) :=
  PreservesKernel.iso (_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U))
      (structureToPushforwardUnit f) ≪≫
    ModuleCat.kernelIsoKer
      ((_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U)).map (structureToPushforwardUnit f))

/-- The kernel comparison preserves the actual inclusion on sections. -/
theorem schemeKernelIdealSectionsIso_hom_subtype (U : Y.Opens) :
    (schemeKernelIdealSectionsIso f U).hom ≫
        ModuleCat.ofHom (LinearMap.ker ((structureToPushforwardUnit f).val.app (op U)).hom).subtype =
      (_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U)).map (schemeKernelIdealι f) := by
  let G := _root_.SheafOfModules.evaluation Y.ringCatSheaf (op U)
  let m := G.map (structureToPushforwardUnit f)
  change ((PreservesKernel.iso G (structureToPushforwardUnit f)).hom ≫
      (ModuleCat.kernelIsoKer m).hom) ≫
        ModuleCat.ofHom (LinearMap.ker m.hom).subtype =
      G.map (kernel.ι (structureToPushforwardUnit f))
  rw [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
    PreservesKernel.iso_hom, kernelComparison_comp_ι]

/-- The pullback of the actual kernel ideal. For a closed immersion this
is its conormal module sheaf. The affine comparison with `J.Cotangent`
and local freeness remain separate theorems. -/
def schemeConormalSheaf : X.Modules :=
  (schemeModulePullback f).obj (schemeKernelIdeal f)

end KltDP.Geometry
