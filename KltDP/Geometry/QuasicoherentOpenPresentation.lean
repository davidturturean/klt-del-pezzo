/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang, Brian Nugent

The affine refinement follows official Mathlib Tilde.lean:600–619 at
79d0395a1825a6264ad5d269e35e60537518955e, using the project's original
open/Over equivalence and actual pinned presentations.
-/
import KltDP.Compatibility.SheafPresentationMap
import KltDP.Compatibility.SheafIteratedOverKernel
import KltDP.Geometry.ModuleOpenOverEquivalence
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Actual affine open presentations of quasicoherent module sheaves

Original Over-site presentations are transported through the already
proved open-subscheme equivalence. Restricting such a presentation to a
smaller open uses the original nested Over functor and its actual unit
and object isomorphisms. The scheme's affine basis then produces an
actual affine covering with presentations. No affine reconstruction or
global generation hypothesis is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (U : X.Opens)

/-- The inverse equivalence's unit comparison derives from the original
open immersion's unit map and the proved equivalence unit. -/
def overToOpenUnitIso : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅
    (openToOverEquivalence U).inverse.obj
      (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  (openToOverEquivalence U).unitIso.app _ ≪≫
    (openToOverEquivalence U).inverse.mapIso (openToOverUnitIso U).symm

/-- The inverse equivalence recovers the original image-open restriction. -/
def overToOpenRestrictionIso (M : X.Modules) :
    (openToOverEquivalence U).inverse.obj (M.over U) ≅
      (SchemeModuleRestriction.restriction U.ι).obj M :=
  (openToOverEquivalence U).inverse.mapIso (openToOverRestrictionIso U M).symm ≪≫
    ((openToOverEquivalence U).unitIso.app _).symm

/-- Transport an original Over presentation to the actual open subscheme. -/
def openPresentationOfOver (M : X.Modules) (P : (M.over U).Presentation) :
    ((SchemeModuleRestriction.restriction U.ι).obj M).Presentation :=
  _root_.SheafOfModules.Presentation.ofIsIso (overToOpenRestrictionIso U M).hom
    (P.map (openToOverEquivalence U).inverse (overToOpenUnitIso U))

variable {U}

/-- Refine the original presentation along an actual inclusion of opens. -/
def overPresentationOfLE (M : X.Modules) {V : X.Opens} (h : V ≤ U)
    (P : (M.over U).Presentation) : (M.over V).Presentation :=
  _root_.SheafOfModules.Presentation.ofIsIso
    (_root_.SheafOfModules.iteratedOverObjIso X.ringCatSheaf M
      (Over.mk (homOfLE h))).hom
    (P.map (_root_.SheafOfModules.overToSingleFunctor X.ringCatSheaf
      (Over.mk (homOfLE h)))
      (_root_.SheafOfModules.overToSingleUnitIso X.ringCatSheaf
        (Over.mk (homOfLE h))))

/-- Every original quasicoherent module has actual scheme-open presentations
on an affine covering of the original scheme. -/
theorem exists_affine_open_presentations (M : X.Modules) [M.IsQuasicoherent] :
    ∃ (I : Type u) (V : I → X.Opens),
      (∀ i, IsAffineOpen (V i)) ∧ (∀ x : X, ∃ i, x ∈ V i) ∧
      Nonempty (∀ i, ((SchemeModuleRestriction.restriction (V i).ι).obj M).Presentation) := by
  obtain ⟨q⟩ := _root_.SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)
  let I := Σ i : q.I, {V : X.affineOpens // V.1 ≤ q.X i}
  let V : I → X.Opens := fun i => i.2.1.1
  refine ⟨I, V, fun i => i.2.1.2, ?_, ⟨fun i => ?_⟩⟩
  · intro x
    obtain ⟨W, f, ⟨i, ⟨g⟩⟩, hxW⟩ := q.coversTop (⊤ : X.Opens) x trivial
    have hxi : x ∈ q.X i := g.le hxW
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAi⟩ :=
      (isBasis_affine_open X).exists_subset_of_mem_open hxi (q.X i).isOpen
    exact ⟨⟨i, ⟨⟨A, hA⟩, hAi⟩⟩, hxA⟩
  · exact openPresentationOfOver (V i) M
      (overPresentationOfLE M i.2.2 (q.presentation i.1))

end KltDP.Geometry
