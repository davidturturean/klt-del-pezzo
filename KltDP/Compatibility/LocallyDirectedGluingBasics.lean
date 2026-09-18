/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

Bounded adaptation of Mathlib 80cbd0498ab39e21d24d6730b3f932cec672a702:
CategoryTheory/LocallyDirected.lean:46-51, AlgebraicGeometry/Gluing.lean:483-491,
Restrict.lean:336-346, and PullbackCarrier.lean:409-417.
The pin's original scheme maps, open covers and pullbacks are retained.
Only small indexing types in the original scheme universe are needed.
-/
import KltDP.Compatibility.DirectedOpenCover

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u v w

namespace CategoryTheory

/-- Every equality in a common target of the diagram is witnessed in a
common smaller object of the original diagram. -/
class Functor.IsLocallyDirected {J : Type w} [Category.{v} J]
    (F : J ⥤ Type u) : Prop where
  cond : ∀ {i j k} (fi : i ⟶ k) (fj : j ⟶ k) (xi : F.obj i) (xj : F.obj j),
    F.map fi xi = F.map fj xj →
      ∃ (l : J) (fli : l ⟶ i) (flj : l ⟶ j) (x : F.obj l),
        F.map fli x = xi ∧ F.map flj x = xj

theorem Functor.exists_map_eq_of_isLocallyDirected {J : Type w} [Category.{v} J]
    (F : J ⥤ Type u) [F.IsLocallyDirected] {i j k : J}
    (fi : i ⟶ k) (fj : j ⟶ k) (xi : F.obj i) (xj : F.obj j)
    (h : F.map fi xi = F.map fj xj) :
    ∃ (l : J) (fli : l ⟶ i) (flj : l ⟶ j) (x : F.obj l),
      F.map fli x = xi ∧ F.map flj x = xj :=
  Functor.IsLocallyDirected.cond fi fj xi xj h

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The original underlying-carrier functor, expressed through the pinned topology functor. -/
abbrev forget : Scheme.{u} ⥤ Type u :=
  Scheme.forgetToTop ⋙ CategoryTheory.forget TopCat

/-- Equality on an actual open neighbourhood of every point determines a scheme morphism. -/
theorem hom_ext_of_forall {X Y : Scheme.{u}} (f g : X ⟶ Y)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g) : f = g := by
  choose U hxU hU using H
  let 𝒰 : OpenCover.{u} X := Cover.mkOfCovers X
    (fun x => (U x).toScheme) (fun x => (U x).ι)
    (fun x => ⟨x, ⟨x, hxU x⟩, rfl⟩)
  exact 𝒰.hom_ext f g hU

/-- The original opens cover their union by the original open inclusions. -/
def Opens.iSupOpenCover {J : Type u} {X : Scheme.{u}} (U : J → X.Opens) :
    OpenCover.{u} (⨆ j, U j).toScheme :=
  Cover.mkOfCovers J (fun j => (U j).toScheme)
    (fun j => X.homOfLE (le_iSup U j))
    (fun x => by
      obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp x.2
      refine ⟨j, ⟨x.1, hxj⟩, ?_⟩
      apply Subtype.ext
      exact Scheme.homOfLE_apply (le_iSup U j) ⟨x.1, hxj⟩)

/-- A pair of original scheme points with the same image lifts through an actual
cartesian square. The original square, rather than a replacement pullback, is the result. -/
theorem exists_preimage_of_isPullback {P X Y Z : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (x : X) (y : Y) (hxy : f.base x = g.base y) :
    ∃ p : P, fst.base p = x ∧ snd.base p = y := by
  obtain ⟨z, hzl, hzr⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨h.isoPullback.inv.base z, ?_, ?_⟩
  · rw [← Scheme.comp_base_apply, h.isoPullback_inv_fst]
    exact hzl
  · rw [← Scheme.comp_base_apply, h.isoPullback_inv_snd]
    exact hzr

end AlgebraicGeometry.Scheme
