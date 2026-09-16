/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

Bounded port from official Mathlib
5aedf732b6987e8c26ab3c9ebc855314f82b045f,
Topology/Sheaves/Over.lean:35-73. The underlying category equivalence
and the forward dense-subsite proof are retained; no newer elaborator
option or downstream sheaf-category construction is imported.
-/
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The actual opens of a subspace and its over site

An open of an open subspace is the same as an ambient open equipped with
an inclusion into that subspace. The equivalence respects the actual
Zariski covering sieves. This permits conversion of actual scheme-open
module charts into the existing over-site local-basis language.
-/

noncomputable section

open CategoryTheory Topology

universe u

namespace TopologicalSpace.Opens

variable {X : Type u} [TopologicalSpace X] (U : Opens X)

/-- The actual over category of an open is equivalent to the opens of
its actual topological subspace. -/
def overEquivalence : Over U ≌ Opens U where
  functor.obj V := ⟨_, IsOpen.preimage continuous_subtype_val V.left.isOpen⟩
  functor.map f := homOfLE (Set.preimage_mono (f := Subtype.val) (leOfHom f.left))
  inverse.obj W :=
    Over.mk (Y := ⟨_, (U.isOpenEmbedding'.isOpen_iff_image_isOpen).1 W.isOpen⟩)
      (homOfLE (fun _ _ => by aesop))
  inverse.map f := Over.homMk (homOfLE (Set.image_mono (leOfHom f)))
  unitIso := NatIso.ofComponents (fun V => Over.isoMk (eqToIso (by
    ext x
    dsimp
    simp only [SetLike.mem_coe, Set.mem_image, Set.mem_preimage,
      Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right, iff_self_and]
    apply leOfHom V.hom)))
  counitIso := NatIso.ofComponents (fun V => eqToIso (by aesop))

/-- The forward equivalence identifies the actual covering sieves. -/
instance overEquivalence_isDenseSubsite : U.overEquivalence.functor.IsDenseSubsite
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U) where
  functorPushforward_mem_iff {V S} := by
    change (∀ x ∈ U.overEquivalence.functor.obj V,
      ∃ (W : Opens U) (f : W ⟶ U.overEquivalence.functor.obj V),
        S.functorPushforward U.overEquivalence.functor f ∧ x ∈ W) ↔
      ∀ x ∈ V.left, ∃ (W : Opens X) (f : W ⟶ V.left),
        Sieve.overEquiv V S f ∧ x ∈ W
    simp only [Sieve.mem_functorPushforward_functor]
    constructor
    · intro H x hxV
      obtain ⟨W, f, hW, hxW⟩ := H ⟨x, V.hom.le hxV⟩ hxV
      exact ⟨_, ((U.overEquivalence.symm.toAdjunction.homEquiv _ _).symm f).left,
        ⟨_, _, 𝟙 _, hW, rfl⟩, _, hxW, rfl⟩
    · intro H x hxV
      obtain ⟨W, f, ⟨W', hW'V, hWW', hSW'V, rfl⟩, hxW⟩ := H x hxV
      exact ⟨_, U.overEquivalence.functor.map hW'V,
        S.downward_closed hSW'V (U.overEquivalence.unitInv.app W'), hWW'.le hxW⟩

end TopologicalSpace.Opens
