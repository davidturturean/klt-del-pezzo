/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer

The basis criterion is the bounded proof from official Mathlib
5aedf732b6987e8c26ab3c9ebc855314f82b045f,
Topology/Sheaves/SheafCondition/Sites.lean:258-265.
Only the newer sheaf morphism field `hom` is changed to the pinned `val`.
-/
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Detecting actual sheaf isomorphisms on an open basis

The generic criterion reuses the pinned cover-dense restriction theorem.
Its module-sheaf specialization forgets to actual sheaves of abelian
groups, whose forgetful functor reflects isomorphisms.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace TopCat.Sheaf

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}}
  {ι : Type*} {B : ι → Opens X}

/-- A morphism of actual sheaves is an isomorphism if it is an
isomorphism on every member of a topological basis. -/
theorem isIso_of_isIso_basis {F G : TopCat.Sheaf C X}
    (h : Opens.IsBasis (Set.range B)) {φ : F ⟶ G}
    (hi : ∀ i, IsIso (φ.val.app (op (B i)))) : IsIso φ := by
  have : (inducedFunctor B).IsCoverDense (Opens.grothendieckTopology X) :=
    Opens.coverDense_inducedFunctor h
  refine Functor.IsCoverDense.iso_of_restrict_iso (G := inducedFunctor B) _ ?_
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun _ => hi _

end TopCat.Sheaf

namespace KltDP.SheafOfModules

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : TopCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  {M N : _root_.SheafOfModules.{u} R} {ι : Type*} {B : ι → Opens X}

/-- A map of actual module sheaves is an isomorphism when its section
maps are bijective on an actual topological basis. -/
theorem isIso_of_bijective_on_basis (φ : M ⟶ N)
    (h : Opens.IsBasis (Set.range B))
    (hi : ∀ i, Function.Bijective (φ.val.app (op (B i)))) : IsIso φ := by
  haveI : IsIso ((_root_.SheafOfModules.toSheaf R).map φ) :=
    TopCat.Sheaf.isIso_of_isIso_basis h (fun i => by
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      exact hi i)
  exact isIso_of_reflects_iso φ (_root_.SheafOfModules.toSheaf R)

end KltDP.SheafOfModules
