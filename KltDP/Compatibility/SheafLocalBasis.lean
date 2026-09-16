/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Brian Nugent

The free generating sections and local-free-data definitions are adapted
from Mathlib 5aedf732b6987e8c26ab3c9ebc855314f82b045f,
Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean. The restriction functor
exposes the functor already used in the pinned definition of `over`.
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# Local free-basis helpers for the pinned sheaf category

These definitions concern actual module sheaves, their restriction to the
over-site, and their coproduct free sheaves. They expose the small part of
the later local-freeness API used by the rank-one sheaf construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u₁

namespace SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- The actual restriction functor whose object map is the pinned `over`. -/
def overFunctor (U : C) : SheafOfModules.{u} R ⥤ SheafOfModules.{u} (R.over U) :=
  pushforward (F := Over.forget U) (J := J.over U) (K := J) (𝟙 (R.over U))

@[simp]
theorem overFunctor_obj (U : C) (M : SheafOfModules.{u} R) :
    (overFunctor R U).obj M = M.over U := rfl

variable {R}

section Unit

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- Restriction of the actual rank-one unit sheaf is the unit sheaf over
the restricted ring sheaf. Both module actions and restriction maps agree. -/
def unitOverIso (U : C) : (unit R).over U ≅ unit (R.over U) := Iso.refl _

end Unit

section GeneratingSections

variable [HasWeakSheafify J AddCommGrp.{u}]
  [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- The tautological basis sections of the actual coproduct free sheaf. -/
def free.generatingSections (I : Type u) : (free (R := R) I).GeneratingSections where
  I := I
  s i := freeSection i
  epi := by
    change Epi ((free I).freeHomEquiv.symm ((free I).freeHomEquiv (𝟙 (free I))))
    rw [Equiv.symm_apply_apply]
    infer_instance

@[simp]
theorem free.generatingSections_π (I : Type u) :
    (free.generatingSections (R := R) I).π = 𝟙 (free I) :=
  Equiv.symm_apply_apply (free I).freeHomEquiv _

/-- Pushing generating sections forward composes their actual presentation map. -/
theorem GeneratingSections.ofEpi_π {M N : SheafOfModules.{u} R}
    (σ : M.GeneratingSections) (p : M ⟶ N) [Epi p] :
    (σ.ofEpi p).π = σ.π ≫ p :=
  (freeHomEquiv_symm_comp σ.s p).symm

/-- A free sheaf with a singleton basis is isomorphic to the actual unit sheaf. -/
def freeUniqueIsoUnit (I : Type u) [Nonempty I] [Subsingleton I] :
    free (R := R) I ≅ unit R := by
  letI : Unique I := uniqueOfSubsingleton (Classical.choice (inferInstance : Nonempty I))
  exact coproductUniqueIso (fun _ : I ↦ unit R)

end GeneratingSections

section LocallyFree

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- A local generating family is a local basis exactly when every
presentation morphism is an isomorphism. -/
class LocalGeneratorsData.IsLocallyFreeData {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) : Prop where
  isIso : ∀ i, IsIso (q.generators i).π

/-- Local freeness of the actual module sheaf. The local ranks may vary. -/
class IsLocallyFree (M : SheafOfModules.{u} R) : Prop where
  exists_isLocallyFreeData : ∃ q : M.LocalGeneratorsData, q.IsLocallyFreeData

end LocallyFree

end SheafOfModules
