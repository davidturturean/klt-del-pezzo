/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from Vilin97/TauCeti a74dfee78f800df63f085a19006f7d502eee365e:
TauCeti/Algebra/Category/ModuleCat/Sheaf/Invertible/Basic.lean and
TauCeti/Algebra/Category/ModuleCat/Sheaf/Invertible/LocalTriviality.lean.
The namespace and missing helper APIs are adapted to the pinned library.
-/
import KltDP.Compatibility.SheafLocalBasis

/-!
# Actual rank-one local bases and local trivializations

The predicate is the source's literal singleton-basis refinement of local
freeness: on a covering, actual free presentation maps are isomorphisms and
their indexing types are nonempty subsingletons. It is equivalent to an
atlas of actual isomorphisms from the free sheaf on `PUnit`.

All objects are sheaves over the given ring sheaf and all restrictions use
the existing over-site functor. No tensor or Picard structure is asserted.
-/

noncomputable section

open CategoryTheory

universe u v u₁

namespace KltDP.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  {M N : _root_.SheafOfModules.{u} R}

/-- A local basis has rank one when each indexing type has exactly one
element. The presentation maps themselves must be isomorphisms. -/
structure LocalGeneratorsData.IsInvertible
    (q : _root_.SheafOfModules.LocalGeneratorsData M) : Prop where
  isLocallyFreeData : q.IsLocallyFreeData
  basisNonempty (i : q.I) : Nonempty (q.generators i).I
  basisSubsingleton (i : q.I) : Subsingleton (q.generators i).I

/-- Invertibility means local freeness of rank one for the actual sheaf. -/
class IsInvertible (M : _root_.SheafOfModules.{u} R) : Prop where
  exists_isInvertible :
    ∃ q : _root_.SheafOfModules.LocalGeneratorsData M, LocalGeneratorsData.IsInvertible q

instance IsInvertible.isLocallyFree (M : _root_.SheafOfModules.{u} R)
    [h : IsInvertible M] : M.IsLocallyFree := by
  obtain ⟨q, hq⟩ := h.exists_isInvertible
  exact ⟨q, hq.isLocallyFreeData⟩

/-- The singleton local bases also give the pinned finite-type property. -/
instance IsInvertible.isFiniteType (M : _root_.SheafOfModules.{u} R)
    [h : IsInvertible M] : M.IsFiniteType := by
  obtain ⟨q, hq⟩ := h.exists_isInvertible
  refine ⟨q, fun i ↦ ?_⟩
  letI := hq.basisSubsingleton i
  infer_instance

/-- Transport the same cover and local generators along the actual
restricted sheaf isomorphisms. -/
def LocalGeneratorsData.ofIso (q : _root_.SheafOfModules.LocalGeneratorsData M)
    (e : M ≅ N) : _root_.SheafOfModules.LocalGeneratorsData N where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi
    ((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom

theorem LocalGeneratorsData.IsInvertible.ofIso
    {q : _root_.SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.IsInvertible q) (e : M ≅ N) :
    LocalGeneratorsData.IsInvertible (LocalGeneratorsData.ofIso q e) where
  isLocallyFreeData := {
    isIso := by
      intro i
      change IsIso ((q.generators i).ofEpi
        ((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom).π
      rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
      letI := hq.isLocallyFreeData.isIso i
      infer_instance }
  basisNonempty i := hq.basisNonempty i
  basisSubsingleton i := hq.basisSubsingleton i

theorem IsInvertible.of_iso (e : M ≅ N) [h : IsInvertible M] : IsInvertible N := by
  obtain ⟨q, hq⟩ := h.exists_isInvertible
  exact ⟨LocalGeneratorsData.ofIso q e, hq.ofIso e⟩

theorem isInvertible_iff_of_iso (e : M ≅ N) : IsInvertible M ↔ IsInvertible N := by
  constructor
  · intro h
    letI := h
    exact IsInvertible.of_iso e
  · intro h
    letI := h
    exact IsInvertible.of_iso e.symm

/-- An actual covering with isomorphisms from the standard rank-one free
sheaf to each restriction of the given sheaf. -/
structure LocalTrivializations (M : _root_.SheafOfModules.{u} R) where
  I : Type u₁
  X : I → C
  coversTop : J.CoversTop X
  iso (i : I) :
    _root_.SheafOfModules.free (R := R.over (X i)) PUnit ≅ M.over (X i)

/-- Relabel a singleton local basis by `PUnit`, then use its given
isomorphic presentation map. -/
def LocalGeneratorsData.IsInvertible.trivializationIso
    {q : _root_.SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.IsInvertible q) (i : q.I) :
    _root_.SheafOfModules.free (R := R.over (q.X i)) PUnit ≅ M.over (q.X i) := by
  letI : Nonempty (q.generators i).I := hq.basisNonempty i
  letI : Subsingleton (q.generators i).I := hq.basisSubsingleton i
  letI := hq.isLocallyFreeData.isIso i
  exact
    ((_root_.SheafOfModules.freeFunctor (R := R.over (q.X i))).mapIso
      Equiv.punitOfNonemptyOfSubsingleton.symm.toIso).trans
      (asIso (q.generators i).π)

namespace LocalTrivializations

/-- Compose each trivialization with the restricted sheaf isomorphism. -/
def ofIso (t : LocalTrivializations M) (e : M ≅ N) : LocalTrivializations N where
  I := t.I
  X := t.X
  coversTop := t.coversTop
  iso i := t.iso i ≪≫ (_root_.SheafOfModules.overFunctor R (t.X i)).mapIso e

/-- The standard free generator, transported by each trivialization,
gives literal rank-one local generator data. -/
theorem isInvertible (t : LocalTrivializations M) : IsInvertible M := by
  let q : _root_.SheafOfModules.LocalGeneratorsData M := {
    I := t.I
    X := t.X
    coversTop := t.coversTop
    generators i :=
      (_root_.SheafOfModules.free.generatingSections
        (R := R.over (t.X i)) PUnit).ofEpi (t.iso i).hom }
  refine ⟨q, {
    isLocallyFreeData := { isIso := ?_ }
    basisNonempty := ?_
    basisSubsingleton := ?_ }⟩
  · intro i
    change IsIso ((_root_.SheafOfModules.free.generatingSections
      (R := R.over (t.X i)) PUnit).ofEpi (t.iso i).hom).π
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π,
      _root_.SheafOfModules.free.generatingSections_π]
    infer_instance
  · intro i
    change Nonempty PUnit
    infer_instance
  · intro i
    change Subsingleton PUnit
    infer_instance

/-- Choose the trivializations already proved to exist in the rank-one
local generator predicate. -/
def ofIsInvertible (M : _root_.SheafOfModules.{u} R) [h : IsInvertible M] :
    LocalTrivializations M := by
  let q := h.exists_isInvertible.choose
  let hq := h.exists_isInvertible.choose_spec
  exact {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    iso := fun i ↦ hq.trivializationIso i }

theorem nonempty_iff_isInvertible :
    Nonempty (LocalTrivializations M) ↔ IsInvertible M := by
  constructor
  · rintro ⟨t⟩
    exact t.isInvertible
  · intro h
    letI := h
    exact ⟨ofIsInvertible M⟩

end LocalTrivializations

section Unit

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- The unit sheaf is trivial on every object of the site. The family of
all objects is an actual cover: each object has its identity morphism. -/
def unitLocalTrivializations : LocalTrivializations (_root_.SheafOfModules.unit R) where
  I := C
  X U := U
  coversTop := by
    intro U
    have h : Sieve.ofObjects (fun V : C ↦ V) U = ⊤ := by
      ext V f
      exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨V, ⟨𝟙 V⟩⟩⟩
    rw [h]
    exact J.top_mem U
  iso U :=
    _root_.SheafOfModules.freeUniqueIsoUnit (R := R.over U) PUnit ≪≫
      (_root_.SheafOfModules.unitOverIso (R := R) U).symm

instance unit_isInvertible : IsInvertible (_root_.SheafOfModules.unit R) :=
  (unitLocalTrivializations (R := R)).isInvertible

variable [HasWeakSheafify J AddCommGrp.{u}]
  [J.WEqualsLocallyBijective AddCommGrp.{u}]

/-- A free sheaf on any singleton basis is invertible. Its actual
coproduct is isomorphic to the unit sheaf. -/
instance free_isInvertible (I : Type u) [Nonempty I] [Subsingleton I] :
    IsInvertible (_root_.SheafOfModules.free (R := R) I) :=
  IsInvertible.of_iso (_root_.SheafOfModules.freeUniqueIsoUnit (R := R) I).symm

end Unit

end KltDP.SheafOfModules
