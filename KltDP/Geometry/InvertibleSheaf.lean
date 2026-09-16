/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from Vilin97/TauCeti a74dfee78f800df63f085a19006f7d502eee365e,
TauCeti/AlgebraicGeometry/LineBundle/Basic.lean. The trivial object here is
the pinned unit sheaf itself, with a proved isomorphism to the free singleton.
-/
import KltDP.Compatibility.InvertibleModuleSheaf
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Invertible sheaves on an actual scheme

These are actual objects of `X.Modules` satisfying the local rank-one
predicate. Morphisms are morphisms of the structure-sheaf modules. Local
trivializations, isomorphism transport, and the actual unit/free constructors
are available. Tensor products, duality, and the Picard group remain later
constructions; no numerical or global-section module replaces a sheaf here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The property of an actual structure-sheaf module being locally free
of rank one. -/
abbrev isInvertibleSheaf (X : Scheme.{u}) : ObjectProperty X.Modules :=
  KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf)

instance (X : Scheme.{u}) : (isInvertibleSheaf X).IsClosedUnderIsomorphisms where
  of_iso {M N} e h := by
    letI : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M := h
    exact KltDP.SheafOfModules.IsInvertible.of_iso
      (R := X.ringCatSheaf) (M := M) (N := N) e

/-- The full subcategory of actual locally free rank-one module sheaves. -/
abbrev InvertibleSheaf (X : Scheme.{u}) := (isInvertibleSheaf X).FullSubcategory

namespace InvertibleSheaf

variable {X : Scheme.{u}}

instance (L : InvertibleSheaf X) : isInvertibleSheaf X L.obj := L.property

/-- Local trivializations of the underlying actual module sheaf. -/
def localTrivializations (L : InvertibleSheaf X) :
    KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) L.obj :=
  KltDP.SheafOfModules.LocalTrivializations.ofIsInvertible
    (R := X.ringCatSheaf) L.obj

/-- An atlas of actual rank-one trivializations constructs an invertible
sheaf with exactly the given underlying module sheaf. -/
def ofLocalTrivializations (M : X.Modules)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M) :
    InvertibleSheaf X :=
  ⟨M, KltDP.SheafOfModules.LocalTrivializations.isInvertible
    (R := X.ringCatSheaf) t⟩

/-- Transport the rank-one condition along an actual module-sheaf isomorphism. -/
def ofIso (L : InvertibleSheaf X) {M : X.Modules} (e : L.obj ≅ M) : InvertibleSheaf X :=
  ⟨M, KltDP.SheafOfModules.IsInvertible.of_iso
    (R := X.ringCatSheaf) (M := L.obj) (N := M) e⟩

/-- The actual free module sheaf on a singleton basis. -/
def free (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] : InvertibleSheaf X :=
  ⟨_root_.SheafOfModules.free (R := X.ringCatSheaf) I, inferInstance⟩

/-- The actual structure-sheaf module over itself. -/
def trivial (X : Scheme.{u}) : InvertibleSheaf X :=
  ⟨_root_.SheafOfModules.unit X.ringCatSheaf, inferInstance⟩

@[simp]
theorem trivial_obj (X : Scheme.{u}) :
    (trivial X).obj = _root_.SheafOfModules.unit X.ringCatSheaf := rfl

@[simp]
theorem free_obj (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    (free X I).obj = _root_.SheafOfModules.free (R := X.ringCatSheaf) I := rfl

/-- The singleton free constructor and the trivial sheaf agree up to an
actual isomorphism in the full subcategory. -/
def freeIsoTrivial (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    free X I ≅ trivial X :=
  ObjectProperty.isoMk (isInvertibleSheaf X)
    (_root_.SheafOfModules.freeUniqueIsoUnit (R := X.ringCatSheaf) I)

instance (X : Scheme.{u}) : Nonempty (InvertibleSheaf X) := ⟨trivial X⟩

end InvertibleSheaf

/-- The scheme-level rank-one predicate is equivalent to an actual cover
and local free rank-one isomorphisms. -/
theorem isInvertibleSheaf_iff_localTrivializations (X : Scheme.{u}) (M : X.Modules) :
    isInvertibleSheaf X M ↔
      Nonempty (KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M) :=
  (KltDP.SheafOfModules.LocalTrivializations.nonempty_iff_isInvertible
    (R := X.ringCatSheaf) (M := M)).symm

end KltDP.Geometry
