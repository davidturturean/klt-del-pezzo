/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck

The forward comparison specializes the argument in CBirkbeck/AINTLIB
7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/Picard/PicComparison.lean, lines 432–447.
The actual local rank-one predicate and skeleton-units object are the
independently defined project interfaces.
-/
import KltDP.Geometry.InvertibleSheaf
import KltDP.Geometry.SheafPicard
import KltDP.Compatibility.InvertibleTensorUnit

/-!
# The forward map from invertible sheaves to the actual Picard group

An actual locally free rank-one sheaf defines a tensor-invertible class.
Its unit witness comes from the proved evaluation isomorphism with the
sheaf dual. The underlying class is exactly that of the original sheaf.
No converse, Cartier comparison or numerical divisor interpretation is
included here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.InvertibleSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}}

/-- The canonical underlying class projection from the existing Picard
group, exposed explicitly because `Scheme.Pic` is a definition. -/
instance picardClassCoe (X : Scheme.{u}) : Coe X.Pic (Skeleton X.Modules) where
  coe p := by
    letI := Scheme.Modules.monoidalCategory X
    exact (show (Skeleton X.Modules)ˣ from p).val

/-- The underlying isomorphism class of a locally free rank-one sheaf is
a unit in the actual tensor monoid of structure-sheaf modules. -/
theorem isUnit_toSkeleton (L : InvertibleSheaf X) :
    letI := Scheme.Modules.monoidalCategory X
    IsUnit (toSkeleton L.obj) :=
  KltDP.SheafOfModules.IsInvertible.isUnit_toSkeleton
    X.sheaf.val X.ringCatSheaf.cond L.obj

/-- The actual Picard class of a locally free rank-one sheaf. -/
noncomputable def toPic (L : InvertibleSheaf X) : X.Pic := by
  letI := Scheme.Modules.monoidalCategory X
  exact (isUnit_toSkeleton L).unit

/-- The forward map retains the original sheaf's isomorphism class. -/
@[simp]
theorem toPic_val (L : InvertibleSheaf X) :
    letI := Scheme.Modules.monoidalCategory X
    (toPic L : Skeleton X.Modules) = toSkeleton L.obj := by
  letI := Scheme.Modules.monoidalCategory X
  exact (isUnit_toSkeleton L).unit_spec

end KltDP.Geometry.InvertibleSheaf
