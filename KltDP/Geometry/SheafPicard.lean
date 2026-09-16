/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck

Adapted from Vilin97/MazurTheorem 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/AINTLIB/Picard/Pic.lean.
Original source: CBirkbeck/AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/Picard/Pic.lean.
Imports, sheaf projections and transparent-definition attributes are adapted
to Lean 4.19 and the pinned Mathlib.
-/
import KltDP.Compatibility.SheafModuleSymmetric
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Monoidal.Skeleton

/-!
# Tensor-invertible module-sheaf classes on an actual scheme

The category `X.Modules` has the symmetric tensor structure constructed
from presheaf tensor and module sheafification. Its skeleton is the existing
quotient by actual sheaf isomorphisms. `Scheme.Pic X` is the group of units
in that tensor monoid, so each class comes with a tensor-inverse class.

This construction does not identify tensor-invertible sheaves with the
separately defined locally free rank-one sheaves. No Cartier/principal
comparison, Picard pullback, degree, intersection form, numerical quotient
or Picard-lattice property is assumed or supplied here.
-/

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace Modules

/-- The actual monoidal category of modules over the structure sheaf.
This definition exposes data without installing a global instance. -/
noncomputable abbrev monoidalCategory (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  PresheafOfModules.sheafOfModulesMonoidalCategory X.sheaf.val X.ringCatSheaf.cond

/-- The symmetric structure on the same structure-sheaf tensor category. -/
noncomputable abbrev symmetricCategory (X : Scheme.{u}) :
    letI := monoidalCategory X
    SymmetricCategory X.Modules :=
  PresheafOfModules.sheafOfModulesSymmetricCategory X.sheaf.val X.ringCatSheaf.cond

end Modules

/-- The group of tensor-invertible isomorphism classes of actual
structure-sheaf modules. Its comparison with locally free rank-one sheaves
is a separate theorem, not part of this definition. -/
noncomputable def Pic (X : Scheme.{u}) : Type _ :=
  letI := Modules.monoidalCategory X
  (Skeleton X.Modules)ˣ

/-- Braiding makes the tensor monoid of isomorphism classes commutative;
the existing units construction therefore gives an actual commutative group. -/
noncomputable instance (X : Scheme.{u}) : CommGroup (Pic X) :=
  letI := Modules.monoidalCategory X
  letI := Modules.symmetricCategory X
  inferInstanceAs (CommGroup (Skeleton X.Modules)ˣ)

end AlgebraicGeometry.Scheme
