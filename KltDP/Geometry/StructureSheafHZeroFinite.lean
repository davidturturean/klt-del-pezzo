import KltDP.Geometry.ModuleCohomology
import KltDP.Geometry.ProperGlobalSectionsFinite
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Finite degree-zero cohomology of the actual structure sheaf

The coefficient sheaf is `SheafOfModules.unit X.ringCatSheaf`, and its
cohomology is the existing Ext-based cohomology of its underlying additive
sheaf. The base-field action is the canonical global-function action
restricted along the original structure morphism's map on global sections.

The proved global-function-linear H0 comparison restricts to a base-field
linear equivalence. Finiteness then follows from the pinned theorem on
global functions of an integral universally closed finite-type scheme.
No assertion about other coefficient sheaves or positive degrees is made.

Reuse: the canonical H0 comparison is the attributed Mazur source port in
`ModuleCohomology`. Scalar restriction and finiteness transfer use the
pinned `Module.compHom`, `IsScalarTower.of_algebraMap_smul`,
`LinearEquiv.restrictScalars`, and `Module.Finite.equiv`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace KltDP.Geometry.StructureSheafCohomology

open ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The actual structure sheaf regarded as a module over itself. -/
abbrev structureSheaf (X : Scheme.{u}) : X.Modules :=
  _root_.SheafOfModules.unit X.ringCatSheaf

/-- Genuine degree-zero cohomology of that coefficient sheaf. -/
abbrev HZero (X : Scheme.{u}) : Type u := H (structureSheaf X) 0

/-- The canonical H0 comparison specializes to actual global functions. -/
def hZeroLinearEquivGlobalSections (X : Scheme.{u}) :
    letI := globalSectionsCohomologyModule (structureSheaf X) 0
    HZero X ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  hZeroCanonicalLinearEquivGlobalSections (structureSheaf X)

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The base-field action obtained from the canonical cohomology action
through the original structure morphism. -/
noncomputable abbrev baseHZeroModule (f : X ⟶ Spec (CommRingCat.of k)) :
    Module k (HZero X) := by
  letI := globalSectionsCohomologyModule (structureSheaf X) 0
  exact Module.compHom (HZero X) (baseFieldToGlobalSections f)

/-- A base scalar acts by cohomology of multiplication by its actual
global function on the coefficient sheaf. -/
theorem baseHZeroModule_smul (f : X ⟶ Spec (CommRingCat.of k))
    (r : k) (x : HZero X) :
    letI := baseHZeroModule f
    r • x = (zariskiFunctor X 0).map
      (globalSmulHom (structureSheaf X) (baseFieldToGlobalSections f r)) x := rfl

/-- The actual H0 comparison is linear for the original base-field action. -/
def hZeroBaseLinearEquivGlobalSections (f : X ⟶ Spec (CommRingCat.of k)) :
    letI := (baseFieldToGlobalSections f).toAlgebra
    letI := baseHZeroModule f
    HZero X ≃ₗ[k] Γ(X, ⊤) := by
  letI := (baseFieldToGlobalSections f).toAlgebra
  letI := globalSectionsCohomologyModule (structureSheaf X) 0
  letI := baseHZeroModule f
  letI : IsScalarTower k Γ(X, ⊤) (HZero X) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact (hZeroLinearEquivGlobalSections X).restrictScalars k

/-- H0 of the structure sheaf is finite for the specified base-field action. -/
theorem hZero_moduleFinite
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    [UniversallyClosed f] [LocallyOfFiniteType f] :
    letI := baseHZeroModule f
    Module.Finite k (HZero X) := by
  letI := (baseFieldToGlobalSections f).toAlgebra
  letI := baseHZeroModule f
  letI := globalSections_moduleFinite f
  exact Module.Finite.equiv (hZeroBaseLinearEquivGlobalSections f).symm

/-- The corresponding degree-zero vector space is finite-dimensional. -/
theorem hZero_finiteDimensional
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    [UniversallyClosed f] [LocallyOfFiniteType f] :
    letI := baseHZeroModule f
    FiniteDimensional k (HZero X) :=
  hZero_moduleFinite f

end KltDP.Geometry.StructureSheafCohomology
