import KltDP.Geometry.StructureSheafHZeroFinite
import KltDP.Geometry.ModuleCohomologyRanks
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
The original global-section algebra acts on the original cohomology groups.
For an integral universally closed finite-type scheme over a field, this
algebra is a finite field extension. Its degree therefore divides each
cohomology dimension for the original base-field action.

The field structure is supplied by `fieldOfFiniteDimensional`, which keeps
the original commutative ring. No geometric-integrality or algebraic-closure
hypothesis, change of structure morphism, or cohomology base change is used.
-/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.IntegralStructureCohomologyScalars

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- H0 is the actual section algebra, with the original field action. -/
theorem hZero_dimension_eq_globalSections_finrank
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) :
    letI := (baseFieldToGlobalSections f).toAlgebra
    cohomologyDimension f (_root_.SheafOfModules.unit X.ringCatSheaf) 0 =
      Module.finrank k Γ(X, ⊤) := by
  letI := (baseFieldToGlobalSections f).toAlgebra
  letI := StructureSheafCohomology.baseHZeroModule f
  exact (StructureSheafCohomology.hZeroBaseLinearEquivGlobalSections f).finrank_eq

/-- The degree of the original field of constants divides every original
cohomology dimension, by restriction of scalars. -/
theorem globalSections_finrank_dvd_cohomologyDimension
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k))
    [UniversallyClosed f] [LocallyOfFiniteType f]
    (M : X.Modules) (n : ℕ) :
    letI := (baseFieldToGlobalSections f).toAlgebra
    Module.finrank k Γ(X, ⊤) ∣ cohomologyDimension f M n := by
  letI := (baseFieldToGlobalSections f).toAlgebra
  letI : Module.Finite k Γ(X, ⊤) := globalSections_moduleFinite f
  letI : Field Γ(X, ⊤) := fieldOfFiniteDimensional k Γ(X, ⊤)
  letI := globalSectionsCohomologyModule M n
  letI := baseModule f M n
  letI : IsScalarTower k Γ(X, ⊤) (H M n) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  refine ⟨Module.finrank Γ(X, ⊤) (H M n), ?_⟩
  exact (Module.finrank_mul_finrank k Γ(X, ⊤) (H M n)).symm

#check hZero_dimension_eq_globalSections_finrank
#print axioms hZero_dimension_eq_globalSections_finrank
#check globalSections_finrank_dvd_cohomologyDimension
#print axioms globalSections_finrank_dvd_cohomologyDimension

end KltDP.Geometry.IntegralStructureCohomologyScalars
