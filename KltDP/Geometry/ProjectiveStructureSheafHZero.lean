import KltDP.Geometry.ProjectiveProper
import KltDP.Geometry.StructureSheafHZeroFinite
import KltDP.Geometry.ProperGlobalSectionsConstants

/-!
# Degree-zero structure-sheaf cohomology of projective integral schemes

The projective embedding proves properness and finite type. The actual
base-linear H0 comparison then identifies cohomology of the structure
sheaf with global functions. Over an algebraically closed field this gives
dimension one, including for the existing normal projective surface object.

The conclusion concerns actual Ext-based H0 and its canonical base action.
It asserts no positive-degree vanishing or Riemann--Roch formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.StructureSheafCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Proper integral schemes over an algebraically closed field have h0(O)=1. -/
theorem hZero_finrank_one [IsAlgClosed k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    [UniversallyClosed f] [LocallyOfFiniteType f] :
    letI := baseHZeroModule f
    Module.finrank k (HZero X) = 1 := by
  letI := (baseFieldToGlobalSections f).toAlgebra
  letI := baseHZeroModule f
  calc
    Module.finrank k (HZero X) = Module.finrank k Γ(X, ⊤) :=
      (hZeroBaseLinearEquivGlobalSections f).finrank_eq
    _ = 1 := globalSections_finrank_one f

/-- An actual projective embedding supplies the geometric finiteness inputs. -/
theorem hZero_moduleFinite_of_projective
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    (hf : IsProjectiveOverField f) :
    letI := baseHZeroModule f
    Module.Finite k (HZero X) := by
  letI := hf.isProper
  letI := hf.locallyOfFiniteType
  exact hZero_moduleFinite f

/-- The dimension-one result with only the actual projective embedding. -/
theorem hZero_finrank_one_of_projective [IsAlgClosed k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    (hf : IsProjectiveOverField f) :
    letI := baseHZeroModule f
    Module.finrank k (HZero X) = 1 := by
  letI := hf.isProper
  letI := hf.locallyOfFiniteType
  exact hZero_finrank_one f

/-- The manuscript's actual normal projective surface has h0(O)=1. -/
theorem normalProjectiveSurface_hZero_finrank_one [IsAlgClosed k]
    (X : NormalProjectiveSurface k) :
    letI := baseHZeroModule X.structureMorphism
    Module.finrank k (HZero X.toScheme) = 1 :=
  hZero_finrank_one_of_projective X.structureMorphism X.projective

end KltDP.Geometry.StructureSheafCohomology
