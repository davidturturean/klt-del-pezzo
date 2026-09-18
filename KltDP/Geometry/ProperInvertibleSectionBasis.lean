import KltDP.AdmissionProbe.ProperCohomologyConsumers
import KltDP.Geometry.ModuleCohomologyRanks
import KltDP.Geometry.SchemeModulePullbackUnit
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# A complete basis of original sections on a proper scheme

The accepted proper-cohomology theorem supplies finiteness of the original
H0 for an actual invertible sheaf. The accepted base-field-linear H0
comparison transports its finite basis to the actual top sections. The
original top-section equivalence then gives compatible global families.
No global-generation condition is imposed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CompleteLinearSystemSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open ModuleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)

/-- The dimension of the entire original H0 with the original base-field action. -/
abbrev dimension : ℕ := cohomologyDimension f L.obj 0

variable [hproper : IsProper f]

include hproper

/-- Properness and original invertibility give finite-dimensional actual H0. -/
theorem cohomology_finiteDimensional :
    letI := baseModule f L.obj 0
    FiniteDimensional k (H L.obj 0) :=
  KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_invertible_field_finiteDimensional
    f L 0

/-- The same finiteness holds for the original top sections with their original scalar action. -/
theorem topSections_finiteDimensional :
    letI := baseSectionsModule f L.obj
    FiniteDimensional k (ModuleCohomology.sections L.obj) := by
  letI := baseModule f L.obj 0
  letI := baseSectionsModule f L.obj
  letI := cohomology_finiteDimensional f L
  exact Module.Finite.equiv (hZeroBaseLinearEquivSections f L.obj)

/-- A finite basis of the entire original cohomology space, indexed by its actual dimension. -/
def cohomologyBasis :
    letI := baseModule f L.obj 0
    Basis (Fin (dimension f L)) k (H L.obj 0) := by
  letI := baseModule f L.obj 0
  letI := cohomology_finiteDimensional f L
  exact Module.finBasis k (H L.obj 0)

/-- The actual H0 comparison carries that whole basis to the original top sections. -/
def topSectionBasis :
    letI := baseSectionsModule f L.obj
    Basis (Fin (dimension f L)) k (ModuleCohomology.sections L.obj) := by
  letI := baseModule f L.obj 0
  letI := baseSectionsModule f L.obj
  exact (cohomologyBasis f L).map (hZeroBaseLinearEquivSections f L.obj)

/-- The original top-section space has the same finite dimension as the original H0. -/
theorem dimension_eq_finrank_topSections :
    letI := baseSectionsModule f L.obj
    dimension f L = Module.finrank k (ModuleCohomology.sections L.obj) := by
  letI := baseModule f L.obj 0
  letI := baseSectionsModule f L.obj
  exact (hZeroBaseLinearEquivSections f L.obj).finrank_eq

/-- Each basis vector gives its actual compatible family on all original opens. -/
def basisSections : Fin (dimension f L) → L.obj.sections := by
  letI := baseSectionsModule f L.obj
  exact fun i => (schemeModuleSectionsEquivTop L.obj).symm (topSectionBasis f L i)

/-- Evaluation of each constructed compatible family recovers the original basis vector. -/
theorem basisSections_top (i : Fin (dimension f L)) :
    letI := baseSectionsModule f L.obj
    (basisSections f L i).val (op ⊤) = topSectionBasis f L i := by
  letI := baseSectionsModule f L.obj
  exact (schemeModuleSectionsEquivTop L.obj).apply_symm_apply (topSectionBasis f L i)

/-- The top values of the actual compatible families span all original global sections. -/
theorem basisSections_span :
    letI := baseSectionsModule f L.obj
    Submodule.span (M := ModuleCohomology.sections L.obj) k (Set.range (fun i =>
      ((basisSections f L i).val (op ⊤) : ModuleCohomology.sections L.obj))) = ⊤ := by
  letI := baseSectionsModule f L.obj
  simpa only [basisSections_top] using (topSectionBasis f L).span_eq

/-- Those original top values are linearly independent over the original base field. -/
theorem basisSections_linearIndependent :
    letI := baseSectionsModule f L.obj
    LinearIndependent (M := ModuleCohomology.sections L.obj) k (fun i =>
      ((basisSections f L i).val (op ⊤) : ModuleCohomology.sections L.obj)) := by
  letI := baseSectionsModule f L.obj
  simpa only [basisSections_top] using (topSectionBasis f L).linearIndependent

end KltDP.Geometry.CompleteLinearSystemSections
