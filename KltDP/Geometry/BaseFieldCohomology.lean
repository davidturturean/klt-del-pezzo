import KltDP.Geometry.ModuleCohomology
import KltDP.Geometry.ProperGlobalSectionsFinite
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Base-field cohomology of actual scheme modules

Restrict the existing global-function action along the original structure
morphism. This gives a module-valued cohomology functor for every coefficient
module and degree. Coefficient-sheaf isomorphisms induce linear equivalences,
and the existing H0 comparison is linear over the same base field.

The groups remain the existing Ext-based Zariski cohomology groups.
No finiteness, higher vanishing, or Euler formula is asserted.
Reuse and source correspondence: docs/BASE_FIELD_COHOMOLOGY_CORRESPONDENCE.md.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k))

/-- The base field acts through its actual global functions. -/
abbrev baseModule (M : X.Modules) (n : ℕ) : Module k (H M n) := by
  letI := globalSectionsCohomologyModule M n
  exact Module.compHom (H M n) (baseFieldToGlobalSections f)

/-- Scalars act by cohomology of the actual coefficient endomorphism. -/
theorem baseModule_smul (M : X.Modules) (n : ℕ) (r : k) (x : H M n) :
    letI := baseModule f M n
    r • x = (zariskiFunctor X n).map
      (globalSmulHom M (baseFieldToGlobalSections f r)) x := rfl

/-- The map induced by a coefficient morphism is base-field-linear. -/
def baseLinearMap (n : ℕ) {M N : X.Modules} (g : M ⟶ N) :
    letI := baseModule f M n
    letI := baseModule f N n
    H M n →ₗ[k] H N n := by
  letI := globalSectionsCohomologyModule M n
  letI := globalSectionsCohomologyModule N n
  letI := baseModule f M n
  letI := baseModule f N n
  refine
    { toFun := (zariskiFunctor X n).map g
      map_add' := ((zariskiFunctor X n).map g).hom.map_add
      map_smul' := ?_ }
  intro r x
  exact (cohomologyLinearMap n g).map_smul (baseFieldToGlobalSections f r) x

/-- Actual Zariski cohomology valued in modules over the original field. -/
def baseFunctor (n : ℕ) : X.Modules ⥤ ModuleCat.{u} k where
  obj M := by
    letI := baseModule f M n
    exact ModuleCat.of k (H M n)
  map {M N} g := by
    letI := baseModule f M n
    letI := baseModule f N n
    exact ModuleCat.ofHom (baseLinearMap f n g)
  map_id M := by
    letI := baseModule f M n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (zariskiFunctor X n).map (𝟙 M) x = x
    exact ConcreteCategory.congr_hom ((zariskiFunctor X n).map_id M) x
  map_comp {M N P} g h := by
    letI := baseModule f M n
    letI := baseModule f N n
    letI := baseModule f P n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (zariskiFunctor X n).map (g ≫ h) x =
      (zariskiFunctor X n).map h ((zariskiFunctor X n).map g x)
    exact ConcreteCategory.congr_hom ((zariskiFunctor X n).map_comp g h) x

/-- A coefficient-sheaf isomorphism induces a base-field linear equivalence. -/
def baseLinearEquiv (n : ℕ) {M N : X.Modules} (e : M ≅ N) :
    letI := baseModule f M n
    letI := baseModule f N n
    H M n ≃ₗ[k] H N n :=
  ((baseFunctor f n).mapIso e).toLinearEquiv

/-- Isomorphic actual coefficients give equal finrank. This transports
finrank without asserting finite-dimensionality. -/
theorem finrank_eq_of_iso (n : ℕ) {M N : X.Modules} (e : M ≅ N) :
    letI := baseModule f M n
    letI := baseModule f N n
    Module.finrank k (H M n) = Module.finrank k (H N n) := by
  letI := baseModule f M n
  letI := baseModule f N n
  exact (baseLinearEquiv f n e).finrank_eq

/-- The original base-field action on actual global sections. -/
abbrev baseSectionsModule (M : X.Modules) : Module k (sections M) :=
  Module.compHom (sections M) (baseFieldToGlobalSections f)

/-- The existing H0 comparison is base-field-linear for every actual M. -/
def hZeroBaseLinearEquivSections (M : X.Modules) :
    letI := baseModule f M 0
    letI := baseSectionsModule f M
    H M 0 ≃ₗ[k] sections M := by
  letI := (baseFieldToGlobalSections f).toAlgebra
  letI := globalSectionsCohomologyModule M 0
  letI := baseModule f M 0
  letI := baseSectionsModule f M
  letI : IsScalarTower k Γ(X, ⊤) (H M 0) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower k Γ(X, ⊤) (sections M) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact (hZeroCanonicalLinearEquivGlobalSections M).restrictScalars k

end KltDP.Geometry.ModuleCohomology
