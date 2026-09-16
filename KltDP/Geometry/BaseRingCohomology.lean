import KltDP.Geometry.BaseFieldCohomology

/-!
# Cohomology over an arbitrary commutative base ring

Restrict the existing global-function action along the actual morphism
to Spec A. The cohomology groups, coefficient morphisms and degree-zero
comparison are unchanged. Specialization to a field gives the existing
base-field structures and comparison by definitional equality.

The scalar map is the canonical Gamma-Spec isomorphism followed by
f.appTop. Its generic expression also appears as testGlobalRingMap in
AffineBlowupSchemeLift; using it directly here avoids importing the
blowup constructions into cohomology merely to name that ring map.

No properness, Noetherianity, coherence or finite-generation assertion is
made. Source correspondence: docs/BASE_RING_COHOMOLOGY_CORRESPONDENCE.md.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section CommRing

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of A))

/-- The actual base ring acts through the original global functions. -/
abbrev baseRingModule (M : X.Modules) (n : ℕ) : Module A (H M n) := by
  letI := globalSectionsCohomologyModule M n
  exact Module.compHom (H M n)
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)

/-- Scalars act by cohomology of the original multiplication morphism. -/
theorem baseRingModule_smul (M : X.Modules) (n : ℕ) (a : A) (x : H M n) :
    letI := baseRingModule f M n
    a • x = (zariskiFunctor X n).map
      (globalSmulHom M
        (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) x := rfl

/-- Every original coefficient morphism induces a base-ring-linear map. -/
def baseRingLinearMap (n : ℕ) {M N : X.Modules} (g : M ⟶ N) :
    letI := baseRingModule f M n
    letI := baseRingModule f N n
    H M n →ₗ[A] H N n := by
  letI := globalSectionsCohomologyModule M n
  letI := globalSectionsCohomologyModule N n
  letI := baseRingModule f M n
  letI := baseRingModule f N n
  refine
    { toFun := (zariskiFunctor X n).map g
      map_add' := ((zariskiFunctor X n).map g).hom.map_add
      map_smul' := ?_ }
  intro a x
  exact (cohomologyLinearMap n g).map_smul
    (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) x

/-- Actual global sections with the action of the same original base ring. -/
abbrev baseRingSectionsModule (M : X.Modules) : Module A (sections M) :=
  Module.compHom (sections M)
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)

/-- The existing degree-zero comparison is linear over any commutative base ring. -/
def hZeroBaseRingLinearEquivSections (M : X.Modules) :
    letI := baseRingModule f M 0
    letI := baseRingSectionsModule f M
    H M 0 ≃ₗ[A] sections M := by
  letI :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).toAlgebra
  letI := globalSectionsCohomologyModule M 0
  letI := baseRingModule f M 0
  letI := baseRingSectionsModule f M
  letI : IsScalarTower A Γ(X, ⊤) (H M 0) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower A Γ(X, ⊤) (sections M) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact (hZeroCanonicalLinearEquivGlobalSections M).restrictScalars A

end CommRing

section Field

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k))

/-- Field specialization retains the full existing cohomology module structure. -/
theorem baseRingModule_eq_baseModule (M : X.Modules) (n : ℕ) :
    baseRingModule f M n = baseModule f M n := rfl

/-- Field specialization retains the full existing global-sections module structure. -/
theorem baseRingSectionsModule_eq_baseSectionsModule (M : X.Modules) :
    baseRingSectionsModule f M = baseSectionsModule f M := rfl

/-- The coefficient map specializes to the original base-field-linear map. -/
theorem baseRingLinearMap_eq_baseLinearMap (n : ℕ) {M N : X.Modules} (g : M ⟶ N) :
    letI := baseModule f M n
    letI := baseModule f N n
    baseRingLinearMap f n g = baseLinearMap f n g := rfl

/-- The whole linear equivalence, not only its underlying function, is unchanged. -/
theorem hZeroBaseRingLinearEquivSections_eq (M : X.Modules) :
    letI := baseModule f M 0
    letI := baseSectionsModule f M
    hZeroBaseRingLinearEquivSections f M = hZeroBaseLinearEquivSections f M := rfl

end Field

end KltDP.Geometry.ModuleCohomology
