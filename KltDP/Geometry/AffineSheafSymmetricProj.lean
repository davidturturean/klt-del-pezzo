/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.SymmetricProjectiveModuleEquiv
import KltDP.Geometry.SymmetricProjectiveSpectrumEmptyProjective
import KltDP.Geometry.FieldFiniteTypeGlobalSections
import KltDP.Geometry.AffineModuleTildeAdjunction

/-!
# The actual affine symmetric Proj of a sheaf on a field spectrum

The algebra is the original symmetric quotient of the original global-section
module, with its canonical field action. No basis or projective-space model is
used to define this object. Original sheaf isomorphisms and the actual tilde
unit induce proved graded algebra and scheme isomorphisms over the field.

Original finite-type local generators imply projectivity of this affine Proj,
including the zero-module case. Identifying this explicit affine construction
with a separately defined relative Proj of the symmetric algebra sheaf remains
a separate source-translation obligation; no published projectivity theorem
or stage-projectivity conclusion is assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineSheafSymmetricProj

open KltDP.SymmetricAlgebra AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The original graded quotient algebra of actual global sections. -/
abbrev sectionAlgebra (E : (Spec (.of k)).Modules) :=
  KltDP.SymmetricAlgebra k (sectionModule E ⊤)

/-- Intrinsic symmetric degrees on the original section algebra. -/
abbrev sectionGrading (E : (Spec (.of k)).Modules) :
    ℕ → Submodule k (sectionAlgebra E) := grading k (sectionModule E ⊤)

/-- The affine symmetric Proj, without choosing a rank or a basis. -/
def scheme (E : (Spec (.of k)).Modules) : Scheme.{u} := Proj (sectionGrading E)

/-- Its original degree-zero structure morphism to the given field. -/
def toSpec (E : (Spec (.of k)).Modules) : scheme E ⟶ Spec (.of k) :=
  SymmetricProjectiveSpace.structureMap k (sectionModule E ⊤)

variable {E F : (Spec (.of k)).Modules}

/-- Evaluation of the original sheaf isomorphism with the original k-action. -/
def sectionsEquiv (e : E ≅ F) : sectionModule E ⊤ ≃ₗ[k] sectionModule F ⊤ :=
  ((globalSectionsFunctor k).mapIso e).toLinearEquiv

@[simp]
theorem sectionsEquiv_apply (e : E ≅ F) (s : sectionModule E ⊤) :
    sectionsEquiv e s = e.hom.val.app (op ⊤) s := rfl

/-- Functorial transport uses the original global section map on generators. -/
def sectionAlgebraEquiv (e : E ≅ F) : sectionAlgebra E ≃ₐ[k] sectionAlgebra F :=
  congr (sectionsEquiv e)

@[simp]
theorem sectionAlgebraEquiv_ι (e : E ≅ F) (s : sectionModule E ⊤) :
    sectionAlgebraEquiv e (ι k (sectionModule E ⊤) s) =
      ι k (sectionModule F ⊤) (e.hom.val.app (op ⊤) s) :=
  congr_ι (sectionsEquiv e) s

/-- Degree preservation and reflection are proved for the original grading. -/
theorem sectionAlgebraEquiv_mem_iff (e : E ≅ F) (n : ℕ) (a : sectionAlgebra E) :
    sectionAlgebraEquiv e a ∈ sectionGrading F n ↔ a ∈ sectionGrading E n :=
  congr_mem_grading_iff (sectionsEquiv e) n a

/-- The induced original scheme isomorphism, retaining its actual point and
homogeneous-localization maps. -/
def iso (e : E ≅ F) : scheme E ≅ scheme F :=
  SymmetricProjectiveModuleEquiv.iso (sectionsEquiv e)

/-- This comparison is over the original field, not only an unstructured iso. -/
theorem iso_toSpec (e : E ≅ F) : (iso e).hom ≫ toSpec F = toSpec E :=
  SymmetricProjectiveModuleEquiv.iso_structure (sectionsEquiv e)

/-- The original tilde-to-global-sections unit induces an actual affine Proj
comparison. No supplied replacement section equivalence is an input. -/
def tildeIso (M : ModuleCat.{u} k) :
    Proj (grading k M) ≅ scheme M.tilde :=
  SymmetricProjectiveModuleEquiv.iso ((unitNatIso k).app M).toLinearEquiv

/-- The tilde comparison preserves the original structure morphism. -/
theorem tildeIso_toSpec (M : ModuleCat.{u} k) :
    (tildeIso M).hom ≫ toSpec M.tilde = SymmetricProjectiveSpace.structureMap k M :=
  SymmetricProjectiveModuleEquiv.iso_structure ((unitNatIso k).app M).toLinearEquiv

/-- The algebra comparison underlying the tilde Proj iso sends an original
module generator to its actual canonical global section. -/
theorem tilde_algebraEquiv_ι (M : ModuleCat.{u} k) (m : M) :
    congr ((unitNatIso k).app M).toLinearEquiv (ι k M m) =
      ι k (sectionModule M.tilde ⊤) (ModuleCat.Tilde.toOpen M ⊤ m) :=
  congr_ι ((unitNatIso k).app M).toLinearEquiv m

/-- Finite type of the original sheaf suffices for actual projectivity.
The finite module is derived from local generators and is not an input. -/
theorem toSpec_isProjective (E : (Spec (.of k)).Modules)
    [_root_.SheafOfModules.IsFiniteType E] : IsProjectiveOverField (toSpec E) := by
  letI : Module.Finite k (sectionModule E ⊤) :=
    globalSections_finite_of_isFiniteType k E
  exact SymmetricProjectiveSpectrumEmptyProjective.structureMap_isProjective
    k (sectionModule E ⊤)

/-- A genuine closed immersion over the field into this original affine
symmetric Proj gives the existing projectivity predicate. -/
theorem projective_of_closedImmersion (E : (Spec (.of k)).Modules)
    [_root_.SheafOfModules.IsFiniteType E] {X : Scheme.{u}}
    (i : X ⟶ scheme E) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of k)) (hif : i ≫ toSpec E = f) : IsProjectiveOverField f := by
  letI : Module.Finite k (sectionModule E ⊤) :=
    globalSections_finite_of_isFiniteType k E
  exact SymmetricProjectiveSpectrumEmptyProjective.projective_of_closedImmersion_over i f hif

end KltDP.Geometry.AffineSheafSymmetricProj
