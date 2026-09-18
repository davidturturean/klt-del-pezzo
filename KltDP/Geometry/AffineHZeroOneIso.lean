import KltDP.Geometry.StructureSheafHZeroFinite
import KltDP.Geometry.ModuleCohomologyRanks
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
For an actual affine scheme over a field, H0 of the original structure
sheaf has dimension one exactly in the case relevant here: the original
structure map is an isomorphism. No reducedness of the affine scheme is
assumed; the original scalar map itself is proved bijective.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.AffineHZeroOneIso

/-- Dimension one makes the original global scalar map bijective. -/
theorem baseFieldToGlobalSections_bijective
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (h : cohomologyDimension f (_root_.SheafOfModules.unit X.ringCatSheaf) 0 = 1) :
    Function.Bijective (baseFieldToGlobalSections f) := by
  letI := (baseFieldToGlobalSections f).toAlgebra
  letI := StructureSheafCohomology.baseHZeroModule f
  have hd : Module.finrank k Γ(X, ⊤) = 1 :=
    (StructureSheafCohomology.hZeroBaseLinearEquivGlobalSections f).finrank_eq.symm.trans h
  letI : Nontrivial Γ(X, ⊤) := Module.nontrivial_of_finrank_eq_succ hd
  refine ⟨(baseFieldToGlobalSections f).injective, ?_⟩
  intro s
  obtain ⟨a, ha⟩ :=
    (_root_.finrank_eq_one_iff_of_nonzero' (1 : Γ(X, ⊤)) one_ne_zero).mp hd s
  refine ⟨a, ?_⟩
  simpa only [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra] using ha

/-- The original affine structure morphism is an isomorphism when its
actual structure-sheaf H0 has dimension one. -/
theorem isIso_of_cohomologyDimension_eq_one
    {k : Type u} [Field k] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of k))
    (h : cohomologyDimension f (_root_.SheafOfModules.unit X.ringCatSheaf) 0 = 1) :
    IsIso f := by
  have hb : Function.Bijective
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom) :=
    baseFieldToGlobalSections_bijective f h
  letI : IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  letI : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of k)).inv f.appTop
  exact (HasAffineProperty.iff_of_isAffine (P := CategoryTheory.MorphismProperty.isomorphisms Scheme)
    (f := f)).mpr ⟨inferInstance, inferInstance⟩

#check KltDP.Geometry.AffineHZeroOneIso.isIso_of_cohomologyDimension_eq_one
#print axioms KltDP.Geometry.AffineHZeroOneIso.isIso_of_cohomologyDimension_eq_one

end KltDP.Geometry.AffineHZeroOneIso
