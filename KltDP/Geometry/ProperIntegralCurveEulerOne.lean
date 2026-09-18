import KltDP.Geometry.IntegralStructureCohomologyScalars
import KltDP.Geometry.AffineHZeroOneIso
import KltDP.Geometry.ProperCurveEuler
import KltDP.AdmissionProbe.ProperFiniteRankCohomology

/-!
Euler characteristic one on an original proper integral scheme of dimension
at most one forces H0 to have dimension one and H1 to vanish, over any field.
The actual global-section scalar map is consequently an isomorphism.

The proof uses the existing global-section field and its cohomology action.
Only the final passage from zero H1 dimension to the actual zero group uses
the already selected proper-coherent-cohomology finiteness theorem.
-/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.ProperIntegralCurveEulerOne

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- No algebraic closure of the base field is needed for these dimensions. -/
theorem cohomology_dimensions
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hχ : eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 1) :
    cohomologyDimension f (_root_.SheafOfModules.unit X.ringCatSheaf) 0 = 1 ∧
      cohomologyDimension f (_root_.SheafOfModules.unit X.ringCatSheaf) 1 = 0 := by
  letI := (baseFieldToGlobalSections f).toAlgebra
  have h0 : cohomologyDimension f (_root_.SheafOfModules.unit X.ringCatSheaf) 0 =
      Module.finrank k Γ(X, ⊤) :=
    IntegralStructureCohomologyScalars.hZero_dimension_eq_globalSections_finrank f
  have hdiv : Module.finrank k Γ(X, ⊤) ∣
      cohomologyDimension f (_root_.SheafOfModules.unit X.ringCatSheaf) 1 :=
    IntegralStructureCohomologyScalars.globalSections_finrank_dvd_cohomologyDimension
      f (_root_.SheafOfModules.unit X.ringCatSheaf) 1
  have hEuler := proper_eulerCharacteristic_eq_h0_sub_h1 f hdim
    (_root_.SheafOfModules.unit X.ringCatSheaf)
  rw [hχ] at hEuler
  have hlt : cohomologyDimension f (_root_.SheafOfModules.unit X.ringCatSheaf) 1 <
      Module.finrank k Γ(X, ⊤) := by omega
  have h1 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
  exact ⟨by omega, h1⟩

/-- The original structure morphism identifies the ground field with all
global functions; this is the actual scalar map, not a chosen equivalence. -/
theorem baseFieldToGlobalSections_bijective
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hχ : eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 1) :
    Function.Bijective (baseFieldToGlobalSections f) :=
  AffineHZeroOneIso.baseFieldToGlobalSections_bijective f
    (cohomology_dimensions f hdim hχ).1

/-- The original global-section scalar arrow is an isomorphism. -/
theorem globalScalar_isIso
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hχ : eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 1) :
    IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (baseFieldToGlobalSections_bijective f hdim hχ)

/-- Proper coherent finiteness turns the computed H1 dimension into actual
vanishing of the original Ext-based cohomology group. -/
theorem hOne_subsingleton
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hχ : eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 1) :
    Subsingleton (H (_root_.SheafOfModules.unit X.ringCatSheaf) 1) := by
  letI := baseModule f (_root_.SheafOfModules.unit X.ringCatSheaf) 1
  letI : FiniteDimensional k
      (H (_root_.SheafOfModules.unit X.ringCatSheaf) 1) :=
    KltDP.AdmissionProbe.ProperFiniteRankCohomology.proper_finiteRank_baseFunctor_finiteDimensional
      f (_root_.SheafOfModules.unit X.ringCatSheaf) 1 inferInstance 1
  exact (Module.finrank_zero_iff (R := k)).mp (cohomology_dimensions f hdim hχ).2

#check cohomology_dimensions
#print axioms cohomology_dimensions
#check baseFieldToGlobalSections_bijective
#print axioms baseFieldToGlobalSections_bijective
#check globalScalar_isIso
#print axioms globalScalar_isIso
#check hOne_subsingleton
#print axioms hOne_subsingleton

end KltDP.Geometry.ProperIntegralCurveEulerOne
