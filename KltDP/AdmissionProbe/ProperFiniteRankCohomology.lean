import KltDP.AdmissionProbe.ProperCohomologyConsumers
import KltDP.Geometry.FiniteLocallyFreeCoherent
import KltDP.Compatibility.ConstantRankTensor
import KltDP.Geometry.ProperCurveEuler

/-!
# Candidate ordinary finite-rank cohomology and Euler adapters

INACTIVE SOURCE CANDIDATE. This text is usable only in a root-staged isolated
checkout containing the selected source-bound proper-cohomology consumer
and finite-rank dependencies. It is not a production module or an admission.

Every coefficient is the original module sheaf on the original scheme, and
every cohomology group retains the scalar action induced by the original
structure morphism. Coherence follows from its actual finite local bases.
The existing consumer supplies finiteness through the proved linear
derived-to-Ext comparison. The independent dimension bound then identifies
the same Euler finsum with its two finite cohomological dimensions.

No positivity of rank, nonemptiness, reducedness, integrality, smoothness,
algebraic closure, or field-characteristic restriction is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KltDP.Geometry
open KltDP.Geometry.ModuleCohomology
open scoped CategoryTheory.MonoidalCategory

universe u

namespace KltDP.AdmissionProbe.ProperFiniteRankCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original finite-rank module has finite-dimensional cohomology for
the original proper structure morphism in every degree. -/
theorem proper_finiteRank_baseFunctor_finiteDimensional
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (E : Y.Modules) (r : ℕ)
    (hE : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) E r) (i : ℕ) :
    FiniteDimensional k ((baseFunctor f i).obj E) := by
  letI : IsLocallyNoetherian Y :=
    isLocallyNoetherian_of_locallyOfFiniteType_toSpec f
  letI : IsCoherentModule (X := Y) E :=
    isCoherentModule_of_isLocallyFreeOfRank (X := Y) E hE
  exact
    KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional
      (X := Y) f E i

/-- Finiteness and actual vanishing give the finite interpretation of the
original Euler expression on any proper scheme of dimension at most one. -/
theorem proper_finiteRank_euler_interpretation
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim Y ≤ 1)
    (E : Y.Modules) (r : ℕ)
    (hE : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) E r) :
    (∀ i, FiniteDimensional k ((baseFunctor f i).obj E)) ∧
      (∀ i, 1 < i → Subsingleton (H E i)) ∧
      eulerCharacteristic f E =
        (cohomologyDimension f E 0 : ℤ) -
          (cohomologyDimension f E 1 : ℤ) := by
  exact ⟨proper_finiteRank_baseFunctor_finiteDimensional f E r hE,
    proper_H_subsingleton_of_dimension_le_one (X := Y) f hdim E,
    proper_eulerCharacteristic_eq_h0_sub_h1 (X := Y) f hdim E⟩

/-- All four original coefficients in the finite-rank tensor-degree
statement have finite-dimensional cohomology. Their tensor rank is proved
by the actual product-basis comparison, and the structure module has rank one. -/
theorem proper_tensor_coefficients_finiteDimensional
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (E V : Y.Modules) (n m : ℕ)
    (hE : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) E n)
    (hV : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) V m) (i : ℕ) :
    letI := Scheme.Modules.monoidalCategory Y
    FiniteDimensional k ((baseFunctor f i).obj E) ∧
      FiniteDimensional k ((baseFunctor f i).obj V) ∧
      FiniteDimensional k ((baseFunctor f i).obj (E ⊗ V)) ∧
      FiniteDimensional k ((baseFunctor f i).obj
        (_root_.SheafOfModules.unit Y.ringCatSheaf)) := by
  letI := Scheme.Modules.monoidalCategory Y
  have hEV : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) (E ⊗ V) (n * m) :=
    KltDP.SheafOfModules.IsLocallyFreeOfRank.tensor (X := Y) hE hV
  have hO : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) (_root_.SheafOfModules.unit Y.ringCatSheaf) 1 :=
    inferInstance
  exact ⟨proper_finiteRank_baseFunctor_finiteDimensional f E n hE i,
    proper_finiteRank_baseFunctor_finiteDimensional f V m hV i,
    proper_finiteRank_baseFunctor_finiteDimensional f (E ⊗ V) (n * m) hEV i,
    proper_finiteRank_baseFunctor_finiteDimensional f
      (_root_.SheafOfModules.unit Y.ringCatSheaf) 1 hO i⟩

/-- The four original coefficients simultaneously have finite cohomology
and their Euler values equal the corresponding finite H0/H1 differences. -/
theorem proper_tensor_coefficients_euler_interpretation
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim Y ≤ 1)
    (E V : Y.Modules) (n m : ℕ)
    (hE : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) E n)
    (hV : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) V m) :
    letI := Scheme.Modules.monoidalCategory Y
    (∀ i, FiniteDimensional k ((baseFunctor f i).obj E) ∧
      FiniteDimensional k ((baseFunctor f i).obj V) ∧
      FiniteDimensional k ((baseFunctor f i).obj (E ⊗ V)) ∧
      FiniteDimensional k ((baseFunctor f i).obj
        (_root_.SheafOfModules.unit Y.ringCatSheaf))) ∧
      (eulerCharacteristic f E =
        (cohomologyDimension f E 0 : ℤ) - (cohomologyDimension f E 1 : ℤ)) ∧
      (eulerCharacteristic f V =
        (cohomologyDimension f V 0 : ℤ) - (cohomologyDimension f V 1 : ℤ)) ∧
      (eulerCharacteristic f (E ⊗ V) =
        (cohomologyDimension f (E ⊗ V) 0 : ℤ) -
          (cohomologyDimension f (E ⊗ V) 1 : ℤ)) ∧
      (eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) =
        (cohomologyDimension f (_root_.SheafOfModules.unit Y.ringCatSheaf) 0 : ℤ) -
          (cohomologyDimension f (_root_.SheafOfModules.unit Y.ringCatSheaf) 1 : ℤ)) := by
  letI := Scheme.Modules.monoidalCategory Y
  exact ⟨proper_tensor_coefficients_finiteDimensional f E V n m hE hV,
    proper_eulerCharacteristic_eq_h0_sub_h1 (X := Y) f hdim E,
    proper_eulerCharacteristic_eq_h0_sub_h1 (X := Y) f hdim V,
    proper_eulerCharacteristic_eq_h0_sub_h1 (X := Y) f hdim (E ⊗ V),
    proper_eulerCharacteristic_eq_h0_sub_h1 (X := Y) f hdim
      (_root_.SheafOfModules.unit Y.ringCatSheaf)⟩

end KltDP.AdmissionProbe.ProperFiniteRankCohomology
