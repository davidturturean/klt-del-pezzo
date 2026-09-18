import KltDP.Geometry.ProjectiveProductCanonicalLocalDifferentials
import KltDP.Geometry.ProjectiveProductCanonicalSecondMapEquality
import KltDP.Geometry.AffineProductKaehlerComparison
import KltDP.Geometry.SchemeModuleOpenLocality
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The original named comparison on an original tensor chart

The global map is the categorical sum of the original projection maps.
Its restriction to each original tensor chart is the original affine
product comparison, through the proved factor and target isomorphisms.
This focused producer checks the named-chart handoff before global locality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalNamedChart

open SchemeKaehlerSheaf SchemeKaehlerPullbackMap
open KltDP.Examples.FrobeniusProjectivePoints
open ProjectiveProductCanonicalDifferentials ProjectiveProductCanonicalLocalDifferentials

private theorem mapped_biprod_square
    {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {A B T : C} [HasBinaryBiproduct A B]
    [HasBinaryBiproduct (F.obj A) (F.obj B)] [PreservesBinaryBiproduct A B F]
    {A' B' T' : D} [HasBinaryBiproduct A' B']
    (f : A ⟶ T) (g : B ⟶ T)
    (eA : F.obj A ≅ A') (eB : F.obj B ≅ B') (eT : F.obj T ≅ T')
    (a : A' ⟶ T') (b : B' ⟶ T')
    (ha : eA.hom ≫ a = F.map f ≫ eT.hom)
    (hb : eB.hom ≫ b = F.map g ≫ eT.hom) :
    (F.mapBiprod A B).hom ≫ (biprod.mapIso eA eB).hom ≫ biprod.desc a b =
      F.map (biprod.desc f g) ≫ eT.hom := by
  have hs : (biprod.mapIso eA eB).hom ≫ biprod.desc a b =
      biprod.desc (F.map f) (F.map g) ≫ eT.hom := by
    apply biprod.hom_ext'
    · simpa only [biprod.mapIso_hom, Category.assoc,
        biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc] using ha
    · simpa only [biprod.mapIso_hom, Category.assoc,
        biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc] using hb
  rw [hs, ← Category.assoc, biprod.mapBiprod_hom_desc]

/-- Infer the actual objects and component maps from the compiled squares.
The conclusion uses their original categorical sum, with no extra defining
sum equality or independently reconstructed biproduct dictionary. -/
private theorem mapped_biprod_isIso
    {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {A B T : C} [HasBinaryBiproduct A B]
    [HasBinaryBiproduct (F.obj A) (F.obj B)] [PreservesBinaryBiproduct A B F]
    {A' B' T' : D} [HasBinaryBiproduct A' B']
    {f : A ⟶ T} {g : B ⟶ T}
    {eA : F.obj A ≅ A'} {eB : F.obj B ≅ B'} {eT : F.obj T ≅ T'}
    {a : A' ⟶ T'} {b : B' ⟶ T'}
    (hb : eB.hom ≫ b = F.map g ≫ eT.hom)
    (ha : eA.hom ≫ a = F.map f ≫ eT.hom)
    (hi : IsIso (biprod.desc a b)) : IsIso (F.map (biprod.desc f g)) := by
  letI : IsIso (biprod.desc a b) := hi
  have h := mapped_biprod_square F f g eA eB eT a b ha hb
  letI : IsIso (F.map (biprod.desc f g) ≫ eT.hom) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right (F.map (biprod.desc f g)) eT.hom

/-- Infer both original maps from their already checked equality. -/
private theorem isIso_map_of_original_eq
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {M N : C} {a b : M ⟶ N} (ha : IsIso (F.map a))
    (h : a = b) : IsIso (F.map b) := by
  cases h
  exact ha

/-- Recover a sum map from its two already checked original components. -/
private theorem desc_eq_of_components
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B T : C} [HasBinaryBiproduct A B]
    {f : A ⟶ T} {g : B ⟶ T} {s : A ⊞ B ⟶ T}
    (hf : biprod.inl ≫ s = f) (hg : biprod.inr ≫ s = g) :
    biprod.desc f g = s := by
  apply biprod.hom_ext'
  · exact (biprod.inl_desc f g).trans hf.symm
  · exact (biprod.inr_desc f g).trans hg.symm

local instance open_pullback_preservesZero
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    (schemeModulePullback j).PreservesZeroMorphisms :=
  schemeModulePullback_open_preservesZeroMorphisms j

private theorem pullback_preservesBinaryBiproducts
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    PreservesBinaryBiproducts (schemeModulePullback j) := by
  letI : (schemeModulePullback j).IsLeftAdjoint :=
    ⟨⟨schemeModulePushforward j, ⟨schemeModulePullbackPushforwardAdjunction j⟩⟩⟩
  exact preservesBinaryBiproducts_of_preservesBinaryCoproducts (schemeModulePullback j)

variable (k : Type u) [Field k]

/- The bounded native comparison in math351 found only these aliases in
these two compiled squares. Normalize them once, before the categorical
application, preserving the original projection maps and base transports. -/
private def first_square_native (i j : Fin 2) := by
  have h := firstFactorIso_differential k i j
  dsimp only [firstFactorIso, differentialIso, lineBase, tensorBase,
    ProjectiveProductCanonicalTensorCharts.chartRing] at h
  exact h

private def second_square_native (i j : Fin 2) := by
  have h := secondFactorIso_differential k i j
  dsimp only [lineBase, tensorBase,
    ProjectiveProductCanonicalTensorCharts.chartRing] at h
  exact h

private def comparison_isIso_on_chart_proof (i j : Fin 2) :=
  let F := schemeModulePullback (ProjectiveProductCanonicalTensorCharts.chart k i j)
  letI : PreservesBinaryBiproducts F := pullback_preservesBinaryBiproducts
    (ProjectiveProductCanonicalTensorCharts.chart k i j)
  mapped_biprod_isIso F
    (second_square_native k i j) (first_square_native k i j)
    (AffineProductKaehler.originalComparison_isIso k (Polynomial k) (Polynomial k))

private abbrev statementOf {P : Prop} (_proof : P) : Prop := P

/-- The pullback of the original global map is invertible on every original tensor chart.
The transparent proposition retains the actual sum of the two original projection maps;
its only difference from the named `comparison` is the measured definitional expansion. -/
theorem comparison_isIso_on_chart (i j : Fin 2) :
    statementOf (comparison_isIso_on_chart_proof k i j) :=
  comparison_isIso_on_chart_proof k i j

private def original_sum_eq_for_transport :=
  fun h => desc_eq_of_components (inl_comparison k)
    ((inr_comparison k).trans
      (ProjectiveProductCanonicalSecondMapEquality.original_second_map_eq_for_transport k h).symm)

private def original_sum_eq_native := by
  have h := original_sum_eq_for_transport k
  dsimp only [firstFactor, secondFactor] at h
  exact h

private def named_chart_proof (i j : Fin 2) :=
  isIso_map_of_original_eq (comparison_isIso_on_chart_proof k i j)
    (original_sum_eq_native k _)

/-- The pullback of the original named `comparison k` on the original tensor
chart is an isomorphism. Every map and transport proof is derived above;
there is no additional geometric or isomorphism hypothesis. -/
theorem named_chart_isIso (i j : Fin 2) :
    statementOf (named_chart_proof k i j) :=
  named_chart_proof k i j

end KltDP.Geometry.ProjectiveProductCanonicalNamedChart
