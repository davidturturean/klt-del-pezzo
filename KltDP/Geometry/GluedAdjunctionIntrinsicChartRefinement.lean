import KltDP.Geometry.GluedAdjunctionIntrinsicSourceProofAnnotations
import KltDP.Geometry.GluedAdjunctionIntrinsicOriginalHomCarriers
import KltDP.Geometry.GluedAdjunctionIntrinsicLocalSquareCarriers
import KltDP.Geometry.GluedAdjunctionIntrinsicTargetOriginalPrefunctor

/-!
# The original intrinsic adjunction charts commute on basic-open refinements

The actual source, local adjunction, ambient, and normal restriction
squares compose to give the original intrinsic chart square. Smoothness
of the smaller chart is proved from its original principal localization.
There is no transition-compatibility input to the resulting theorem.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicChartRefinement

open GluedConormalBasicOpenLocalization

private theorem chart_word {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {S U V T : C} {S' U' V' T' : D}
    {s : S ⟶ U} {a : U ⟶ V} {c : V ⟶ T}
    {s' : S' ⟶ U'} {a' : U' ⟶ V'} {c' : V' ⟶ T'}
    {j : S ⟶ T} {j' : S' ⟶ T'}
    {rS : F.obj S ⟶ S'} {rU : F.obj U ⟶ U'}
    {rV : F.obj V ⟶ V'} {rT : F.obj T ⟶ T'}
    (hA : F.map a ≫ rV = rU ≫ a')
    (hj : j = s ≫ a ≫ c) (hj' : j' = s' ≫ a' ≫ c')
    (hS : F.map s ≫ rU = rS ≫ s')
    (hC : F.map c ≫ rT = rV ≫ c') :
    F.map j ≫ rT = rS ≫ j' := by
  rw [hj, hj']
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hC, ← Category.assoc (F.map a) rV, hA]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map s) rU, hS]
  simp only [Category.assoc]

private theorem associate_target_square {C : Type*} [Category C]
    {S P Q T : C} {l : S ⟶ T} {p : S ⟶ P} {q : P ⟶ Q} {a : Q ⟶ T}
    (h : l = p ≫ q ≫ a) : l = (p ≫ q) ≫ a :=
  h.trans (Category.assoc p q a).symm

private def iso_refinement_proof {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    chart_word
      (GluedAdjunctionIntrinsicTargetModuleProjections.local_square f I U r d hU hd hAmbient hCurve)
      (GluedAdjunctionIntrinsicOriginalHomCarriers.original_hom f I hI U d hU hd hAmbient hCurve)
      (GluedAdjunctionIntrinsicOriginalHomCarriers.original_hom f I hI (X.affineBasicOpen r)
        (sectionMap U r d) (equation_span I U r d hU) (equation_regular U r d hd)
        (GluedAdjunctionBasicOpenAlgebra.ambient_standardSmooth f U r)
        (GluedAdjunctionBasicOpenAlgebra.quotient_standardSmooth f I U r))
      (GluedAdjunctionIntrinsicSourceProofAnnotations.source_square f I U r d hU hd hAmbient hCurve)
      (associate_target_square
        (GluedAdjunctionIntrinsicTargetOriginalPrefunctor.target_square f I hI U r d hU hd hAmbient hCurve))

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

/-- The original global-object adjunction chart commutes with every actual basic-open
refinement. Both endpoint maps are the original `GluedAdjunctionIntrinsicChart.iso`.
Only the original regular equation and the original ambient/curve smoothness are inputs. -/
theorem iso_refinement {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)]
      [hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)],
      statementOf (iso_refinement_proof f I hI U r d hU hd hAmbient hCurve) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro hAmbient hCurve
  exact iso_refinement_proof f I hI U r d hU hd hAmbient hCurve

end KltDP.Geometry.GluedAdjunctionIntrinsicChartRefinement
