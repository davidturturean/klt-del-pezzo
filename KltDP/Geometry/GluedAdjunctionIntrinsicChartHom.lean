import KltDP.Geometry.GluedAdjunctionIntrinsicChart

/-!
# The forward map of the original intrinsic adjunction chart

Normalize only the original composition and the two tensor whiskerings.
The source, local adjunction, ambient and normal comparisons remain their
already defined maps. This is the form used when pasting their original
restriction squares.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicChartHom

local instance intrinsicHomTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem normalized_word {C : Type*} [Category C] [MonoidalCategory C]
    {S T A B M N K : C} (s : S ≅ T) (a : T ≅ A ⊗ B)
    (β : B ≅ N) (α : A ≅ M) (t : K ≅ M ⊗ N) :
    ((s ≪≫ (a ≪≫ whiskerLeftIso A β)) ≪≫
      (whiskerRightIso α N ≪≫ t.symm)).hom =
      s.hom ≫ a.hom ≫ (α.hom ⊗ β.hom) ≫ t.inv := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    Category.assoc]
  rw [← Category.assoc (A ◁ β.hom) (α.hom ▷ N), ← tensorHom_def']

private def iso_hom_proof {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens)
    (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
    (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    normalized_word
      (GluedChartKaehlerPullback.iso f I U)
      (NormalTwistedAdjunctionTensorChart.iso R Γ(X, U.1) (I.ideal U)
        (gluedAffineIdealEquation I U d hU) hU.symm hd)
      (GluedConormalTildeDualChart.chartIso I hI U d hU hd)
      (GluedAdjunctionAmbientChart.iso f I U)
      (schemeModulePullbackTensorIso (I.glueData.ι U)
        (GluedAdjunctionAmbientChart.globalAmbientSheaf f I)
        (GluedConormalTildeDualChart.globalNormalSheaf I))

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
  (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens)
  (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

/-- The original intrinsic chart hom is its original source map, local adjunction map,
tensor of ambient and normal maps, then inverse pullback tensor comparison.
The transparent proposition unfolds precisely the original chart definitions. -/
theorem iso_hom :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)]
      [hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)],
      statementOf (iso_hom_proof f I hI U d hU hd hAmbient hCurve) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro hAmbient hCurve
  exact iso_hom_proof f I hI U d hU hd hAmbient hCurve

end KltDP.Geometry.GluedAdjunctionIntrinsicChartHom
