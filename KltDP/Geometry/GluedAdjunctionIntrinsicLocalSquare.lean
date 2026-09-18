import KltDP.Geometry.GluedAdjunctionBasicOpenAlgebra
import KltDP.Geometry.NormalTwistedAdjunctionTensorChartRestriction

/-!
# The original local adjunction square on an actual principal chart

Retain the native equation of the compiled tensor-chart restriction. The
only replacement folds its two expanded chart homs back to the original
named isomorphisms. All intervening restriction maps remain the original
maps of that compiled equation, with their inferred module carriers.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicLocalSquare

open GluedConormalBasicOpenLocalization

private theorem replace_chart_maps {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {S T : C} {S' T' : D}
    {a₀ a : S ⟶ T} {a₀' a' : S' ⟶ T'}
    (ha : a₀ = a) (ha' : a₀' = a')
    {s : F.obj S ⟶ S'} {t : F.obj T ⟶ T'}
    (h : F.map a₀ ≫ t = s ≫ a₀') : F.map a ≫ t = s ≫ a' := by
  cases ha
  cases ha'
  exact h

private def tensor_chart_hom (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (J : Ideal A)
    [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]
    (d : J) (hJ : Ideal.span {(d : A)} = J)
    (hd : (d : A) ∈ nonZeroDivisors A) := by
  have h := Eq.refl ((NormalTwistedAdjunctionTensorChart.iso R A J d hJ hd).hom)
  conv at h =>
    lhs
    unfold NormalTwistedAdjunctionTensorChart.iso
    simp only [Iso.trans_hom]
  exact h

/-- The original named local adjunction maps satisfy the original native
restriction square. Only smoothness of the larger original chart is an input. -/
def local_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  let _ : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  let _ : Algebra Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) :=
    GluedAdjunctionBasicOpenAlgebra.restrictionAlgebra U r
  let _ : IsScalarTower R Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) :=
    GluedAdjunctionBasicOpenAlgebra.restrictionTower f U r
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, (X.affineBasicOpen r).1) :=
      GluedAdjunctionBasicOpenAlgebra.ambient_standardSmooth f U r
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R
        (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r)) :=
      GluedAdjunctionBasicOpenAlgebra.quotient_standardSmooth f I U r
    let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (KltDP.RingTheory.SmoothPrincipalDeterminantRestriction.quotientMap
          Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) (I.ideal U)
          (I.ideal (X.affineBasicOpen r))
          (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))))) := by
      change IsOpenImmersion (I.glueDataObjMap (X.affineBasicOpen_le r))
      infer_instance
    replace_chart_maps (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r)))
      (tensor_chart_hom R Γ(X, U.1) (I.ideal U)
        (gluedAffineIdealEquation I U d hU) hU.symm hd)
      (tensor_chart_hom R Γ(X, (X.affineBasicOpen r).1) (I.ideal (X.affineBasicOpen r))
        (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
          (equation_span I U r d hU))
        (equation_span I U r d hU).symm (equation_regular U r d hd))
      (NormalTwistedAdjunctionTensorChartRestriction.iso_restriction R
        Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) (I.ideal U)
        (I.ideal (X.affineBasicOpen r)) (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))
        (gluedAffineIdealEquation I U d hU) hU.symm hd
        (equation_span I U r d hU).symm (equation_regular U r d hd))

end KltDP.Geometry.GluedAdjunctionIntrinsicLocalSquare
