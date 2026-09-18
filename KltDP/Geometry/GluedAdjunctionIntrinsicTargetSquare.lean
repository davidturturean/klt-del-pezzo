import KltDP.Geometry.GluedAdjunctionAmbientRefinement
import KltDP.Geometry.GluedAdjunctionChartComponentHoms
import KltDP.Geometry.GluedAdjunctionTensorRefinement

/-!
# The original ambient and normal target square on a principal chart

Feed the compiled original component equations directly to the compiled
tensor refinement theorem. Their native types determine every chart and
restriction arrow. Only the categorical component projection of an
isomorphism is normalized, before the original normal square is used.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicTargetSquare

private theorem normalize_app_homs {C D : Type*} [Category C] [Category D]
    {F G H : C ⥤ D} (e : F ≅ G) (e' : G ≅ H) (M : C)
    {S T : D} {a : S ⟶ F.obj M} {δ : S ⟶ T} {b : T ⟶ H.obj M}
    (h : a ≫ (e.app M).hom ≫ (e'.app M).hom = δ ≫ b) :
    a ≫ e.hom.app M ≫ e'.hom.app M = δ ≫ b := by
  simpa only [Iso.app_hom] using h

private def normal_component {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  normalize_app_homs
    (schemeModulePullbackCompIso (I.glueDataObjMap (X.affineBasicOpen_le r))
      (I.glueData.ι U))
    (eqToIso (congrArg schemeModulePullback
      (I.glueDataObjMap_ι (X.affineBasicOpen r) U (X.affineBasicOpen_le r))))
    (GluedConormalTildeDualChart.globalNormalSheaf I)
    (GluedAdjunctionChartComponentHoms.normal_refinement I hI U r d hU hd)

/-- The actual target factors commute with the original global-object refinement.
Every original ambient, normal, and tensor arrow is inferred from its proved equation. -/
def target_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  let _ : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  let _ : Algebra Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) :=
    GluedAdjunctionBasicOpenAlgebra.restrictionAlgebra U r
  let _ : IsScalarTower R Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) :=
    GluedAdjunctionBasicOpenAlgebra.restrictionTower f U r
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, (X.affineBasicOpen r).1) :=
      GluedAdjunctionBasicOpenAlgebra.ambient_standardSmooth f U r
    GluedAdjunctionTensorRefinement.target_refinement
      (I.glueDataObjMap (X.affineBasicOpen_le r))
      (I.glueData.ι U) (I.glueData.ι (X.affineBasicOpen r))
      (I.glueDataObjMap_ι (X.affineBasicOpen r) U (X.affineBasicOpen_le r))
      (GluedAdjunctionAmbientChart.globalAmbientSheaf f I)
      (GluedConormalTildeDualChart.globalNormalSheaf I)
      _ _ _ _ _ _
      (GluedAdjunctionAmbientRefinement.iso_refinement f I U r)
      (normal_component I hI U r d hU hd)

end KltDP.Geometry.GluedAdjunctionIntrinsicTargetSquare
