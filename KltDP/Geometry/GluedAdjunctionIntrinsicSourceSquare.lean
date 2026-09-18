import KltDP.Geometry.GluedAdjunctionChartComponentHoms

/-!
# The original intrinsic source square in its native composition carrier

Associate the checked source equation and normalize the natural-isomorphism
component projection while the categories and objects are abstract. The
concrete definition then retains the original source maps without simp on
their differential sheaves or pullback functors.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicSourceSquare

private theorem associate_app_hom {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (η : F ≅ G) (M : C) {P Q : D}
    {a : G.obj M ⟶ P} {b : P ⟶ Q} {l : F.obj M ⟶ Q}
    (h : l = (η.app M).hom ≫ a ≫ b) :
    l = (η.hom.app M ≫ a) ≫ b := by
  simpa only [Iso.app_hom, Category.assoc] using h

/-- The checked original cotangent-source square with the literal original comparison component. -/
def source_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r : Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  let _ : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  associate_app_hom
    (schemeModulePullbackCompIso (I.glueDataObjMap (X.affineBasicOpen_le r))
      (I.glueData.ι U))
    (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f))
    (GluedAdjunctionChartComponentHoms.source_refinement f I U r)

end KltDP.Geometry.GluedAdjunctionIntrinsicSourceSquare
