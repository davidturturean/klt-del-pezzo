import KltDP.Geometry.GluedChartKaehlerRefinement
import KltDP.Geometry.GluedConormalNormalRefinement
import KltDP.Geometry.GluedConormalNormalSemilinear

/-!
# The original source and normal refinement equations as morphisms

The existing chart isomorphism equalities give the source and normal
morphism squares used in intrinsic adjunction. The normal transition is
identified with the already proved original semilinear normal restriction.
No chart compatibility or smoothness witness is added.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionChartComponentHoms

open GluedConormalBasicOpenLocalization

private theorem source_word {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {S T : C} {P S' T' : D}
    (s : S ≅ T) (k : F.obj T ≅ T') (c : F.obj S ≅ P)
    (e : P ≅ S') (s' : S' ≅ T')
    (h : F.mapIso s ≪≫ k = c ≪≫ e ≪≫ s') :
    F.map s.hom ≫ k.hom = c.hom ≫ e.hom ≫ s'.hom := by
  simpa only [CategoryTheory.Functor.mapIso_hom, Iso.trans_hom, Category.assoc] using
    congrArg (fun z => z.hom) h

private theorem normal_word {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {S T : C} {P S' T' : D}
    (s : S ≅ T) (c : F.obj T ≅ P) (e : P ≅ T')
    (n : F.obj S ≅ S') (s' : S' ≅ T') (γ : F.obj S ⟶ S')
    (h : F.mapIso s ≪≫ c ≪≫ e = n ≪≫ s') (hn : n.hom = γ) :
    F.map s.hom ≫ c.hom ≫ e.hom = γ ≫ s'.hom := by
  simpa only [CategoryTheory.Functor.mapIso_hom, Iso.trans_hom, Category.assoc, hn] using
    congrArg (fun z => z.hom) h

private def source_refinement_proof {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r : Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  let _ : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  source_word (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r)))
    (GluedChartKaehlerPullback.iso f I U)
    (GluedChartKaehlerRefinement.refinementIso f I U r)
    ((schemeModulePullbackCompIso (I.glueDataObjMap (X.affineBasicOpen_le r))
      (I.glueData.ι U)).app (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)))
    (eqToIso (congrArg
      (fun a => (schemeModulePullback a).obj (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)))
      (I.glueDataObjMap_ι (X.affineBasicOpen r) U (X.affineBasicOpen_le r))))
    (GluedChartKaehlerPullback.iso f I (X.affineBasicOpen r))
    (GluedChartKaehlerRefinement.iso_refinement f I U r)

private def normal_refinement_proof {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  normal_word (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r)))
    (GluedConormalTildeDualChart.chartIso I hI U d hU hd)
    ((schemeModulePullbackCompIso (I.glueDataObjMap (X.affineBasicOpen_le r))
      (I.glueData.ι U)).app (GluedConormalTildeDualChart.globalNormalSheaf I))
    ((eqToIso (congrArg schemeModulePullback
      (I.glueDataObjMap_ι (X.affineBasicOpen r) U (X.affineBasicOpen_le r)))).app
      (GluedConormalTildeDualChart.globalNormalSheaf I))
    (GluedConormalBasicOpenNormal.normalTildeRefinementIso I U r d hU hd)
    (GluedConormalTildeDualChart.chartIso I hI (X.affineBasicOpen r) (sectionMap U r d)
      (equation_span I U r d hU) (equation_regular U r d hd))
    (AffineModuleTildeSemilinearMap.pullbackMap (quotientMap I U r)
      (GluedConormalNormalSemilinear.nativeNormalMap I U r d hU hd))
    (GluedConormalNormalRefinement.chartIso_refinement I hI U r d hU hd)
    (GluedConormalNormalSemilinear.normalTildeRefinementIso_hom_eq I U r d hU hd)

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

/-- The original global differential chart and its actual native restriction commute. -/
theorem source_refinement {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r : Γ(X, U.1)) :
    statementOf (source_refinement_proof f I U r) :=
  source_refinement_proof f I U r

/-- The original global normal chart commutes with the actual native semilinear restriction. -/
theorem normal_refinement {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :
    statementOf (normal_refinement_proof I hI U r d hU hd) :=
  normal_refinement_proof I hI U r d hU hd

end KltDP.Geometry.GluedAdjunctionChartComponentHoms
