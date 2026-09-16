import KltDP.Geometry.GluedConormalBasicOpenLocalization
import KltDP.Geometry.GluedConormalEquationIndependence
import KltDP.Geometry.SchemeKernelOpenPullback

/-!
# Original tilde equation frames on actual basic-open quotient charts

The compiled cotangent scalar-extension isomorphism preserves the original
principal coordinate. Its actual tilde pullback consequently preserves the
original equation frame, including the existing structure-unit comparison.
No global conormal comparison is used in this normalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.GluedConormalBasicOpenFrames

open GluedConormalBasicOpenLocalization GluedConormalEquationIndependence

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
  (r d : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

/-- The original basic-open cotangent isomorphism preserves the original principal coordinate. -/
theorem moduleIso_coordinate :
    (moduleIso I U r d hI hd).hom ≫
      (gluedAffineCotangentEquiv I (X.affineBasicOpen r) (sectionMap U r d)
        (equation_span I U r d hI) (equation_regular U r d hd)).symm.toModuleIso.hom =
    AffineModuleTildePullbackUnit.extendedCoordinate (quotientMap I U r)
      (gluedAffineCotangentEquiv I U d hI hd).symm.toModuleIso.hom := by
  let eU := (gluedAffineCotangentEquiv I U d hI hd).toModuleIso
  let eV := (gluedAffineCotangentEquiv I (X.affineBasicOpen r) (sectionMap U r d)
    (equation_span I U r d hI) (equation_regular U r d hd)).toModuleIso
  change ((ModuleCat.extendScalars (quotientMap I U r)).map eU.inv ≫
      (AffineModuleTildePullbackUnit.scalarUnitIso (quotientMap I U r)).hom ≫ eV.hom) ≫
      eV.inv =
    (ModuleCat.extendScalars (quotientMap I U r)).map eU.inv ≫
      (AffineModuleTildePullbackUnit.scalarUnitIso (quotientMap I U r)).hom
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual tilde scalar-extension map preserves that coordinate through the original unit. -/
theorem tildeRefinementIso_coordinate :
    (tildeRefinementIso I U r d hI hd).hom ≫
      (tildeFrame I (X.affineBasicOpen r) (sectionMap U r d)
        (equation_span I U r d hI) (equation_regular U r d hd)).inv =
    (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).map
        (tildeFrame I U d hI hd).inv ≫
      (schemeModulePullbackUnitIso (I.glueDataObjMap (X.affineBasicOpen_le r))).hom := by
  change ((AffineModuleTilde.pullbackIso (quotientMap I U r)
      (ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)).hom ≫
        AffineModuleTilde.map (moduleIso I U r d hI hd).hom) ≫
      (AffineModuleTilde.map
          (gluedAffineCotangentEquiv I (X.affineBasicOpen r) (sectionMap U r d)
            (equation_span I U r d hI) (equation_regular U r d hd)).symm.toModuleIso.hom ≫
        (AffineModuleTilde.unitIso
          (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))).hom) =
    (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).map
      (AffineModuleTilde.map (gluedAffineCotangentEquiv I U d hI hd).symm.toModuleIso.hom ≫
        (AffineModuleTilde.unitIso (Γ(X, U.1) ⧸ I.ideal U)).hom) ≫
      (schemeModulePullbackUnitIso (I.glueDataObjMap (X.affineBasicOpen_le r))).hom
  rw [Category.assoc, ← Category.assoc
    (AffineModuleTilde.map (moduleIso I U r d hI hd).hom)
    (AffineModuleTilde.map
      (gluedAffineCotangentEquiv I (X.affineBasicOpen r) (sectionMap U r d)
        (equation_span I U r d hI) (equation_regular U r d hd)).symm.toModuleIso.hom),
    ← AffineModuleTilde.map_comp, moduleIso_coordinate]
  exact AffineModuleTildePullbackUnit.pullback_coordinate (quotientMap I U r)
    (gluedAffineCotangentEquiv I U d hI hd).symm.toModuleIso.hom

/-- The original equation frame itself is retained by the actual basic-open tilde pullback. -/
theorem tildeFrame_refinement :
    schemeModulePullbackFrame (I.glueDataObjMap (X.affineBasicOpen_le r))
        (tildeFrame I U d hI hd).hom ≫
      (tildeRefinementIso I U r d hI hd).hom =
    (tildeFrame I (X.affineBasicOpen r) (sectionMap U r d)
      (equation_span I U r d hI) (equation_regular U r d hd)).hom := by
  apply (cancel_mono (tildeFrame I (X.affineBasicOpen r) (sectionMap U r d)
    (equation_span I U r d hI) (equation_regular U r d hd)).inv).mp
  rw [Category.assoc, tildeRefinementIso_coordinate, Iso.hom_inv_id]
  simp only [schemeModulePullbackFrame, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id]

end KltDP.Geometry.GluedConormalBasicOpenFrames
