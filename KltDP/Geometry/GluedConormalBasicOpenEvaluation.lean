import KltDP.Geometry.GluedConormalBasicOpenFrames
import KltDP.Geometry.GluedConormalBasicOpenNormal
import KltDP.Geometry.PrincipalConormalTildeEvaluation
import KltDP.Geometry.SchemeModulePullbackTensorMultiplication

/-!
# Original conormal evaluation on actual basic-open quotient charts

The existing conormal and normal scalar-extension maps preserve the
original principal coordinates. Their actual tilde pullback isomorphisms
therefore preserve the original evaluation through the original scheme
tensor and unit comparisons. The quotient rings and chart map are the
ones in the ideal-sheaf gluing, without replacement by a model localization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.GluedConormalBasicOpenEvaluation

open GluedConormalBasicOpenLocalization GluedConormalBasicOpenNormal
  PrincipalConormalTildeEvaluation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
  (r d : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

private abbrev sourceNormalCoframe :=
  normalCoframe (I.ideal U) (gluedAffineIdealEquation I U d hI) hI.symm hd

private abbrev targetNormalCoframe :=
  normalCoframe (I.ideal (X.affineBasicOpen r))
    (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
      (equation_span I U r d hI))
    (equation_span I U r d hI).symm (equation_regular U r d hd)

/-- The actual normal scalar extension preserves its original dual coordinate. -/
theorem normalModuleIso_coordinate :
    (normalModuleIso I U r d hI hd).hom ≫ (targetNormalCoframe I U r d hI hd).hom =
      AffineModuleTildePullbackUnit.extendedCoordinate
        (quotientMap I U r) (sourceNormalCoframe I U d hI hd).hom := by
  change ((ModuleCat.extendScalars (quotientMap I U r)).map
      (sourceNormalCoframe I U d hI hd).hom ≫
      (AffineModuleTildePullbackUnit.scalarUnitIso (quotientMap I U r)).hom ≫
      (targetNormalCoframe I U r d hI hd).inv) ≫
        (targetNormalCoframe I U r d hI hd).hom =
    (ModuleCat.extendScalars (quotientMap I U r)).map
      (sourceNormalCoframe I U d hI hd).hom ≫
      (AffineModuleTildePullbackUnit.scalarUnitIso (quotientMap I U r)).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The original conormal coordinate is preserved through the actual basic-open pullback. -/
theorem conormalTildeRefinementIso_coordinate :
    (tildeRefinementIso I U r d hI hd).hom ≫
        conormalCoordinate (I.ideal (X.affineBasicOpen r))
          (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
            (equation_span I U r d hI))
          (equation_span I U r d hI).symm (equation_regular U r d hd) =
      (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).map
          (conormalCoordinate (I.ideal U) (gluedAffineIdealEquation I U d hI) hI.symm hd) ≫
        (schemeModulePullbackUnitIso (I.glueDataObjMap (X.affineBasicOpen_le r))).hom :=
  GluedConormalBasicOpenFrames.tildeRefinementIso_coordinate I U r d hI hd

/-- The original normal coordinate has the same actual pullback-unit normalization. -/
theorem normalTildeRefinementIso_coordinate :
    (normalTildeRefinementIso I U r d hI hd).hom ≫
        normalCoordinate (I.ideal (X.affineBasicOpen r))
          (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
            (equation_span I U r d hI))
          (equation_span I U r d hI).symm (equation_regular U r d hd) =
      (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).map
          (normalCoordinate (I.ideal U) (gluedAffineIdealEquation I U d hI) hI.symm hd) ≫
        (schemeModulePullbackUnitIso (I.glueDataObjMap (X.affineBasicOpen_le r))).hom := by
  change ((AffineModuleTilde.pullbackIso (quotientMap I U r)
      (PrincipalConormalTildeDual.normalModule (I.ideal U))).hom ≫
      AffineModuleTilde.map (normalModuleIso I U r d hI hd).hom) ≫
    (AffineModuleTilde.map (targetNormalCoframe I U r d hI hd).hom ≫
      (AffineModuleTilde.unitIso
        (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))).hom) = _
  rw [Category.assoc, ← Category.assoc
    (AffineModuleTilde.map (normalModuleIso I U r d hI hd).hom)
    (AffineModuleTilde.map (targetNormalCoframe I U r d hI hd).hom),
    ← AffineModuleTilde.map_comp, normalModuleIso_coordinate]
  exact AffineModuleTildePullbackUnit.pullback_coordinate
    (quotientMap I U r) (sourceNormalCoframe I U d hI hd).hom

/-- The original evaluation commutes with the actual basic-open quotient-chart
restriction, including the original scheme tensor and unit comparisons. -/
theorem tensor_evaluation :
    (tensorIso (tildeRefinementIso I U r d hI hd)
      (normalTildeRefinementIso I U r d hI hd)).hom ≫
        (PrincipalConormalTildeDual.transportedEvaluationIso (I.ideal (X.affineBasicOpen r))
          (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
            (equation_span I U r d hI))
          (equation_span I U r d hI).symm (equation_regular U r d hd)).hom =
      (schemeModulePullbackTensorIso (I.glueDataObjMap (X.affineBasicOpen_le r))
        (PrincipalConormalTildeDual.conormalModule (I.ideal U)).tilde
        (PrincipalConormalTildeDual.normalModule (I.ideal U)).tilde).inv ≫
      (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).map
        (PrincipalConormalTildeDual.transportedEvaluationIso (I.ideal U)
          (gluedAffineIdealEquation I U d hI) hI.symm hd).hom ≫
      (schemeModulePullbackUnitIso (I.glueDataObjMap (X.affineBasicOpen_le r))).hom := by
  apply (cancel_epi (schemeModulePullbackTensorIso
    (I.glueDataObjMap (X.affineBasicOpen_le r))
    (PrincipalConormalTildeDual.conormalModule (I.ideal U)).tilde
    (PrincipalConormalTildeDual.normalModule (I.ideal U)).tilde).hom).mp
  rw [Iso.hom_inv_id_assoc, transportedEvaluation_product, transportedEvaluation_product]
  simp only [tensorIso_hom, Category.assoc]
  rw [← tensor_comp_assoc, conormalTildeRefinementIso_coordinate,
    normalTildeRefinementIso_coordinate]
  exact schemeModulePullbackTensorIso_product
    (I.glueDataObjMap (X.affineBasicOpen_le r))
    (conormalCoordinate (I.ideal U) (gluedAffineIdealEquation I U d hI) hI.symm hd)
    (normalCoordinate (I.ideal U) (gluedAffineIdealEquation I U d hI) hI.symm hd)

end KltDP.Geometry.GluedConormalBasicOpenEvaluation
