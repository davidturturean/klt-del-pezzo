import KltDP.Geometry.GluedAdjunctionBasisSectionComponents
import KltDP.Geometry.GluedAdjunctionRefinedSectionSquare

/-!
# Actual adjunction section components agree under original principal refinement

The original intrinsic refinement square is evaluated through the original
open section equivalences. Equality of the original chart inclusion with
the composite inclusion is eliminated before any section-map calculation.
The resulting statement compares the actual basis components on every
original subopen of the smaller chart.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionBasisSectionRefinement

open GluedAdjunctionChartBasis

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
  (hI : IdealLocallyPrincipalRegular I)

/-- The actual original section components agree on every subopen of an actual basic refinement. -/
theorem hom_basicOpen (c : Chart f I) (r : Γ(X, c.U.1))
    (W : I.glueData.glued.Opens) (hW : W ≤ (c.basicOpen r).sourceOpen) :
    GluedAdjunctionBasisSectionComponents.hom f I hI (c.basicOpen r) W hW =
      GluedAdjunctionBasisSectionComponents.hom f I hI c W (hW.trans (c.basicOpen_le r)) := by
  letI : Algebra k Γ(X, c.U.1) := GluedChartKaehlerPullback.chartAlgebra f c.U
  letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, c.U.1) := c.ambient
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Γ(X, c.U.1) ⧸ I.ideal c.U) := c.curve
  apply GluedAdjunctionRefinedSectionSquare.hom_eq_of_refined (I.glueData.ι c.U) (I.glueDataObjMap (X.affineBasicOpen_le r))
    (I.glueData.ι (X.affineBasicOpen r))
    (I.glueDataObjMap_ι (X.affineBasicOpen r) c.U (X.affineBasicOpen_le r))
    (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f))
    (GluedAdjunctionIntrinsicChart.targetSheaf f I) W
    (GluedAdjunctionBasisSectionComponents.image_preimage f I c W (hW.trans (c.basicOpen_le r)))
    (GluedAdjunctionBasisSectionComponents.image_preimage f I (c.basicOpen r) W hW)
    (GluedAdjunctionCommonRefinement.iso f I hI c).hom
    (GluedAdjunctionCommonRefinement.iso f I hI (c.basicOpen r)).hom
  exact GluedAdjunctionCommonRefinement.refinedHom_eq f I hI c r

end KltDP.Geometry.GluedAdjunctionBasisSectionRefinement
