import KltDP.Geometry.SchemeKernelOpenPullback
import KltDP.Geometry.SchemeModulePullbackRestrict
import KltDP.Geometry.GluedConormalPullbackFrame

/-!
# Original conormal chart frames through their ambient kernel maps

The accepted conormal restriction is factored through the original
kernel comparison and the original pullback square. The existing global
quotient-chart frame is then expressed as pullback of its original
ambient-kernel equation. This permits actual kernel refinement equalities
to be used before pulling to the closed scheme.

All comparisons are the already defined maps. No conormal compatibility
or equality of frames is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemeConormalKernelPullback

open SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- The existing conormal restriction comparison, on the original pullback presentation. -/
def restrictionIso :
    (schemeModulePullback (f ⁻¹ᵁ U).ι).obj (schemeConormalSheaf f) ≅
      schemeConormalSheaf (f ∣_ U) :=
  ((restrictionIsoPullback (f ⁻¹ᵁ U).ι).app (schemeConormalSheaf f)).symm ≪≫
    schemeConormalRestrictionIso f U

/-- Its factorization uses the original kernel map and the actual pullback square. -/
theorem restrictionIso_factor :
    restrictionIso f U =
      (schemeModulePullbackRestrictIso f U).app (schemeKernelIdeal f) ≪≫
        (schemeModulePullback (f ∣_ U)).mapIso (localKernelToGlobalPullbackIso f U).symm := by
  let K := schemeKernelIdeal f
  let F := schemeModulePullback (f ∣_ U)
  let a := (restrictionIsoPullback (f ⁻¹ᵁ U).ι).app (schemeConormalSheaf f)
  let b := (schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f).app K
  let c := (eqToIso (congrArg schemeModulePullback (morphismRestrict_ι f U).symm)).app K
  let d := (schemeModulePullbackCompIso (f ∣_ U) U.ι).app K
  let e := (restrictionIsoPullback U.ι).app K
  let k := schemeKernelRestrictionIso f U
  apply Iso.ext
  change a.inv ≫ (a.hom ≫ b.hom ≫ c.hom ≫ d.inv ≫ F.map e.inv ≫ F.map k.hom) =
    (b.hom ≫ c.hom ≫ d.inv) ≫ F.map (e.inv ≫ k.hom)
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- An original local conormal equation is pullback of the original ambient-kernel equation. -/
theorem localEquation (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0) :
    schemeConormalGenerator (f ∣_ U) d hd ≫ (restrictionIso f U).inv =
      schemeModulePullbackFrame (f ∣_ U) (localKernelGlobalEquation f U d hd) ≫
        (schemeModulePullbackRestrictIso f U).inv.app (schemeKernelIdeal f) := by
  rw [restrictionIso_factor]
  change schemeModulePullbackFrame (f ∣_ U) (schemeKernelGenerator (f ∣_ U) d hd) ≫
      ((schemeModulePullback (f ∣_ U)).map (localKernelToGlobalPullbackIso f U).hom ≫
        (schemeModulePullbackRestrictIso f U).inv.app (schemeKernelIdeal f)) =
    schemeModulePullbackFrame (f ∣_ U)
      (schemeKernelGenerator (f ∣_ U) d hd ≫ (localKernelToGlobalPullbackIso f U).hom) ≫
        (schemeModulePullbackRestrictIso f U).inv.app (schemeKernelIdeal f)
  rw [schemeModulePullbackFrame_postcomp, Category.assoc]

section Chart

variable {Z : Scheme.{u}} (I : Z.IdealSheafData) (A : Z.affineOpens)

/-- The existing chart comparison is exactly pullback of the existing conormal restriction,
followed by the original chart inclusion equality. -/
theorem chartComparison_inv :
    (gluedAffineConormalChartComparisonIso I A).inv =
      (schemeModulePullback (I.glueDataObjIso A).hom).map
          (restrictionIso I.gluedTo A.1).inv ≫
        (schemeModulePullbackCompIso (I.glueDataObjIso A).hom
          (I.gluedTo ⁻¹ᵁ A.1).ι).hom.app (schemeConormalSheaf I.gluedTo) ≫
        (eqToIso (congrArg schemeModulePullback
          (I.glueDataObjIso_hom_ι A))).hom.app (schemeConormalSheaf I.gluedTo) := by
  let q := (I.glueDataObjIso A).hom
  let R := restriction q
  let F := schemeModulePullback q
  let C := schemeConormalSheaf I.gluedTo
  let e := schemeConormalRestrictionIso I.gluedTo A.1
  let a := restrictionIsoPullback q
  let b := (restrictionIsoPullback (I.gluedTo ⁻¹ᵁ A.1).ι).app C
  let c := (schemeModulePullbackCompIso q (I.gluedTo ⁻¹ᵁ A.1).ι).app C
  let t := (eqToIso (congrArg schemeModulePullback (I.glueDataObjIso_hom_ι A))).app C
  have hn : (a.app (schemeConormalSheaf (I.gluedTo ∣_ A.1))).inv ≫ R.map e.inv =
      F.map e.inv ≫ (a.app ((restriction (I.gluedTo ⁻¹ᵁ A.1).ι).obj C)).inv :=
    (a.inv.naturality e.inv).symm
  change ((a.app (schemeConormalSheaf (I.gluedTo ∣_ A.1))).inv ≫ R.map e.inv) ≫
      ((a.app ((restriction (I.gluedTo ⁻¹ᵁ A.1).ι).obj C)).hom ≫
        F.map b.hom ≫ c.hom ≫ t.hom) =
    F.map (e.inv ≫ b.hom) ≫ c.hom ≫ t.hom
  rw [hn]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

variable (d : Γ(Z, A.1)) (hI : I.ideal A = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(Z, A.1))

/-- The original global conormal chart frame is the original ambient-kernel equation
pulled through the existing square and the actual chart inclusion. -/
theorem chartFrame :
    (gluedAffineConormalChartFrameIso I A d hI hd).hom =
      schemeModulePullbackFrame (I.glueDataObjIso A).hom
        (schemeModulePullbackFrame (I.gluedTo ∣_ A.1)
            (localKernelGlobalEquation I.gluedTo A.1 (gluedAffineEquation A d)
              (gluedAffineEquation_eq_zero I A d hI)) ≫
          (schemeModulePullbackRestrictIso I.gluedTo A.1).inv.app
            (schemeKernelIdeal I.gluedTo)) ≫
        (schemeModulePullbackCompIso (I.glueDataObjIso A).hom
          (I.gluedTo ⁻¹ᵁ A.1).ι).hom.app (schemeConormalSheaf I.gluedTo) ≫
        (eqToIso (congrArg schemeModulePullback
          (I.glueDataObjIso_hom_ι A))).hom.app (schemeConormalSheaf I.gluedTo) := by
  calc
    _ = pulledConormalGenerator (I.gluedTo ∣_ A.1) (I.glueDataObjIso A).hom
        (gluedAffineEquation A d) (gluedAffineEquation_eq_zero I A d hI) ≫
        (gluedAffineConormalChartComparisonIso I A).inv := by
      rw [← gluedAffineConormalChartFrameIso_comparison I A d hI hd]
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = _ := by
      rw [chartComparison_inv]
      change schemeModulePullbackFrame (I.glueDataObjIso A).hom
          (schemeConormalGenerator (I.gluedTo ∣_ A.1) (gluedAffineEquation A d)
            (gluedAffineEquation_eq_zero I A d hI)) ≫
        (schemeModulePullback (I.glueDataObjIso A).hom).map
          (restrictionIso I.gluedTo A.1).inv ≫
        (schemeModulePullbackCompIso (I.glueDataObjIso A).hom
          (I.gluedTo ⁻¹ᵁ A.1).ι).hom.app (schemeConormalSheaf I.gluedTo) ≫
        (eqToIso (congrArg schemeModulePullback
          (I.glueDataObjIso_hom_ι A))).hom.app (schemeConormalSheaf I.gluedTo) = _
      rw [← Category.assoc
        (schemeModulePullbackFrame (I.glueDataObjIso A).hom
          (schemeConormalGenerator (I.gluedTo ∣_ A.1) (gluedAffineEquation A d)
            (gluedAffineEquation_eq_zero I A d hI)))
        ((schemeModulePullback (I.glueDataObjIso A).hom).map
          (restrictionIso I.gluedTo A.1).inv)]
      rw [← schemeModulePullbackFrame_postcomp, localEquation]

end Chart

end KltDP.Geometry.SchemeConormalKernelPullback
