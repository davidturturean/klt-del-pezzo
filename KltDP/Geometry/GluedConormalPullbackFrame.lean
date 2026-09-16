import KltDP.Geometry.GluedConormalTilde
import KltDP.Geometry.ConormalGeneratorPullback
import KltDP.Geometry.SchemeModuleUnitCoherence

/-!
# Original quotient-chart conormal frames under actual pullback

The original tilde comparison uses two successive open restrictions.
Here those restrictions are compared with pullback along the original
quotient-chart inclusion into the glued closed scheme. The resulting
frame is proved to be the actual pulled conormal equation map under the
canonical comparison with the restricted closed immersion.

The original chart inclusion, equation, and unit normalization are kept.
No frame agreement, transition equation, or global bundle comparison is
an input. Specialization to the Rees quotient charts and the two P1
charts, and their inter-chart transition, remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

open SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem restrictionUnitIso_inv_comparison {Y Z : Scheme.{u}}
    (g : Z ⟶ Y) [IsOpenImmersion g] :
    (restrictionUnitIso g).inv ≫
        (restrictionIsoPullback g).hom.app (_root_.SheafOfModules.unit Y.ringCatSheaf) =
      (schemeModulePullbackUnitIso g).inv := by
  apply (cancel_mono (schemeModulePullbackUnitIso g).hom).mp
  rw [Category.assoc, restrictionIsoPullback_unit, Iso.inv_hom_id, Iso.inv_hom_id]

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- The two original open restrictions identify with pullback along the
actual quotient-chart inclusion into the glued closed scheme. -/
def gluedAffineGlobalConormalPullbackIso :
    gluedAffineGlobalConormal I U ≅
      (schemeModulePullback (I.glueData.ι U)).obj (schemeConormalSheaf I.gluedTo) :=
  (restrictionIsoPullback (I.glueDataObjIso U).hom).app _ ≪≫
    (schemeModulePullback (I.glueDataObjIso U).hom).mapIso
      ((restrictionIsoPullback (I.gluedTo ⁻¹ᵁ U.1).ι).app _) ≪≫
    (schemeModulePullbackCompIso (I.glueDataObjIso U).hom
      (I.gluedTo ⁻¹ᵁ U.1).ι).app _ ≪≫
    (eqToIso (congrArg schemeModulePullback (I.glueDataObjIso_hom_ι U))).app _

/-- The same original restricted sheaf identifies with pullback of the
conormal of the actual restricted immersion along its quotient-chart iso. -/
def gluedAffineConormalLocalPullbackIso :
    gluedAffineGlobalConormal I U ≅
      (schemeModulePullback (I.glueDataObjIso U).hom).obj
        (schemeConormalSheaf (I.gluedTo ∣_ U.1)) :=
  (restriction (I.glueDataObjIso U).hom).mapIso
      (schemeConormalRestrictionIso I.gluedTo U.1) ≪≫
    (restrictionIsoPullback (I.glueDataObjIso U).hom).app _

/-- This comparison has the actual chart pullback of the global conormal
as source and the actual local-immersion pullback as target. -/
def gluedAffineConormalChartComparisonIso :
    (schemeModulePullback (I.glueData.ι U)).obj (schemeConormalSheaf I.gluedTo) ≅
      (schemeModulePullback (I.glueDataObjIso U).hom).obj
        (schemeConormalSheaf (I.gluedTo ∣_ U.1)) :=
  (gluedAffineGlobalConormalPullbackIso I U).symm ≪≫
    gluedAffineConormalLocalPullbackIso I U

variable (d : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {d})
  (hregular : d ∈ nonZeroDivisors Γ(X, U.1))

/-- The actual equation frame on the original quotient chart now lands
in the pullback along its original inclusion, without choosing a new basis. -/
def gluedAffineConormalChartFrameIso :
    _root_.SheafOfModules.unit (I.glueDataObj U).ringCatSheaf ≅
      (schemeModulePullback (I.glueData.ι U)).obj (schemeConormalSheaf I.gluedTo) :=
  gluedAffineGlobalConormalUnitIso I U d hI hregular ≪≫
    gluedAffineGlobalConormalPullbackIso I U

/-- Unit coherence and naturality identify the original restricted
frame with the actual pulled equation map, not an arbitrary trivialization. -/
theorem gluedAffineGlobalConormalUnitIso_localPullback :
    (gluedAffineGlobalConormalUnitIso I U d hI hregular).hom ≫
        (gluedAffineConormalLocalPullbackIso I U).hom =
      pulledConormalGenerator (I.gluedTo ∣_ U.1) (I.glueDataObjIso U).hom
        (gluedAffineEquation U d) (gluedAffineEquation_eq_zero I U d hI) := by
  change ((restrictionUnitIso (I.glueDataObjIso U).hom).inv ≫
      (restriction (I.glueDataObjIso U).hom).map
        ((gluedAffineConormalIso I U d hI hregular).hom ≫
          (schemeConormalRestrictionIso I.gluedTo U.1).inv)) ≫
      ((restriction (I.glueDataObjIso U).hom).map
          (schemeConormalRestrictionIso I.gluedTo U.1).hom ≫
        (restrictionIsoPullback (I.glueDataObjIso U).hom).hom.app
          (schemeConormalSheaf (I.gluedTo ∣_ U.1))) = _
  simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [(restrictionIsoPullback (I.glueDataObjIso U).hom).hom.naturality
    (gluedAffineConormalIso I U d hI hregular).hom]
  rw [← Category.assoc, restrictionUnitIso_inv_comparison]
  rfl

/-- The frame of the actual global chart pullback is the original pulled
equation map through the proved comparison. No such agreement is assumed. -/
theorem gluedAffineConormalChartFrameIso_comparison :
    (gluedAffineConormalChartFrameIso I U d hI hregular).hom ≫
        (gluedAffineConormalChartComparisonIso I U).hom =
      pulledConormalGenerator (I.gluedTo ∣_ U.1) (I.glueDataObjIso U).hom
        (gluedAffineEquation U d) (gluedAffineEquation_eq_zero I U d hI) := by
  simp only [gluedAffineConormalChartFrameIso, gluedAffineConormalChartComparisonIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact gluedAffineGlobalConormalUnitIso_localPullback I U d hI hregular

/-- The existing tilde comparison, with the actual chart pullback as
target rather than its two-step open-restriction presentation. -/
def gluedAffineConormalTildePullbackIso :
    (ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent).tilde ≅
      (schemeModulePullback (I.glueData.ι U)).obj (schemeConormalSheaf I.gluedTo) :=
  gluedAffineConormalTildeIso I U d hI hregular ≪≫
    gluedAffineGlobalConormalPullbackIso I U

/-- On every actual quotient-chart open the class of the original
equation maps to the original chart frame evaluated at the unit section. -/
theorem gluedAffineConormalTildePullbackIso_toOpen_equation
    (V : (I.glueDataObj U).Opens) :
    (gluedAffineConormalTildePullbackIso I U d hI hregular).hom.val.app (op V)
        (ModuleCat.Tilde.toOpen
          (ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent) V
          ((I.ideal U).toCotangent (gluedAffineIdealEquation I U d hI))) =
      (gluedAffineConormalChartFrameIso I U d hI hregular).hom.val.app (op V)
        (1 : Γ(I.glueDataObj U, V)) := by
  change (gluedAffineGlobalConormalPullbackIso I U).hom.val.app (op V)
      ((gluedAffineConormalTildeIso I U d hI hregular).hom.val.app (op V)
        (ModuleCat.Tilde.toOpen
          (ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent) V
          ((I.ideal U).toCotangent (gluedAffineIdealEquation I U d hI)))) =
    (gluedAffineGlobalConormalPullbackIso I U).hom.val.app (op V)
      ((gluedAffineGlobalConormalUnitIso I U d hI hregular).hom.val.app (op V)
        (1 : Γ(I.glueDataObj U, V)))
  rw [gluedAffineConormalTildeIso_toOpen_equation]

end KltDP.Geometry
