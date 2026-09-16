import KltDP.Geometry.SchematicImageGlued

/-!
# Lifting a morphism through a glued closed subscheme

The accepted `SchematicImageGlued.toImage f` factors `f : X ⟶ Y` through the glued closed subscheme of
its own kernel `f.ker`. The same construction (pinned `Scheme.Hom.liftQuotient` on the affine pieces of
the pulled-back cover, glued by `Scheme.Cover.glueMorphisms`) works for every ideal sheaf `I ≤ f.ker`:
`liftGlued I f hI : X ⟶ I.glueData.glued` with `liftGlued I f hI ≫ I.gluedTo = f`
(`liftGlued_gluedTo`). The accepted module is reproduced with `f.ker` replaced by `I`; the only new
step is `I.ideal U ≤ f.ker.ideal U`, from the pointwise order on ideal sheaves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.GluedIdealSheafLift

variable {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (hI : I ≤ f.ker)

private abbrev sourceCover : X.OpenCover :=
  (Y.openCoverOfISupEqTop (fun U : Y.affineOpens => U.1)
    (iSup_affineOpens_eq_top Y)).pullbackCover f

include hI

private lemma ideal_le_ker_affinePullback (U : Y.affineOpens) :
    I.ideal U ≤ RingHom.ker ((Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫
      (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).appTop).hom := by
  let e : Γ(X, f ⁻¹ᵁ U.1) ≅ Γ(pullback f U.1.ι, ⊤) :=
    X.presheaf.mapIso (eqToIso (by
      simp only [Scheme.Hom.image_top_eq_opensRange,
        IsOpenImmersion.opensRange_pullback_fst_of_right, Scheme.Opens.opensRange_ι])).op
      ≪≫ (pullback.fst f U.1.ι).appIso ⊤
  have he : f.app U.1 ≫ e.hom =
      (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫
        (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).appTop := by
    rw [← (Iso.inv_comp_eq _).mpr U.2.isoSpec_inv_appTop,
      Category.assoc, Iso.eq_inv_comp]
    simp only [Scheme.Opens.topIso_hom, eqToHom_op, Scheme.Hom.app_eq_appLE,
      Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      Scheme.Hom.appIso_hom', Scheme.Hom.appLE_map, Scheme.Hom.map_appLE,
      Scheme.appLE_comp_appLE, Opens.map_top, e, pullback.condition,
      IsAffineOpen.toSpecΓ_isoSpec_inv, Category.assoc]
    rw [Scheme.comp_appLE, Scheme.Opens.ι_app]
    exact Scheme.Hom.map_appLE _ _ (homOfLE le_top).op
  rw [← he]
  refine ((hI U).trans (Scheme.IdealSheafData.ideal_ofIdeals_le _ _)).trans_eq
    (RingHom.ker_equiv_comp _ e.commRingCatIsoToRingEquiv).symm

private def affineToGlued (U : Y.affineOpens) : pullback f U.1.ι ⟶ I.glueData.glued :=
  (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).liftQuotient (I.ideal U)
    (ideal_le_ker_affinePullback I f hI U) ≫ I.glueData.ι U

@[reassoc]
private theorem affineToGlued_gluedTo (U : Y.affineOpens) :
    affineToGlued I f hI U ≫ I.gluedTo = pullback.fst f U.1.ι ≫ f := by
  simp only [affineToGlued, Category.assoc,
    Scheme.IdealSheafData.ι_gluedTo, Scheme.IdealSheafData.glueDataObjι,
    Scheme.Hom.liftQuotient_comp_assoc,
    IsAffineOpen.toSpecΓ_isoSpec_inv_assoc, pullback.condition]

/-- **A morphism whose kernel contains `I` factors through the glued closed subscheme of `I`.** -/
def liftGlued : X ⟶ I.glueData.glued :=
  (sourceCover f).glueMorphisms (affineToGlued I f hI) (by
    intro U V
    rw [← cancel_mono I.gluedTo]
    simp only [Category.assoc, affineToGlued_gluedTo]
    exact pullback.condition_assoc
      (f := pullback.fst f U.1.ι) (g := pullback.fst f V.1.ι) f)

@[reassoc]
theorem liftGlued_gluedTo : liftGlued I f hI ≫ I.gluedTo = f := by
  apply (sourceCover f).hom_ext
  intro U
  simpa only [liftGlued, Scheme.Cover.ι_glueMorphisms_assoc] using
    affineToGlued_gluedTo I f hI U

end KltDP.Geometry.GluedIdealSheafLift
