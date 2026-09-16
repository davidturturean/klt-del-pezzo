/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

Adapted from Mathlib commit 5aedf732b6987e8c26ab3c9ebc855314f82b045f,
Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean, lines 667-705.
The target here is the quotient-chart gluing already present at the pin,
with its actual closed inclusion supplied by PrimeCurveSubscheme.
-/
import KltDP.Geometry.PrimeCurveSubscheme

/-!
# Factorization through the glued scheme-theoretic image

For an actual morphism `f`, the image is the quotient-chart scheme glued
from the actual ideal sheaf `f.ker`. On the pullback of each affine open
of the target, the section map kills this ideal and therefore lifts to
the quotient chart. These lifts agree after the closed inclusion, hence
agree themselves and glue to a morphism from the original source.

No quasi-compactness hypothesis is needed for this factorization. Claims
about the topological closure of the image require separate hypotheses.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.SchematicImageGlued

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual quotient-chart gluing of the kernel ideal sheaf. -/
abbrev image : Scheme.{u} := f.ker.glueData.glued

/-- Its actual closed inclusion into the original target. -/
abbrev inclusion : image f ⟶ Y := f.ker.gluedTo

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion f) :=
  f.ker.gluedTo_isClosedImmersion

private lemma ideal_ker_le_ker_affinePullback (U : Y.affineOpens) :
    f.ker.ideal U ≤ RingHom.ker ((Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫
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
  refine (Scheme.IdealSheafData.ideal_ofIdeals_le _ _).trans_eq
    (RingHom.ker_equiv_comp _ e.commRingCatIsoToRingEquiv).symm

private abbrev sourceCover : X.OpenCover :=
  (Y.openCoverOfISupEqTop (fun U : Y.affineOpens => U.1)
    (iSup_affineOpens_eq_top Y)).pullbackCover f

private def affineToImage (U : Y.affineOpens) : pullback f U.1.ι ⟶ image f :=
  (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).liftQuotient (f.ker.ideal U)
    (ideal_ker_le_ker_affinePullback f U) ≫ f.ker.glueData.ι U

@[reassoc]
private theorem affineToImage_inclusion (U : Y.affineOpens) :
    affineToImage f U ≫ inclusion f = pullback.fst f U.1.ι ≫ f := by
  simp only [affineToImage, inclusion, Category.assoc,
    Scheme.IdealSheafData.ι_gluedTo, Scheme.IdealSheafData.glueDataObjι,
    Scheme.Hom.liftQuotient_comp_assoc,
    IsAffineOpen.toSpecΓ_isoSpec_inv_assoc, pullback.condition]

/-- The actual morphism from the source to the glued kernel subscheme. -/
def toImage : X ⟶ image f :=
  (sourceCover f).glueMorphisms (affineToImage f) (by
    intro U V
    rw [← cancel_mono (inclusion f)]
    simp only [Category.assoc, affineToImage_inclusion]
    exact pullback.condition_assoc
      (f := pullback.fst f U.1.ι) (g := pullback.fst f V.1.ι) f)

/-- The glued morphism factors the original morphism through its actual
closed image inclusion. -/
@[reassoc]
theorem toImage_inclusion : toImage f ≫ inclusion f = f := by
  apply (sourceCover f).hom_ext
  intro U
  simpa only [toImage, Scheme.Cover.ι_glueMorphisms_assoc] using
    affineToImage_inclusion f U

end KltDP.Geometry.SchematicImageGlued
