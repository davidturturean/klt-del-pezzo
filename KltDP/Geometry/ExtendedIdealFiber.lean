import KltDP.Geometry.AffineBlowupFiber
import KltDP.Geometry.AffineBlowupSchemeLift
import KltDP.Geometry.PrimeCurveSubscheme

/-!
# The actual closed scheme of an extended ideal is the actual center fiber

For any map Y → Spec R and any ideal I of R, the previously constructed
extended ideal sheaf has a glued closed scheme canonically isomorphic to
the categorical fiber product Y ×[Spec R] Spec(R/I). The proof computes
the actual quotient charts with the pinned tensor-quotient equivalence,
then glues maps in both directions using their actual inclusions into Y.

No regular equation, finiteness, domain, or assumed fiber identification
is required. The affine blowup specialization is in a separate module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.Geometry.ExtendedIdealFiber

open AffineBlowup

variable {R : Type u} [CommRing R] (I : Ideal R)
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))

/-- The literal scheme-theoretic inverse image of the affine center. -/
abbrev fiber := pullback f (centerInclusion I)

/-- The original projection of that actual fiber into Y. -/
abbrev fiberι : fiber I f ⟶ Y := pullback.fst f (centerInclusion I)

local instance : IsClosedImmersion (centerInclusion I) := by
  unfold centerInclusion
  exact IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) Ideal.Quotient.mk_surjective

section Chart

variable (U : Y.affineOpens)

/-- The actual ring map of the original affine chart over the base. -/
def chartRingMap : R →+* Γ(Y, U.1) :=
  (Spec.preimage (U.2.fromSpec ≫ f)).hom

private theorem spec_chartRingMap :
    Spec.map (CommRingCat.ofHom (chartRingMap f U)) = U.2.fromSpec ≫ f := by
  simp only [chartRingMap, CommRingCat.ofHom_hom, Spec.map_preimage]

/-- The actual affine quotient ring is the base-change tensor product. -/
def chartTensorEquiv :
    letI := (chartRingMap f U).toAlgebra
    (Γ(Y, U.1) ⧸ (extendedCenter I f).ideal U) ≃+*
      Γ(Y, U.1) ⊗[R] (R ⧸ I) := by
  letI := (chartRingMap f U).toAlgebra
  exact (Ideal.quotEquivOfEq (extendedCenter_ideal I f U)).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Γ(Y, U.1) I).toRingEquiv

/-- The comparison fixes the original quotient numerator. -/
theorem chartTensorEquiv_mk (a : Γ(Y, U.1)) :
    letI := (chartRingMap f U).toAlgebra
    chartTensorEquiv I f U (Ideal.Quotient.mk ((extendedCenter I f).ideal U) a) =
      a ⊗ₜ[R] (1 : R ⧸ I) := by
  letI := (chartRingMap f U).toAlgebra
  change Algebra.TensorProduct.quotIdealMapEquivTensorQuot Γ(Y, U.1) I
    (Ideal.quotEquivOfEq (extendedCenter_ideal I f U)
      (Ideal.Quotient.mk ((extendedCenter I f).ideal U) a)) = _
  rw [Ideal.quotEquivOfEq_mk]
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk Γ(Y, U.1) I a

/-- The inverse tensor comparison retains the actual scalar map. -/
theorem chartTensorEquiv_symm_tmul (a : Γ(Y, U.1)) (r : R) :
    letI := (chartRingMap f U).toAlgebra
    (chartTensorEquiv I f U).symm (a ⊗ₜ[R] (Ideal.Quotient.mk I r)) =
      Ideal.Quotient.mk ((extendedCenter I f).ideal U) (chartRingMap f U r * a) := by
  letI := (chartRingMap f U).toAlgebra
  change (Ideal.quotEquivOfEq (extendedCenter_ideal I f U)).symm
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot Γ(Y, U.1) I).symm
      (a ⊗ₜ[R] (Ideal.Quotient.mk I r))) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul,
    Ideal.quotEquivOfEq_symm]
  exact Ideal.quotEquivOfEq_mk (extendedCenter_ideal I f U).symm _

/-- Killing the actual extended ideal gives the actual quotient base map. -/
def chartQuotientMap : (R ⧸ I) →+* (Γ(Y, U.1) ⧸ (extendedCenter I f).ideal U) :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk ((extendedCenter I f).ideal U)).comp (chartRingMap f U))
    (fun r hr => Ideal.Quotient.eq_zero_iff_mem.mpr (by
      rw [extendedCenter_ideal]
      exact Ideal.mem_map_of_mem (chartRingMap f U) hr))

/-- The original quotient chart maps to the original affine center. -/
def chartToCenter : (extendedCenter I f).glueDataObj U ⟶
    Spec (CommRingCat.of (R ⧸ I)) :=
  Spec.map (CommRingCat.ofHom (chartQuotientMap I f U))

/-- Both routes from a quotient chart to the original base are identical. -/
theorem chartToCenter_comp :
    chartToCenter I f U ≫ centerInclusion I =
      ((extendedCenter I f).glueDataObjι U ≫ U.1.ι) ≫ f := by
  calc
    _ = Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk ((extendedCenter I f).ideal U))) ≫
        Spec.map (CommRingCat.ofHom (chartRingMap f U)) := by
      rw [chartToCenter, centerInclusion, ← Spec.map_comp, ← Spec.map_comp] <;> rfl
    _ = Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk ((extendedCenter I f).ideal U))) ≫
        (U.2.fromSpec ≫ f) := by rw [spec_chartRingMap]
    _ = _ := by
      simp only [Scheme.IdealSheafData.glueDataObjι, Category.assoc,
        IsAffineOpen.isoSpec_inv_ι_assoc]

/-- The actual quotient chart is the affine fiber product over the center. -/
def chartFiberIso : (extendedCenter I f).glueDataObj U ≅
    pullback (Spec.map (CommRingCat.ofHom (chartRingMap f U))) (centerInclusion I) := by
  letI := (chartRingMap f U).toAlgebra
  exact Scheme.Spec.mapIso (chartTensorEquiv I f U).symm.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R Γ(Y, U.1) (R ⧸ I)).symm

theorem chartFiberIso_hom_fst :
    (chartFiberIso I f U).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((extendedCenter I f).ideal U))) := by
  letI := (chartRingMap f U).toAlgebra
  change (Spec.map (CommRingCat.ofHom (chartTensorEquiv I f U).symm.toRingHom) ≫
    (pullbackSpecIso R Γ(Y, U.1) (R ⧸ I)).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  apply congrArg (fun g : Γ(Y, U.1) →+* (Γ(Y, U.1) ⧸ (extendedCenter I f).ideal U) =>
    Spec.map (CommRingCat.ofHom g))
  apply RingHom.ext
  intro a
  change (chartTensorEquiv I f U).symm (a ⊗ₜ[R] (1 : R ⧸ I)) = _
  apply (chartTensorEquiv I f U).injective
  rw [RingEquiv.apply_symm_apply, chartTensorEquiv_mk]

theorem chartFiberIso_hom_snd :
    (chartFiberIso I f U).hom ≫ pullback.snd _ _ = chartToCenter I f U := by
  letI := (chartRingMap f U).toAlgebra
  change (Spec.map (CommRingCat.ofHom (chartTensorEquiv I f U).symm.toRingHom) ≫
    (pullbackSpecIso R Γ(Y, U.1) (R ⧸ I)).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  apply congrArg (fun g : (R ⧸ I) →+* (Γ(Y, U.1) ⧸ (extendedCenter I f).ideal U) =>
    Spec.map (CommRingCat.ofHom g))
  apply RingHom.ext
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  change (chartTensorEquiv I f U).symm ((1 : Γ(Y, U.1)) ⊗ₜ[R] (Ideal.Quotient.mk I r)) = _
  rw [chartTensorEquiv_symm_tmul, mul_one]
  rfl

/-- The same actual pullback square in the original affine-open coordinates. -/
theorem chart_isPullback :
    IsPullback ((extendedCenter I f).glueDataObjι U) (chartToCenter I f U)
      (U.1.ι ≫ f) (centerInclusion I) := by
  have h : IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((extendedCenter I f).ideal U))))
      (chartToCenter I f U) (Spec.map (CommRingCat.ofHom (chartRingMap f U)))
      (centerInclusion I) := by
    apply IsPullback.of_iso_pullback _ (chartFiberIso I f U)
      (chartFiberIso_hom_fst I f U) (chartFiberIso_hom_snd I f U)
    constructor
    rw [chartToCenter_comp]
    simp only [Scheme.IdealSheafData.glueDataObjι, Category.assoc,
      IsAffineOpen.isoSpec_inv_ι_assoc, spec_chartRingMap]
  refine h.of_iso (Iso.refl _) U.2.isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp,
      Scheme.IdealSheafData.glueDataObjι]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id,
      spec_chartRingMap, IsAffineOpen.isoSpec_inv_ι_assoc]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The map of an actual quotient chart into the whole center fiber. -/
def chartToFiber : (extendedCenter I f).glueDataObj U ⟶ fiber I f :=
  pullback.lift ((extendedCenter I f).glueDataObjι U ≫ U.1.ι)
    (chartToCenter I f U) (chartToCenter_comp I f U).symm

@[simp] theorem chartToFiber_ι :
    chartToFiber I f U ≫ fiberι I f = (extendedCenter I f).glueDataObjι U ≫ U.1.ι :=
  pullback.lift_fst _ _ _

@[simp] theorem chartToFiber_snd :
    chartToFiber I f U ≫ pullback.snd f (centerInclusion I) = chartToCenter I f U :=
  pullback.lift_snd _ _ _

/-- Pullback cancellation identifies this chart with the actual inverse-image chart. -/
theorem chartToFiber_isPullback :
    IsPullback ((extendedCenter I f).glueDataObjι U) (chartToFiber I f U)
      U.1.ι (fiberι I f) := by
  have h := chart_isPullback I f U
  rw [← chartToFiber_snd I f U] at h
  exact h.of_bot (chartToFiber_ι I f U).symm
    (IsPullback.of_hasPullback f (centerInclusion I))

/-- The actual quotient chart and the corresponding pullback-cover object. -/
def chartRestrictionIso : (extendedCenter I f).glueDataObj U ≅
    pullback (fiberι I f) U.1.ι := (chartToFiber_isPullback I f U).flip.isoPullback

@[simp] theorem chartRestrictionIso_hom_fst :
    (chartRestrictionIso I f U).hom ≫ pullback.fst _ _ = chartToFiber I f U :=
  (chartToFiber_isPullback I f U).flip.isoPullback_hom_fst

end Chart

/-- All the original affine opens, as an actual open cover of Y. -/
def ambientCover : Y.OpenCover :=
  Y.openCoverOfISupEqTop (fun U : Y.affineOpens => U.1) (iSup_affineOpens_eq_top Y)

/-- Its actual inverse-image cover of the categorical center fiber. -/
def fiberCover : (fiber I f).OpenCover := (ambientCover (Y := Y)).pullbackCover (fiberι I f)

/-- The quotient charts glue to an actual map from the closed scheme to the fiber. -/
def toFiber : (extendedCenter I f).glueData.glued ⟶ fiber I f :=
  (extendedCenter I f).glueData.openCover.glueMorphisms (chartToFiber I f) (by
    intro U V
    rw [← cancel_mono (fiberι I f)]
    simp only [Category.assoc, chartToFiber_ι]
    rw [← (extendedCenter I f).ι_gluedTo U, ← (extendedCenter I f).ι_gluedTo V,
      ← Category.assoc, ← Category.assoc]
    exact congrArg (fun g => g ≫ (extendedCenter I f).gluedTo)
      (pullback.condition (f := (extendedCenter I f).glueData.openCover.map U)
        (g := (extendedCenter I f).glueData.openCover.map V)))

@[simp] theorem chartι_toFiber (U : Y.affineOpens) :
    (extendedCenter I f).glueData.ι U ≫ toFiber I f = chartToFiber I f U :=
  (extendedCenter I f).glueData.openCover.ι_glueMorphisms _ _ U

/-- The glued comparison retains the original closed immersion into Y. -/
@[simp] theorem toFiber_ι :
    toFiber I f ≫ fiberι I f = (extendedCenter I f).gluedTo := by
  apply (extendedCenter I f).glueData.openCover.hom_ext
  intro U
  change (extendedCenter I f).glueData.ι U ≫ (toFiber I f ≫ fiberι I f) =
    (extendedCenter I f).glueData.ι U ≫ (extendedCenter I f).gluedTo
  rw [← Category.assoc, chartι_toFiber, chartToFiber_ι,
    (extendedCenter I f).ι_gluedTo]

/-- The inverse map on a member of the actual pullback cover. -/
def chartFromFiber (U : Y.affineOpens) :
    (fiberCover I f).obj U ⟶ (extendedCenter I f).glueData.glued :=
  (chartRestrictionIso I f U).inv ≫ (extendedCenter I f).glueData.ι U

@[simp] theorem chartFromFiber_ι (U : Y.affineOpens) :
    chartFromFiber I f U ≫ (extendedCenter I f).gluedTo =
      (fiberCover I f).map U ≫ fiberι I f := by
  rw [chartFromFiber, Category.assoc, (extendedCenter I f).ι_gluedTo,
    ← chartToFiber_ι]
  rw [← chartRestrictionIso_hom_fst]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The inverse chart maps agree because they have the same actual closed inclusion. -/
def fromFiber : fiber I f ⟶ (extendedCenter I f).glueData.glued :=
  (fiberCover I f).glueMorphisms (chartFromFiber I f) (by
    intro U V
    rw [← cancel_mono (extendedCenter I f).gluedTo]
    simp only [Category.assoc, chartFromFiber_ι]
    rw [← Category.assoc, ← Category.assoc, pullback.condition])

@[simp] theorem fromFiber_ι :
    fromFiber I f ≫ (extendedCenter I f).gluedTo = fiberι I f := by
  apply (fiberCover I f).hom_ext
  intro U
  rw [← Category.assoc, fromFiber, Scheme.Cover.ι_glueMorphisms, chartFromFiber_ι]

/-- The actual glued closed scheme is the categorical center fiber over Y. -/
def iso : (extendedCenter I f).glueData.glued ≅ fiber I f where
  hom := toFiber I f
  inv := fromFiber I f
  hom_inv_id := by
    rw [← cancel_mono (extendedCenter I f).gluedTo]
    rw [Category.assoc, fromFiber_ι, toFiber_ι, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (fiberι I f)]
    rw [Category.assoc, toFiber_ι, fromFiber_ι, Category.id_comp]

@[simp] theorem iso_hom_ι : (iso I f).hom ≫ fiberι I f = (extendedCenter I f).gluedTo :=
  toFiber_ι I f

@[simp] theorem iso_inv_ι : (iso I f).inv ≫ (extendedCenter I f).gluedTo = fiberι I f :=
  fromFiber_ι I f

end KltDP.Geometry.ExtendedIdealFiber
