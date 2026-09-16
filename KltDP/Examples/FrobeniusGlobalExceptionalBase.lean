import KltDP.Examples.FrobeniusGlobalExceptionalNormal
import KltDP.Examples.FrobeniusExceptionalBaseField

/-!
# Original field structures on the global exceptional fiber

The global structure morphism is the actual closed fiber inclusion followed
by the existing whole blowup projection and its original field structure.
The affine structure likewise uses the original exceptional inclusion and
Rees projection. Their compatibility follows from the proved embedding
square. The original quotient-center scalar map also agrees with these
projections, so the existing exceptional/P1 isomorphism is over the same
field. No structure morphism is defined by transporting along an isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusGlobalExceptionalBase

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusExceptionalCharts FrobeniusExceptionalBaseField
open FrobeniusExceptionalProjectiveLine FrobeniusExceptionalLine
open FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalNormal

variable {k : Type u} [Field k]

local instance originBaseIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The affine exceptional scheme's structure is its original projection to the plane. -/
abbrev affineExceptionalStructure : exceptionalScheme (centerIdeal (k := k)) ⟶
    Spec (CommRingCat.of k) :=
  exceptionalι centerIdeal ≫ toSpec centerIdeal ≫ planeStructure

/-- The center quotient scalar map is the original plane scalar map followed by quotient. -/
theorem centerInclusion_structure :
    centerInclusion (centerIdeal (k := k)) ≫ planeStructure = centerToField := by
  have h : (Ideal.Quotient.mk (centerIdeal (k := k))).comp planeConstants =
      originQuotientEquiv.symm.toRingHom := by
    apply RingHom.ext
    intro r
    exact (originQuotientEquiv_symm r).symm
  rw [centerInclusion, planeStructure, centerToField, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, h]

/-- The actual affine center-fiber map to the field is its original blowup projection. -/
theorem fiberStructure_eq_projection :
    fiberStructure (k := k) =
      centerFiberι centerIdeal ≫ toSpec centerIdeal ≫ planeStructure := by
  rw [fiberStructure, ← centerInclusion_structure]
  simpa only [Category.assoc] using
    congrArg (fun g : centerFiber (centerIdeal (k := k)) ⟶ plane k => g ≫ planeStructure)
      (pullback.condition (f := toSpec centerIdeal) (g := centerInclusion centerIdeal)).symm

/-- The very exceptional/P1 isomorphism used for the original normal preserves the field. -/
theorem exceptionalProjectiveLineIso_hom_structure :
    (exceptionalProjectiveLineIso (k := k)).hom ≫ projectiveSpaceToSpec k 1 =
      affineExceptionalStructure := by
  rw [exceptionalProjectiveLineIso, Iso.trans_hom, Category.assoc,
    exceptionalFiberProjectiveLineIso_hom_structure, fiberStructure_eq_projection]
  change (exceptionalFiberIso (centerIdeal (k := k))).hom ≫
      (centerFiberι centerIdeal ≫ (toSpec centerIdeal ≫ planeStructure)) =
    exceptionalι centerIdeal ≫ (toSpec centerIdeal ≫ planeStructure)
  rw [← Category.assoc, exceptionalFiberIso_hom_ι]

/-- The original inverse P1 comparison preserves those same structure morphisms. -/
theorem exceptionalProjectiveLineIso_inv_structure :
    (exceptionalProjectiveLineIso (k := k)).inv ≫ affineExceptionalStructure =
      projectiveSpaceToSpec k 1 := by
  rw [← exceptionalProjectiveLineIso_hom_structure, Iso.inv_hom_id_assoc]

variable (A : PlaneChartedScheme k)

/-- The global fiber uses the original whole next-stage structure morphism. -/
abbrev globalExceptionalStructure : globalExceptionalScheme A ⟶ Spec (CommRingCat.of k) :=
  globalExceptionalInclusion A ≫ A.nextStructure

/-- The original affine blowup open immersion is over the original coefficient field. -/
theorem nextAffineBlowup_structure :
    A.nextAffineBlowup ≫ A.nextStructure = toSpec centerIdeal ≫ planeStructure := by
  rw [PlaneChartedScheme.nextStructure, ← Category.assoc,
    A.nextAffineBlowup_projection, Category.assoc, A.chart_structure]

/-- The global fiber structure also equals its actual second pullback projection to the center. -/
theorem globalExceptionalStructure_eq_toCenter :
    globalExceptionalStructure A =
      PointBlowupGluing.globalCenterFiberToCenter A.chart (originPoint (k := k))
        A.center_closed ≫ centerToField := by
  have h : globalExceptionalInclusion A ≫ A.nextProjection =
      PointBlowupGluing.globalCenterFiberToCenter A.chart (originPoint (k := k))
        A.center_closed ≫ PointBlowupGluing.closedCenterInclusion A.chart
          (originPoint (k := k)) := pullback.condition
  change globalExceptionalInclusion A ≫ (A.nextProjection ≫ A.structureMap) = _
  rw [← Category.assoc, h, Category.assoc]
  apply congrArg (fun g => PointBlowupGluing.globalCenterFiberToCenter A.chart
    (originPoint (k := k)) A.center_closed ≫ g)
  change (centerInclusion (centerIdeal (k := k)) ≫ A.chart) ≫ A.structureMap = centerToField
  rw [Category.assoc, A.chart_structure, centerInclusion_structure]

/-- The original affine/global exceptional comparison preserves the original projection maps. -/
theorem affineExceptionalIso_hom_structure :
    (affineExceptionalIso A).hom ≫ globalExceptionalStructure A =
      affineExceptionalStructure := by
  change (affineExceptionalIso A).hom ≫
      (globalExceptionalInclusion A ≫ A.nextStructure) = _
  rw [← Category.assoc, affineExceptionalIso_hom_inclusion, Category.assoc,
    nextAffineBlowup_structure]

/-- The inverse affine/global comparison is over the same original field. -/
theorem affineExceptionalIso_inv_structure :
    (affineExceptionalIso A).inv ≫ affineExceptionalStructure =
      globalExceptionalStructure A := by
  rw [← affineExceptionalIso_hom_structure A, Iso.inv_hom_id_assoc]

/-- The global center fiber and P1 are compared through the two existing actual isomorphisms. -/
def globalExceptionalProjectiveLineIso : globalExceptionalScheme A ≅ projectiveSpace k 1 :=
  (affineExceptionalIso A).symm ≪≫ exceptionalProjectiveLineIso

/-- The resulting whole-fiber/P1 comparison preserves the original global structure morphism. -/
theorem globalExceptionalProjectiveLineIso_hom_structure :
    (globalExceptionalProjectiveLineIso A).hom ≫ projectiveSpaceToSpec k 1 =
      globalExceptionalStructure A := by
  rw [globalExceptionalProjectiveLineIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, exceptionalProjectiveLineIso_hom_structure,
    affineExceptionalIso_inv_structure]

/-- The inverse used to pull the original global normal to P1 is over the same field. -/
theorem globalExceptionalProjectiveLineIso_inv_structure :
    (globalExceptionalProjectiveLineIso A).inv ≫ globalExceptionalStructure A =
      projectiveSpaceToSpec k 1 := by
  rw [← globalExceptionalProjectiveLineIso_hom_structure A, Iso.inv_hom_id_assoc]

end KltDP.Examples.FrobeniusGlobalExceptionalBase
