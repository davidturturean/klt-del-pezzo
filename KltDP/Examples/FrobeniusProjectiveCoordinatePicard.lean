import KltDP.Examples.FrobeniusProjectiveCoordinateTransition
import KltDP.Geometry.OpenFrameTransitionCoefficient
import KltDP.Geometry.ProjectiveLinePicardExponent

/-!
# The original coordinate-point kernel as an invertible sheaf

The two proved original kernel frames give an atlas of the original
scheme module. Its transition is extracted from those frames, and its
coefficient is computed through the original overlap morphism. The
Picard exponent concerns this original point ideal, with no prescribed
twist or divisor degree.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusProjectiveCoordinatePicard

open KltDP.Geometry SchemeModuleRestriction
open FrobeniusProjectiveCoordinateIdeal FrobeniusProjectiveCoordinateTransition
open ProjectiveLineComparison ProjectiveLineSections ProjectiveLineTransitionExtension
open OpenFrameTransitionCoefficient

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- The first original kernel frame, expressed through the actual open restriction. -/
def firstRestrictionFrame :
    _root_.SheafOfModules.unit (firstOpen (k := k)).toScheme.ringCatSheaf ≅
      (restriction (firstOpen (k := k)).ι).obj (schemeKernelIdeal (coordinatePoint (k := k))) :=
  firstGlobalFrameIso ≪≫
    ((restrictionIsoPullback (firstOpen (k := k)).ι).app _).symm

/-- The same original frame on the equal first standard open. -/
def leftOpenFrame :
    _root_.SheafOfModules.unit (chartOpen k 0).toScheme.ringCatSheaf ≅
      (restriction (chartOpen k 0).ι).obj (schemeKernelIdeal (coordinatePoint (k := k))) :=
  frameOfOpenEq _ (firstOpen_eq (k := k)) firstRestrictionFrame

/-- The actual unit-equation frame on the second standard open. -/
def rightOpenFrame :
    _root_.SheafOfModules.unit (chartOpen k 1).toScheme.ringCatSheaf ≅
      (restriction (chartOpen k 1).ι).obj (schemeKernelIdeal (coordinatePoint (k := k))) :=
  rightGlobalFrameIso ≪≫ ((restrictionIsoPullback (chartOpen k 1).ι).app _).symm

/-- Both original standard opens carry the proved point-kernel frames. -/
def originalOpenFrame (i : Fin 2) :
    _root_.SheafOfModules.unit (chartOpen k i).toScheme.ringCatSheaf ≅
      (restriction (chartOpen k i).ι).obj (schemeKernelIdeal (coordinatePoint (k := k))) := by
  exact Fin.cases (leftOpenFrame (k := k))
    (Fin.cases (rightOpenFrame (k := k)) (fun j => Fin.elim0 j)) i

/-- The actual two standard opens cover the original projective line. -/
theorem originalOpens_cover (x : projectiveSpace k 1) :
    ∃ i : ULift.{u} (Fin 2), x ∈ standardOpens k i := by
  have hx : x ∈ chartOpen k 0 ⊔ chartOpen k 1 := by
    rw [chartOpen_sup]
    trivial
  rcases hx with hx | hx
  · exact ⟨⟨0⟩, hx⟩
  · exact ⟨⟨1⟩, hx⟩

/-- An atlas of the original point-kernel module, from the original two frames. -/
def originalAtlas : KltDP.SheafOfModules.LocalTrivializations
    (R := (projectiveSpace k 1).ringCatSheaf) (schemeKernelIdeal (coordinatePoint (k := k))) :=
  localTrivializationsOfOpenCharts _ (standardOpens k) originalOpens_cover
    (fun i => originalOpenFrame i.down)

/-- The actual kernel of the original coordinate point is invertible. -/
theorem coordinateKernel_isInvertible :
    isInvertibleSheaf (projectiveSpace k 1) (schemeKernelIdeal (coordinatePoint (k := k))) :=
  (originalAtlas (k := k)).isInvertible

/-- The invertible sheaf has literally the original coordinate-point kernel as its object. -/
def coordinateIdealLine : InvertibleSheaf (projectiveSpace k 1) :=
  InvertibleSheaf.ofLocalTrivializations _ (originalAtlas (k := k))

theorem coordinateIdealLine_obj :
    (coordinateIdealLine (k := k)).obj = schemeKernelIdeal (coordinatePoint (k := k)) := rfl

theorem originalAtlas_X (i : ULift.{u} (Fin 2)) :
    (originalAtlas (k := k)).X i = standardOpens k i := rfl

/-- The original atlas coordinates cancel only the singleton-free comparison. -/
theorem originalAtlas_unitIso_hom (i : ULift.{u} (Fin 2)) :
    ((originalAtlas (k := k)).unitIso i).hom =
      (openChartToOverUnitIso (standardOpens k i) (schemeKernelIdeal (coordinatePoint (k := k)))
        (originalOpenFrame i.down)).inv := by
  simp only [originalAtlas, KltDP.SheafOfModules.LocalTrivializations.unitIso,
    localTrivializationsOfOpenCharts, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem originalAtlas_unitIso_inv (i : ULift.{u} (Fin 2)) :
    ((originalAtlas (k := k)).unitIso i).inv =
      (openChartToOverUnitIso (standardOpens k i) (schemeKernelIdeal (coordinatePoint (k := k)))
        (originalOpenFrame i.down)).hom := by
  exact (Iso.inv_eq_inv ((originalAtlas (k := k)).unitIso i)
    (openChartToOverUnitIso (standardOpens k i)
      (schemeKernelIdeal (coordinatePoint (k := k)))
      (originalOpenFrame i.down)).symm).mpr (originalAtlas_unitIso_hom (k := k) i)

/-- Actual units extracted from the original coordinate-point atlas. -/
def originalUnits : ∀ i j : ULift.{u} (Fin 2),
    Γ(projectiveSpace k 1, standardOpens k i ⊓ standardOpens k j)ˣ :=
  TransitionUnitExtraction.transitionUnits (projectiveSpace k 1)
    (schemeKernelIdeal (coordinatePoint (k := k))) originalAtlas

theorem originalUnits_isCocycle :
    TransitionUnitGluing.IsCocycle (projectiveSpace k 1) (standardOpens k)
      (originalUnits (k := k)) :=
  TransitionUnitExtraction.transitionUnits_isCocycle (projectiveSpace k 1)
    (schemeKernelIdeal (coordinatePoint (k := k))) originalAtlas

/-- The actual original kernel is recovered from its extracted transition units. -/
def originalRecoveryIso : (coordinateIdealLine (k := k)).obj ≅
    TransitionUnitGluing.moduleSheaf (projectiveSpace k 1) (standardOpens k) originalUnits :=
  TransitionUnitExtraction.recoveryIso (projectiveSpace k 1)
    (schemeKernelIdeal (coordinatePoint (k := k))) originalAtlas

/-- The original point ideal's existing exponent is computed by its actual frame atlas. -/
theorem coordinateExponent_eq_originalCocycle :
    ProjectiveLineSheafExponent.exponent k (coordinateIdealLine (k := k)) =
      cocycleExponent k (originalUnits (k := k)) :=
  ProjectiveLineSheafExponent.exponent_eq_of_iso_to_glued k coordinateIdealLine originalUnits
    originalUnits_isCocycle originalRecoveryIso

/-- The original overlap map factors through the equal first standard open. -/
def overlapToLeftOpen : Spec (CommRingCat.of (overlapRing k)) ⟶ (chartOpen k 0).toScheme :=
  overlapToFirst ≫ eqToHom
    (congrArg (fun W : (projectiveSpace k 1).Opens => W.toScheme) (firstOpen_eq (k := k)))

theorem overlapToLeftOpen_ι :
    overlapToLeftOpen (k := k) ≫ (chartOpen k 0).ι = overlapMap :=
  mapOfOpenEq_ι (firstOpen_eq (k := k)) overlapToFirst

/-- The first normalized standard-open frame is the proved original overlap frame. -/
theorem normalized_left_frame :
    (normalizedFrameIso (chartOpen k 0) (schemeKernelIdeal (coordinatePoint (k := k))) leftOpenFrame
      overlapToLeftOpen (overlapMap (k := k)) overlapToLeftOpen_ι).hom = leftOverlapFrame := by
  unfold leftOpenFrame overlapToLeftOpen
  rw [normalizedFrameIso_frameOfOpenEq _ (firstOpen_eq (k := k))
    firstRestrictionFrame overlapToFirst overlapMap rfl overlapToLeftOpen_ι]
  have he : firstRestrictionFrame (k := k) ≪≫
      (restrictionIsoPullback (firstOpen (k := k)).ι).app (schemeKernelIdeal (coordinatePoint (k := k))) =
        firstGlobalFrameIso := by
    simp only [firstRestrictionFrame, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  simp only [normalizedFrameIso, he, leftOverlapFrame, kernelFrameRefinement,
    schemeModulePullbackFrame, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    eqToIso_refl, Iso.app_hom, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    Category.assoc]

/-- Normalize the same original frame refinement before specializing its schemes and maps. -/
private theorem normalizedFrameIso_kernel_refinement
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      (restriction U.ι).obj (schemeKernelIdeal f))
    (s : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      (schemeModulePullback U.ι).obj (schemeKernelIdeal f))
    (he : e ≪≫ (restrictionIsoPullback U.ι).app (schemeKernelIdeal f) = s)
    (q : Z ⟶ U.toScheme) (l : Z ⟶ Y) (h : q ≫ U.ι = l) :
    (normalizedFrameIso U (schemeKernelIdeal f) e q l h).hom =
      kernelFrameRefinement f U.ι q s.hom ≫
        (eqToIso (congrArg schemeModulePullback h)).hom.app (schemeKernelIdeal f) := by
  simp only [normalizedFrameIso, he, kernelFrameRefinement,
    schemeModulePullbackFrame, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Category.assoc]

-- Cancel the original restriction comparison before specializing the actual frames.
private theorem normalizedFrameIso_kernel_refinement_cancel
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (s : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      (schemeModulePullback U.ι).obj (schemeKernelIdeal f))
    (q : Z ⟶ U.toScheme) (l : Z ⟶ Y) (h : q ≫ U.ι = l) :
    (normalizedFrameIso U (schemeKernelIdeal f)
      (s ≪≫ ((restrictionIsoPullback U.ι).app (schemeKernelIdeal f)).symm) q l h).hom =
      kernelFrameRefinement f U.ι q s.hom ≫
        (eqToIso (congrArg schemeModulePullback h)).hom.app (schemeKernelIdeal f) := by
  have he : (s ≪≫ ((restrictionIsoPullback U.ι).app (schemeKernelIdeal f)).symm) ≪≫
      (restrictionIsoPullback U.ι).app (schemeKernelIdeal f) = s := by
    simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  exact normalizedFrameIso_kernel_refinement f U
    (s ≪≫ ((restrictionIsoPullback U.ι).app (schemeKernelIdeal f)).symm) s he q l h

-- Keep the named endpoint maps intact when specializing the abstract normalization.
private theorem normalizedFrameIso_kernel_refinement_named
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (s : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      (schemeModulePullback U.ι).obj (schemeKernelIdeal f))
    (q : Z ⟶ U.toScheme) (l : Z ⟶ Y) (h : q ≫ U.ι = l)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      (restriction U.ι).obj (schemeKernelIdeal f))
    (he : e = s ≪≫ ((restrictionIsoPullback U.ι).app (schemeKernelIdeal f)).symm)
    (t : _root_.SheafOfModules.unit Z.ringCatSheaf ⟶
      (schemeModulePullback l).obj (schemeKernelIdeal f))
    (ht : kernelFrameRefinement f U.ι q s.hom ≫
      (eqToIso (congrArg schemeModulePullback h)).hom.app (schemeKernelIdeal f) = t) :
    (normalizedFrameIso U (schemeKernelIdeal f) e q l h).hom = t := by
  subst e
  exact (normalizedFrameIso_kernel_refinement_cancel f U s q l h).trans ht

-- Check the two concrete endpoint conversions separately from normalization.
private theorem rightOpenFrame_original_comparison :
    rightOpenFrame (k := k) =
      rightGlobalFrameIso (k := k) ≪≫
        ((restrictionIsoPullback (chartOpen k 1).ι).app
          (schemeKernelIdeal (coordinatePoint (k := k)))).symm :=
  Eq.refl (rightOpenFrame (k := k))

private theorem rightOverlapFrame_original_refinement :
    kernelFrameRefinement (coordinatePoint (k := k)) (chartOpen k 1).ι
        (overlapToRight (k := k)) (rightGlobalFrameIso (k := k)).hom ≫
      (eqToIso (congrArg schemeModulePullback (overlapMap_right (k := k)))).hom.app
        (schemeKernelIdeal (coordinatePoint (k := k))) = rightOverlapFrame (k := k) := by
  apply (pulledKernelInclusion_cancel
    (coordinatePoint (k := k)) (overlapMap (k := k)) _ _).mp
  calc
    _ = kernelFrameRefinement (coordinatePoint (k := k)) (chartOpen k 1).ι
          (overlapToRight (k := k)) (rightGlobalFrameIso (k := k)).hom ≫
        pulledKernelInclusion (coordinatePoint (k := k))
          (overlapToRight (k := k) ≫ (chartOpen k 1).ι) :=
      (Category.assoc
        (kernelFrameRefinement (coordinatePoint (k := k)) (chartOpen k 1).ι
          (overlapToRight (k := k)) (rightGlobalFrameIso (k := k)).hom)
        ((eqToIso (congrArg schemeModulePullback (overlapMap_right (k := k)))).hom.app
          (schemeKernelIdeal (coordinatePoint (k := k))))
        (pulledKernelInclusion (coordinatePoint (k := k)) (overlapMap (k := k)))).trans
        (congrArg (fun a :
            (schemeModulePullback (overlapToRight (k := k) ≫ (chartOpen k 1).ι)).obj
                (schemeKernelIdeal (coordinatePoint (k := k))) ⟶
              _root_.SheafOfModules.unit
                (Spec (CommRingCat.of (overlapRing k))).ringCatSheaf =>
          kernelFrameRefinement (coordinatePoint (k := k)) (chartOpen k 1).ι
            (overlapToRight (k := k)) (rightGlobalFrameIso (k := k)).hom ≫ a)
          (pulledKernelInclusion_congr (coordinatePoint (k := k))
            (overlapMap_right (k := k))))
    _ = schemeScalarEnd ((overlapToRight (k := k)).appTop
        (1 : Γ((chartOpen k 1).toScheme, ⊤))) :=
      (congrArg (fun s :
          _root_.SheafOfModules.unit (chartOpen k 1).toScheme.ringCatSheaf ⟶
            (schemeModulePullback (chartOpen k 1).ι).obj
              (schemeKernelIdeal (coordinatePoint (k := k))) =>
        kernelFrameRefinement (coordinatePoint (k := k)) (chartOpen k 1).ι
          (overlapToRight (k := k)) s ≫
            pulledKernelInclusion (coordinatePoint (k := k))
              (overlapToRight (k := k) ≫ (chartOpen k 1).ι))
        (rightGlobalFrameIso_hom (k := k))).trans
        (localKernelGlobalEquation_refinement_inclusion
          (coordinatePoint (k := k)) (chartOpen k 1) 1
          (rightCoordinateEquation_eq_zero (k := k)) (overlapToRight (k := k)))
    _ = _ := (rightOverlapFrame_inclusion (k := k)).symm

set_option maxHeartbeats 800000 in
/-- The second normalized frame retains the proved equality transport of the original maps. -/
theorem normalized_right_frame :
    (normalizedFrameIso (chartOpen k 1) (schemeKernelIdeal (coordinatePoint (k := k))) rightOpenFrame
      overlapToRight (overlapMap (k := k)) overlapMap_right).hom = rightOverlapFrame := by
  exact normalizedFrameIso_kernel_refinement_named
    (coordinatePoint (k := k)) (chartOpen k 1) (rightGlobalFrameIso (k := k))
    (overlapToRight (k := k)) (overlapMap (k := k)) (overlapMap_right (k := k))
    (rightOpenFrame (k := k)) (rightOpenFrame_original_comparison (k := k))
    (rightOverlapFrame (k := k)) (rightOverlapFrame_original_refinement (k := k))

/-- The actual overlap maps entirely into the original standard-open intersection. -/
theorem overlap_preimage_top :
    (⊤ : (Spec (CommRingCat.of (overlapRing k))).Opens) ≤
      overlapMap (k := k) ⁻¹ᵁ overlapOpen k := by
  intro x _
  rw [overlapOpen_eq_inf]
  constructor
  · change (overlapMap (k := k)).base x ∈ chartOpen k 0
    rw [← overlapToLeftOpen_ι]
    exact ((overlapToLeftOpen (k := k)).base x).property
  · change (overlapMap (k := k)).base x ∈ chartOpen k 1
    rw [← overlapMap_right]
    exact ((overlapToRight (k := k)).base x).property

private theorem originalUnits_overlap_value :
    (overlapRestriction k (originalUnits (k := k) ⟨0⟩ ⟨1⟩) :
      Γ(projectiveSpace k 1, overlapOpen k)) =
      (openChartToOverUnitIso (chartOpen k 0) (schemeKernelIdeal (coordinatePoint (k := k)))
        leftOpenFrame).inv.val.app (op (Over.mk (homOfLE (overlapOpen_le_left k))))
        ((openChartToOverUnitIso (chartOpen k 1) (schemeKernelIdeal (coordinatePoint (k := k)))
          rightOpenFrame).hom.val.app (op (Over.mk (homOfLE (overlapOpen_le_right k))))
            (1 : Γ(projectiveSpace k 1, overlapOpen k))) := by
  change TransitionUnitGluing.res (projectiveSpace k 1) (overlapOpen_eq_inf k).le
    (TransitionUnitExtraction.transitionUnitOn (projectiveSpace k 1)
      (schemeKernelIdeal (coordinatePoint (k := k))) originalAtlas ⟨0⟩ ⟨1⟩
      inf_le_left inf_le_right).val = _
  rw [TransitionUnitExtraction.transitionUnitOn_restrict]
  simp only [TransitionUnitExtraction.transitionUnitOn, KltDP.Module.transitionUnit_val,
    TransitionUnitExtraction.chartEquiv_apply, TransitionUnitExtraction.chartEquiv_symm_apply,
    originalAtlas_unitIso_hom, originalAtlas_unitIso_inv]
  rfl

/-- The original atlas transition pulls back to the proved original reciprocal section. -/
theorem originalUnits_overlap_pullback :
    (overlapMap (k := k)).appLE (overlapOpen k) ⊤ overlap_preimage_top
      (overlapRestriction k (originalUnits (k := k) ⟨0⟩ ⟨1⟩) :
        Γ(projectiveSpace k 1, overlapOpen k)) = reciprocalSection := by
  have h := coefficient (chartOpen k 0) (chartOpen k 1) (overlapOpen k)
    (overlapOpen_le_left k) (overlapOpen_le_right k) (schemeKernelIdeal (coordinatePoint (k := k)))
    leftOpenFrame rightOpenFrame overlapToLeftOpen overlapToRight overlapMap
    overlapToLeftOpen_ι overlapMap_right overlap_preimage_top (reciprocalSection (k := k))
    (by
      rw [normalized_left_frame, normalized_right_frame]
      exact overlapFrame_transition)
  rw [originalUnits_overlap_value]
  exact h

private def projectiveOverlapOpenIso :
    (overlapOpen k).toScheme ≅ Spec (CommRingCat.of (overlapRing k)) :=
  Proj.basicOpenIsoSpec (grading k)
    ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)
    (SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X k (0 : Fin 2))
      (MvPolynomial.isHomogeneous_X k (1 : Fin 2))) (by decide)

/-- The homogeneous overlap isomorphism preserves the original overlap inclusion. -/
private theorem projectiveOverlapOpenIso_inv_ι :
    (projectiveOverlapOpenIso (k := k)).inv ≫ (overlapOpen k).ι = overlapMap := by
  rw [overlapMap_left]
  simpa only [toOverlapLeft, chartImmersion, projectiveOverlapOpenIso, Proj.awayι] using
    (Proj.SpecMap_awayMap_awayι (grading k)
      (MvPolynomial.isHomogeneous_X k (0 : Fin 2)) (by decide)
      (MvPolynomial.isHomogeneous_X k (1 : Fin 2)) rfl).symm

private theorem overlap_appLE_eq :
    (overlapMap (k := k)).appLE (overlapOpen k) ⊤ overlap_preimage_top =
      (overlapOpen k).topIso.inv ≫ (projectiveOverlapOpenIso (k := k)).inv.appTop := by
  have H := Scheme.appLE_comp_appLE (projectiveOverlapOpenIso (k := k)).inv
    (overlapOpen k).ι (overlapOpen k) ⊤ ⊤
    (overlapOpen k).ι_preimage_self.ge le_rfl
  simp only [projectiveOverlapOpenIso_inv_ι] at H
  simpa only [Scheme.Hom.appLE_eq_app, Scheme.Opens.ι_appLE,
    Scheme.Opens.topIso_inv, eqToHom_op] using H.symm

/-- Original homogeneous sections followed by the original overlap map are Gamma-Spec. -/
private theorem awayToSection_overlap_appLE :
    Proj.awayToSection (grading k)
        ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1) ≫
      (overlapMap (k := k)).appLE (overlapOpen k) ⊤ overlap_preimage_top =
        (Scheme.ΓSpecIso (CommRingCat.of (overlapRing k))).inv := by
  have hc : Proj.awayToSection (grading k)
        ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1) ≫
      (overlapOpen k).topIso.inv =
        (Scheme.ΓSpecIso (CommRingCat.of (overlapRing k))).inv ≫
          (projectiveOverlapOpenIso (k := k)).hom.appTop := by
    rw [projectiveOverlapOpenIso, Proj.basicOpenIsoSpec_hom,
      Scheme.Hom.appTop, Proj.basicOpenToSpec_app_top, Iso.inv_hom_id_assoc]
    rfl
  rw [overlap_appLE_eq, ← Category.assoc, hc, Category.assoc,
    ← Scheme.comp_appTop, Iso.inv_hom_id, Scheme.id_appTop, Category.comp_id]

/-- The original Laurent section coordinates agree with the actual overlap map. -/
theorem overlapSectionsEquiv_originalMap (s : Γ(projectiveSpace k 1, overlapOpen k)) :
    overlapSectionsEquiv k s = overlapLaurentEquiv k
      ((Scheme.ΓSpecIso (CommRingCat.of (overlapRing k))).hom
        ((overlapMap (k := k)).appLE (overlapOpen k) ⊤ overlap_preimage_top s)) := by
  obtain ⟨r, hr⟩ := (Proj.basicOpenIsoAway (grading k)
    ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)
    (SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X k (0 : Fin 2))
      (MvPolynomial.isHomogeneous_X k (1 : Fin 2))) (by decide)).commRingCatIsoToRingEquiv.surjective s
  change (Proj.awayToSection (grading k)
    ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)) r = s at hr
  rw [← hr, overlapSectionsEquiv_awayToSection]
  have h := ConcreteCategory.congr_hom (awayToSection_overlap_appLE (k := k)) r
  change (overlapMap (k := k)).appLE (overlapOpen k) ⊤ overlap_preimage_top
      ((Proj.awayToSection (grading k)
        ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)) r) =
      (Scheme.ΓSpecIso (CommRingCat.of (overlapRing k))).inv r at h
  rw [h]
  exact (congrArg (overlapLaurentEquiv k) (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso (CommRingCat.of (overlapRing k))).inv_hom_id r)).symm

/-- The transition extracted from the original point kernel has Laurent coordinate T^-1. -/
theorem originalUnits_laurent :
    overlapSectionsEquiv k
      (overlapRestriction k (originalUnits (k := k) ⟨0⟩ ⟨1⟩) :
        Γ(projectiveSpace k 1, overlapOpen k)) = LaurentPolynomial.T (-1) := by
  rw [overlapSectionsEquiv_originalMap, originalUnits_overlap_pullback]
  exact reciprocalSection_laurent

/-- The original coordinate-point ideal has exponent minus one. -/
theorem coordinateExponent_eq_neg_one :
    ProjectiveLineSheafExponent.exponent k (coordinateIdealLine (k := k)) = -1 := by
  have h (s : Γ(projectiveSpace k 1, overlapOpen k)ˣ)
      (hs : overlapSectionsEquiv k (s : Γ(projectiveSpace k 1, overlapOpen k)) =
        LaurentPolynomial.T (-1)) :
      ProjectiveLineTransitionExponent.overlapExponent k s = -1 := by
    apply ProjectiveLineTransitionExponent.unitExponent_eq_of_monomial k
      (ProjectiveLineTransitionExponent.overlapLaurentUnit k s) (1 : kˣ) (-1)
    change overlapSectionsEquiv k (s : Γ(projectiveSpace k 1, overlapOpen k)) = _
    simpa only [Units.val_one, map_one, one_mul] using hs
  rw [coordinateExponent_eq_originalCocycle, cocycleExponent]
  exact h (overlapRestriction k (originalUnits (k := k) ⟨0⟩ ⟨1⟩))
    (originalUnits_laurent (k := k))

/-- Its existing Picard value is computed for the original kernel object. -/
theorem coordinatePicardValue_eq_neg_one :
    ProjectiveLinePicardExponent.value k (coordinateIdealLine (k := k)).toPic = -1 := by
  rw [ProjectiveLinePicardExponent.value_toPic, coordinateExponent_eq_neg_one]

end KltDP.Examples.FrobeniusProjectiveCoordinatePicard
