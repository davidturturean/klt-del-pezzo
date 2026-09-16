import KltDP.Examples.FrobeniusProjectiveCoordinateIdeal
import KltDP.Geometry.SchemeKernelOpenPullback
import KltDP.Geometry.ProjectiveLineSections

/-!
# Original coordinate-point ideal frames and their reciprocal transition

The local equations are transported into the kernel module of the original
projective point morphism. Both overlap frames take values in the same
actual open pullback of that kernel. Their transition is determined through
the original kernel inclusion and the existing reciprocal coordinate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusProjectiveCoordinateTransition

open KltDP.Geometry
open FrobeniusProjectiveCoordinateIdeal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

/-- The actual restricted section kernel uses the original top-section
comparison, for the original morphism rather than a replacement subscheme. -/
private theorem kernel_restrict_top {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) :
    RingHom.ker (f ∣_ U.1).appTop.hom =
      (f.ker.ideal U).comap U.1.topIso.hom.hom := by
  have h : (f ∣_ U.1).appTop =
      (U.1.topIso.hom ≫ f.app U.1) ≫ (f ⁻¹ᵁ U.1).topIso.inv := by
    simpa only [Scheme.Γ_map_op, Category.assoc] using Γ_map_morphismRestrict f U.1
  have hinj : Function.Injective (f ⁻¹ᵁ U.1).topIso.inv.hom :=
    (f ⁻¹ᵁ U.1).topIso.symm.commRingCatIsoToRingEquiv.injective
  rw [h, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hinj,
    CommRingCat.hom_comp, ← RingHom.comap_ker, ← Scheme.Hom.ker_apply f U]

end

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- The first original polynomial chart image, with its actual image-open type. -/
def firstOpen : (projectiveSpace k 1).Opens :=
  ProjectiveLineComparison.polynomialChartMap k 0 ''ᵁ ⊤

/-- This is the original first standard projective open. -/
theorem firstOpen_eq : firstOpen (k := k) = ProjectiveLineComparison.chartOpen k 0 := by
  rw [firstOpen, Scheme.Hom.image_top_eq_opensRange,
    ProjectiveLineComparison.polynomialChartMap_opensRange]

/-- Its affineness is inherited from the actual polynomial chart. -/
def firstAffineOpen : (projectiveSpace k 1).affineOpens :=
  ⟨firstOpen, (isAffineOpen_top (Spec (CommRingCat.of (Polynomial k)))).image_of_isOpenImmersion
    (ProjectiveLineComparison.polynomialChartMap k 0)⟩

/-- The first equation in the original ambient section ring. -/
def firstSection : Γ(projectiveSpace k 1, firstOpen (k := k)) :=
  ((ProjectiveLineComparison.polynomialChartMap k 0).appIso ⊤).inv
    (affineCoordinateEquation (k := k))

/-- Original point-ideal generation follows from the actual chart kernel
and the original chart section isomorphism. -/
theorem firstSection_ideal :
    (coordinatePointIdeal (k := k)).ideal firstAffineOpen = Ideal.span {firstSection} := by
  let e :=
    ((ProjectiveLineComparison.polynomialChartMap k 0).appIso ⊤).symm.commRingCatIsoToRingEquiv
  have h := coordinatePointIdeal_chart (k := k)
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of (Polynomial k)))⟩
  rw [Scheme.Hom.ker_apply, affineCoordinatePoint_kernel] at h
  change Ideal.span {affineCoordinateEquation (k := k)} =
    ((coordinatePointIdeal (k := k)).ideal firstAffineOpen).comap e.toRingHom at h
  calc
    _ = (((coordinatePointIdeal (k := k)).ideal firstAffineOpen).comap
        e.toRingHom).map e.toRingHom :=
      (Ideal.map_comap_of_surjective e.toRingHom e.surjective _).symm
    _ = (Ideal.span {affineCoordinateEquation (k := k)}).map e.toRingHom := by rw [← h]
    _ = Ideal.span {firstSection (k := k)} := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl

/-- The same equation on the actual open subscheme. -/
def firstEquation : Γ((firstOpen (k := k)).toScheme, ⊤) :=
  (firstOpen (k := k)).topIso.inv firstSection

/-- The kernel is that of the original restricted projective point. -/
theorem firstEquation_kernel :
    RingHom.ker (coordinatePoint (k := k) ∣_ firstOpen).appTop.hom =
      Ideal.span {firstEquation} := by
  change RingHom.ker (coordinatePoint (k := k) ∣_
    (firstAffineOpen (k := k)).1).appTop.hom = _
  rw [kernel_restrict_top coordinatePoint firstAffineOpen]
  change ((coordinatePointIdeal (k := k)).ideal (firstAffineOpen (k := k))).comap
    (firstOpen (k := k)).topIso.hom.hom = _
  rw [firstSection_ideal]
  let e := (firstOpen (k := k)).topIso.commRingCatIsoToRingEquiv
  change (Ideal.span {firstSection (k := k)}).comap e.toRingHom =
    Ideal.span {e.symm firstSection}
  rw [RingEquiv.toRingHom_eq_coe e, Ideal.comap_coe e, ← Ideal.map_symm e,
    Ideal.map_span, Set.image_singleton]

/-- The actual local equation is killed by the original point restriction. -/
theorem firstEquation_eq_zero :
    (coordinatePoint (k := k) ∣_ firstOpen).appTop firstEquation = 0 := by
  apply RingHom.mem_ker.mp
  rw [firstEquation_kernel]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Its regularity is transported through the two original section isomorphisms. -/
theorem firstEquation_regular :
    firstEquation (k := k) ∈ nonZeroDivisors Γ((firstOpen (k := k)).toScheme, ⊤) := by
  let e := (firstOpen (k := k)).topIso.commRingCatIsoToRingEquiv
  let a :=
    ((ProjectiveLineComparison.polynomialChartMap k 0).appIso ⊤).commRingCatIsoToRingEquiv
  apply mem_nonZeroDivisors_of_injective (f := e) e.injective
  change e (e.symm firstSection) ∈ nonZeroDivisors Γ(projectiveSpace k 1, firstOpen)
  rw [e.apply_symm_apply]
  apply mem_nonZeroDivisors_of_injective (f := a) a.injective
  change a (a.symm affineCoordinateEquation) ∈
    nonZeroDivisors Γ(Spec (CommRingCat.of (Polynomial k)), ⊤)
  rw [a.apply_symm_apply]
  exact affineCoordinateEquation_regular

/-- The first original kernel frame on the literal first open. -/
def firstLocalFrameIso :
    _root_.SheafOfModules.unit (firstOpen (k := k)).toScheme.ringCatSheaf ≅
      schemeKernelIdeal (coordinatePoint (k := k) ∣_ firstOpen) := by
  letI : IsAffine (firstOpen (k := k)).toScheme := (firstAffineOpen (k := k)).2
  letI : IsClosedImmersion (coordinatePoint (k := k) ∣_ firstOpen) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict coordinatePoint firstOpen).flip
      inferInstance
  exact principalKernelSheafIso (coordinatePoint ∣_ firstOpen) firstEquation
    firstEquation_eq_zero firstEquation_kernel firstEquation_regular

/-- The first frame now takes values in the pullback of the ORIGINAL projective kernel. -/
def firstGlobalFrameIso :
    _root_.SheafOfModules.unit (firstOpen (k := k)).toScheme.ringCatSheaf ≅
      (schemeModulePullback (firstOpen (k := k)).ι).obj
        (schemeKernelIdeal (coordinatePoint (k := k))) :=
  firstLocalFrameIso ≪≫ localKernelToGlobalPullbackIso coordinatePoint firstOpen

/-- The map is exactly the original equation lift with canonical kernel comparison. -/
theorem firstGlobalFrameIso_hom :
    (firstGlobalFrameIso (k := k)).hom =
      localKernelGlobalEquation coordinatePoint firstOpen firstEquation firstEquation_eq_zero := rfl

/-- Its original projective kernel inclusion recovers the original first equation. -/
theorem firstGlobalFrameIso_inclusion :
    (firstGlobalFrameIso (k := k)).hom ≫
      pulledKernelInclusion (coordinatePoint (k := k)) (firstOpen (k := k)).ι =
        (schemeScalarEnd (Y := (firstOpen (k := k)).toScheme) (firstEquation (k := k)) :
          _root_.SheafOfModules.unit (firstOpen (k := k)).toScheme.ringCatSheaf ⟶
            _root_.SheafOfModules.unit (firstOpen (k := k)).toScheme.ringCatSheaf) :=
  localKernelGlobalEquation_inclusion coordinatePoint firstOpen firstEquation firstEquation_eq_zero

/-- The second original unit frame has the same projective kernel as its source of pullback. -/
def rightGlobalFrameIso :
    _root_.SheafOfModules.unit (ProjectiveLineComparison.chartOpen k 1).toScheme.ringCatSheaf ≅
      (schemeModulePullback (ProjectiveLineComparison.chartOpen k 1).ι).obj
        (schemeKernelIdeal (coordinatePoint (k := k))) :=
  rightCoordinateKernelFrameIso ≪≫
    localKernelToGlobalPullbackIso coordinatePoint (ProjectiveLineComparison.chartOpen k 1)

theorem rightGlobalFrameIso_hom :
    (rightGlobalFrameIso (k := k)).hom =
      localKernelGlobalEquation coordinatePoint (ProjectiveLineComparison.chartOpen k 1)
        1 rightCoordinateEquation_eq_zero := by
  simp only [rightGlobalFrameIso, Iso.trans_hom, rightCoordinateKernelFrameIso_hom,
    localKernelGlobalEquation, rightCoordinatePoint]

/-- The original polynomial chart isomorphism onto its actual image open. -/
def firstChartIso : Spec (CommRingCat.of (Polynomial k)) ≅ (firstOpen (k := k)).toScheme :=
  (ProjectiveLineComparison.polynomialChartMap k 0).isoOpensRange ≪≫
    (projectiveSpace k 1).isoOfEq
      (ProjectiveLineComparison.polynomialChartMap k 0).image_top_eq_opensRange.symm

@[reassoc]
theorem firstChartIso_hom_ι :
    (firstChartIso (k := k)).hom ≫ (firstOpen (k := k)).ι =
      ProjectiveLineComparison.polynomialChartMap k 0 := by
  simp only [firstChartIso, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
    Scheme.Hom.isoOpensRange_hom_ι]

/-- The original chart section isomorphism is the actual map through the
literal open, with its canonical top-section normalization. -/
theorem firstChartIso_sections :
    (firstOpen (k := k)).topIso.inv ≫ (firstChartIso (k := k)).hom.appTop =
      ((ProjectiveLineComparison.polynomialChartMap k 0).appIso ⊤).hom := by
  have h := Scheme.appLE_comp_appLE (firstChartIso (k := k)).hom (firstOpen (k := k)).ι
    (firstOpen (k := k)) ⊤ ⊤ (firstOpen (k := k)).ι_preimage_self.ge le_rfl
  have appLE_of_eq :
      ∀ {X Y : Scheme.{u}} (f g : X ⟶ Y) (e : f = g)
        (U : Y.Opens) (V : X.Opens)
        (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U),
        f.appLE U V hf = g.appLE U V hg := by
    intro X Y f g e U V hf hg
    cases e
    rfl
  have h' := h.trans (appLE_of_eq
    ((firstChartIso (k := k)).hom ≫ (firstOpen (k := k)).ι)
    (ProjectiveLineComparison.polynomialChartMap k 0)
    (firstChartIso_hom_ι (k := k)) (firstOpen (k := k)) ⊤
    _ ((ProjectiveLineComparison.polynomialChartMap k 0).preimage_image_eq ⊤).ge)
  rw [Scheme.Hom.appIso_hom']
  simpa only [Scheme.Hom.appLE_eq_app, Scheme.Opens.ι_appLE,
    Scheme.Opens.topIso_inv, eqToHom_op] using h'

/-- Pulling the transported equation back gives the exact previously
proved polynomial equation, not a unit multiple chosen afterward. -/
theorem firstChartIso_equation :
    (firstChartIso (k := k)).hom.appTop firstEquation = affineCoordinateEquation := by
  have h := ConcreteCategory.congr_hom (firstChartIso_sections (k := k)) firstSection
  change (firstChartIso (k := k)).hom.appTop firstEquation =
    ((ProjectiveLineComparison.polynomialChartMap k 0).appIso ⊤).hom
      (((ProjectiveLineComparison.polynomialChartMap k 0).appIso ⊤).inv
        (affineCoordinateEquation (k := k))) at h
  exact h.trans (ConcreteCategory.congr_hom
    ((ProjectiveLineComparison.polynomialChartMap k 0).appIso ⊤).inv_hom_id _)

/-- The actual second homogeneous chart, identified with its original standard open. -/
def rightChartIso :
    Spec (CommRingCat.of (ProjectiveLineComparison.chartRing k 1)) ≅
      (ProjectiveLineComparison.chartOpen k 1).toScheme :=
  (ProjectiveLineComparison.chartImmersion k 1).isoOpensRange ≪≫
    (projectiveSpace k 1).isoOfEq (ProjectiveLineComparison.chartImmersion_opensRange k 1)

@[reassoc]
theorem rightChartIso_hom_ι :
    (rightChartIso (k := k)).hom ≫ (ProjectiveLineComparison.chartOpen k 1).ι =
      ProjectiveLineComparison.chartImmersion k 1 := by
  simp only [rightChartIso, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
    Scheme.Hom.isoOpensRange_hom_ι]

/-- The original overlap projection expressed in the first polynomial coordinates. -/
def overlapToPolynomial :
    Spec (CommRingCat.of (ProjectiveLineComparison.overlapRing k)) ⟶
      Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (ProjectiveLineComparison.toOverlapLeft k)) ≫
    (ProjectiveLineComparison.chartPolynomialIso k 0).hom

/-- Both subsequent maps are original ambient open maps. -/
def overlapToFirst :
    Spec (CommRingCat.of (ProjectiveLineComparison.overlapRing k)) ⟶
      (firstOpen (k := k)).toScheme :=
  overlapToPolynomial ≫ (firstChartIso (k := k)).hom

def overlapToRight :
    Spec (CommRingCat.of (ProjectiveLineComparison.overlapRing k)) ⟶
      (ProjectiveLineComparison.chartOpen k 1).toScheme :=
  Spec.map (CommRingCat.ofHom (ProjectiveLineComparison.toOverlapRight k)) ≫
    (rightChartIso (k := k)).hom

/-- The overlap immersion into the original projective line. -/
def overlapMap :
    Spec (CommRingCat.of (ProjectiveLineComparison.overlapRing k)) ⟶ projectiveSpace k 1 :=
  overlapToFirst (k := k) ≫ (firstOpen (k := k)).ι

theorem overlapMap_left :
    overlapMap (k := k) =
      Spec.map (CommRingCat.ofHom (ProjectiveLineComparison.toOverlapLeft k)) ≫
        ProjectiveLineComparison.chartImmersion k 0 := by
  simp only [overlapMap, overlapToFirst, overlapToPolynomial, Category.assoc,
    firstChartIso_hom_ι, ProjectiveLineComparison.polynomialChartMap, Iso.hom_inv_id_assoc]

theorem overlapMap_right :
    overlapToRight (k := k) ≫ (ProjectiveLineComparison.chartOpen k 1).ι = overlapMap := by
  simp only [overlapToRight, Category.assoc, rightChartIso_hom_ι, overlapMap_left]
  apply (cancel_epi (ProjectiveLineComparison.overlapPullbackIso k).hom).mp
  simp only [← Category.assoc, ProjectiveLineComparison.overlapPullbackIso_hom_left,
    ProjectiveLineComparison.overlapPullbackIso_hom_right]
  exact pullback.condition.symm

instance overlapMap_isOpenImmersion : IsOpenImmersion (overlapMap (k := k)) := by
  have h : Spec.map (CommRingCat.ofHom (ProjectiveLineComparison.toOverlapLeft k)) =
      (ProjectiveLineComparison.overlapPullbackIso k).inv ≫
        pullback.fst (ProjectiveLineComparison.chartImmersion k 0)
          (ProjectiveLineComparison.chartImmersion k 1) := by
    rw [← ProjectiveLineComparison.overlapPullbackIso_hom_left, Iso.inv_hom_id_assoc]
  rw [overlapMap_left, h]
  infer_instance

/-- The overlap pullback of the first actual equation is the original coordinate. -/
theorem overlapToFirst_equation :
    (overlapToFirst (k := k)).appTop firstEquation =
      (Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).inv
        (ProjectiveLineComparison.toOverlapLeft k
          (ProjectiveLineComparison.coordinate k 0 1)) := by
  change (overlapToPolynomial (k := k)).appTop
    ((firstChartIso (k := k)).hom.appTop firstEquation) = _
  rw [firstChartIso_equation]
  have hc : (ProjectiveLineComparison.chartPolynomialIso k 0).hom.appTop
      (affineCoordinateEquation (k := k)) =
      (Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.chartRing k 0))).inv
        (ProjectiveLineComparison.coordinate k 0 1) := by
    change (Spec.map (CommRingCat.ofHom
        (ProjectiveLineComparison.firstChartPolynomialEquiv k).symm.toRingHom)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X) = _
    have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (ProjectiveLineComparison.firstChartPolynomialEquiv k).symm.toRingHom))
      (Polynomial.X : Polynomial k)
    have he : (ProjectiveLineComparison.firstChartPolynomialEquiv k).symm Polynomial.X =
        ProjectiveLineComparison.coordinate k 0 1 := by
      rw [← ProjectiveLineComparison.firstChartPolynomialEquiv_coordinate k,
        RingEquiv.symm_apply_apply]
    change (Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.chartRing k 0))).inv
      ((ProjectiveLineComparison.firstChartPolynomialEquiv k).symm Polynomial.X) = _ at h
    rw [he] at h
    exact h.symm
  change (Spec.map (CommRingCat.ofHom (ProjectiveLineComparison.toOverlapLeft k))).appTop
      ((ProjectiveLineComparison.chartPolynomialIso k 0).hom.appTop affineCoordinateEquation) = _
  rw [hc]
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (ProjectiveLineComparison.toOverlapLeft k)))
    (ProjectiveLineComparison.coordinate k 0 1)).symm

/-- The reciprocal is the original overlap function under Gamma-Spec. -/
def reciprocalSection : Γ(Spec (CommRingCat.of (ProjectiveLineComparison.overlapRing k)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).inv
    (ProjectiveLineComparison.toOverlapRight k (ProjectiveLineComparison.coordinate k 1 0))

/-- The first equation and its actual reciprocal multiply to the second equation. -/
theorem overlap_equation_transition :
    (overlapToRight (k := k)).appTop (1 : Γ((ProjectiveLineComparison.chartOpen k 1).toScheme, ⊤)) =
      reciprocalSection (k := k) * (overlapToFirst (k := k)).appTop firstEquation := by
  rw [map_one, overlapToFirst_equation]
  let l : ProjectiveLineComparison.overlapRing k :=
    ProjectiveLineComparison.toOverlapLeft k (ProjectiveLineComparison.coordinate k 0 1)
  let r : ProjectiveLineComparison.overlapRing k :=
    ProjectiveLineComparison.toOverlapRight k (ProjectiveLineComparison.coordinate k 1 0)
  let φ : ProjectiveLineComparison.overlapRing k →+*
      Γ(Spec (CommRingCat.of (ProjectiveLineComparison.overlapRing k)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).inv.hom
  have hm : r * l = 1 :=
    (mul_comm r l).trans (ProjectiveLineComparison.overlap_coordinates_mul k)
  change 1 = φ r * φ l
  exact (φ.map_one).symm.trans ((congrArg φ hm.symm).trans (φ.map_mul r l))

-- Share the literal transported frame with its abstract inclusion proof.
private def frameRefinementTransport
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (s : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (schemeModulePullback U.ι).obj (schemeKernelIdeal f))
    (g : Z ⟶ U.toScheme) (j : Z ⟶ Y) (h : g ≫ U.ι = j) :
    _root_.SheafOfModules.unit Z.ringCatSheaf ⟶
      (schemeModulePullback j).obj (schemeKernelIdeal f) :=
  kernelFrameRefinement f U.ι g s ≫
    (eqToIso (congrArg schemeModulePullback h)).hom.app (schemeKernelIdeal f)

-- Normalize the two existing equalities before specializing the schemes.
private theorem frameRefinementTransport_inclusion
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0)
    (s : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (schemeModulePullback U.ι).obj (schemeKernelIdeal f))
    (hs : s = localKernelGlobalEquation f U d hd)
    (g : Z ⟶ U.toScheme) (j : Z ⟶ Y) (h : g ≫ U.ι = j) :
    frameRefinementTransport f U s g j h ≫ pulledKernelInclusion f j =
      schemeScalarEnd (g.appTop d) := by
  subst s
  subst j
  simpa only [frameRefinementTransport, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id] using
    localKernelGlobalEquation_refinement_inclusion f U d hd g

/-- Both original local frames are now expressed in the same original kernel pullback. -/
def leftOverlapFrame :
    _root_.SheafOfModules.unit
      (Spec (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).ringCatSheaf ⟶
      (schemeModulePullback (overlapMap (k := k))).obj
        (schemeKernelIdeal (coordinatePoint (k := k))) :=
  kernelFrameRefinement coordinatePoint (firstOpen (k := k)).ι overlapToFirst
    (firstGlobalFrameIso (k := k)).hom

def rightOverlapFrame :
    _root_.SheafOfModules.unit
      (Spec (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).ringCatSheaf ⟶
      (schemeModulePullback (overlapMap (k := k))).obj
        (schemeKernelIdeal (coordinatePoint (k := k))) :=
  frameRefinementTransport (coordinatePoint (k := k)) (ProjectiveLineComparison.chartOpen k 1)
    (rightGlobalFrameIso (k := k)).hom (overlapToRight (k := k)) (overlapMap (k := k))
    (overlapMap_right (k := k))

instance leftOverlapFrame_isIso : IsIso (leftOverlapFrame (k := k)) := by
  unfold leftOverlapFrame kernelFrameRefinement schemeModulePullbackFrame
  infer_instance

instance rightOverlapFrame_isIso : IsIso (rightOverlapFrame (k := k)) := by
  unfold rightOverlapFrame frameRefinementTransport kernelFrameRefinement schemeModulePullbackFrame
  infer_instance

/-- The actual first overlap frame retains its equation after the original inclusion. -/
theorem leftOverlapFrame_inclusion :
    leftOverlapFrame (k := k) ≫ pulledKernelInclusion coordinatePoint overlapMap =
      schemeScalarEnd ((overlapToFirst (k := k)).appTop firstEquation) := by
  rw [leftOverlapFrame, firstGlobalFrameIso_hom]
  exact localKernelGlobalEquation_refinement_inclusion _ _ _ _ _

set_option maxHeartbeats 800000 in
/-- The same original inclusion sends the second frame to the actual unit equation. -/
theorem rightOverlapFrame_inclusion :
    rightOverlapFrame (k := k) ≫ pulledKernelInclusion coordinatePoint overlapMap =
      schemeScalarEnd ((overlapToRight (k := k)).appTop 1) := by
  exact frameRefinementTransport_inclusion
    (coordinatePoint (k := k)) (ProjectiveLineComparison.chartOpen k 1)
    1 (rightCoordinateEquation_eq_zero (k := k))
    (rightGlobalFrameIso (k := k)).hom (rightGlobalFrameIso_hom (k := k))
    (overlapToRight (k := k)) (overlapMap (k := k)) (overlapMap_right (k := k))

/-- The transition follows from the ORIGINAL kernel inclusion on the actual open overlap. -/
theorem overlapFrame_transition :
    rightOverlapFrame (k := k) = schemeScalarEnd (reciprocalSection (k := k)) ≫ leftOverlapFrame := by
  apply (pulledKernelInclusion_cancel coordinatePoint (overlapMap (k := k)) _ _).mp
  rw [rightOverlapFrame_inclusion, Category.assoc, leftOverlapFrame_inclusion,
    ← schemeScalarEnd_mul, ← overlap_equation_transition]

/-- The original coordinate transition is the negative Laurent generator. -/
theorem reciprocalSection_laurent :
    ProjectiveLineComparison.overlapLaurentEquiv k
      ((Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).hom
        (reciprocalSection (k := k))) = LaurentPolynomial.T (-1) := by
  change ProjectiveLineComparison.overlapLaurentEquiv k
      ((Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).inv
          (ProjectiveLineComparison.toOverlapRight k (ProjectiveLineComparison.coordinate k 1 0)))) = _
  rw [show (Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).inv
        (ProjectiveLineComparison.toOverlapRight k (ProjectiveLineComparison.coordinate k 1 0))) =
      ProjectiveLineComparison.toOverlapRight k (ProjectiveLineComparison.coordinate k 1 0) from
        ConcreteCategory.congr_hom
          (Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).inv_hom_id _]
  exact ProjectiveLineComparison.overlapLaurentEquiv_right_coordinate k

end KltDP.Examples.FrobeniusProjectiveCoordinateTransition
