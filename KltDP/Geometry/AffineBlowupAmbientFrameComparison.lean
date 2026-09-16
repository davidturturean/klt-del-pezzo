import KltDP.Geometry.SchemeKernelOpenPullback
import KltDP.Geometry.AffineBlowupExceptionalIntersection

/-!
# Actual original ideal frames on the common Rees ambient chart

The local original equation maps are transported into the pullback of
one global ideal kernel on the actual product chart. Their equality with
the original ratio is proved by its actual inclusion into the ambient
structure module and the already proved Rees equation identity.

The resulting equality may be pulled back to the exceptional quotient.
No injectivity after closed-immersion pullback is asserted. Comparing
these normalized kernel-pullback frames with the frozen conormal-chart
frames is a subsequent unit/composition comparison, not an assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.AffineBlowup

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

/-- The actual original Rees affine scheme and its affine open range,
through the same sections comparison used for the exceptional quotient. -/
def chartAmbientIso : Spec (CommRingCat.of (chartRing I a)) ≅
    (chartAffineOpen I a).1.toScheme :=
  (chartSectionSchemeIso I a).symm ≪≫ (chartAffineOpen I a).2.isoSpec.symm

/-- This isomorphism preserves the original ambient chart immersion. -/
theorem chartAmbientIso_hom_ι :
    (chartAmbientIso I a).hom ≫ (chartAffineOpen I a).1.ι = chartι I a := by
  simp only [chartAmbientIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change (chartSectionSchemeIso I a).inv ≫ (chartAffineOpen I a).2.fromSpec = _
  rw [← chartSectionSchemeIso_hom_fac, Iso.inv_hom_id_assoc]

/-- The actual chart pullback of its original equation section is the
original Rees equation, under the original Gamma-Spec comparison. -/
theorem chartAmbientIso_equation :
    (chartAmbientIso I a).hom.appTop
      (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a)) =
      (Scheme.ΓSpecIso (CommRingCat.of (chartRing I a))).inv (chartCenterEquation I a) := by
  let e := chartSectionSchemeIso I a
  have he : e.hom.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (chartRing I a))).inv (chartCenterEquation I a)) =
      (Scheme.ΓSpecIso Γ(scheme I, (chartAffineOpen I a).1)).inv
        (chartEquationSection I a) := by
    have h := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (Spec.preimage e.hom))
      (chartCenterEquation I a : chartRing I a)
    rw [Spec.map_preimage] at h
    exact h.symm
  change e.inv.appTop ((chartAffineOpen I a).2.isoSpec.inv.appTop
      (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))) = _
  rw [IsAffineOpen.isoSpec_inv_appTop]
  change e.inv.appTop ((Scheme.ΓSpecIso Γ(scheme I, (chartAffineOpen I a).1)).inv
    ((chartAffineOpen I a).1.topIso.hom
      ((chartAffineOpen I a).1.topIso.inv (chartEquationSection I a)))) = _
  have ht : (chartAffineOpen I a).1.topIso.hom
      ((chartAffineOpen I a).1.topIso.inv (chartEquationSection I a)) =
        chartEquationSection I a :=
    (chartAffineOpen I a).1.topIso.commRingCatIsoToRingEquiv.apply_symm_apply _
  rw [ht, ← he]
  have h := congrArg Scheme.Hom.appTop e.inv_hom_id
  simp only [Scheme.comp_appTop, Scheme.id_appTop] at h
  exact ConcreteCategory.congr_hom h _

/-- The actual first route from the product chart to its ambient open. -/
def overlapToLeftAmbient : Spec (CommRingCat.of (conormalOverlapRing I a b)) ⟶
    (chartAffineOpen I a).1.toScheme :=
  Spec.map (CommRingCat.ofHom (conormalOverlapLeft I a b)) ≫ (chartAmbientIso I a).hom

/-- The actual second route into the other ambient open. -/
def overlapToRightAmbient : Spec (CommRingCat.of (conormalOverlapRing I a b)) ⟶
    (chartAffineOpen I b).1.toScheme :=
  Spec.map (CommRingCat.ofHom (conormalOverlapRight I a b)) ≫ (chartAmbientIso I b).hom

/-- The original common ambient immersion into the actual Rees blowup. -/
def ambientOverlapMap : Spec (CommRingCat.of (conormalOverlapRing I a b)) ⟶ scheme I :=
  overlapToLeftAmbient I a b ≫ (chartAffineOpen I a).1.ι

/-- The two ambient-open routes give the same original blowup morphism. -/
theorem ambientOverlapMap_right :
    overlapToRightAmbient I a b ≫ (chartAffineOpen I b).1.ι = ambientOverlapMap I a b := by
  simp only [overlapToRightAmbient, ambientOverlapMap, overlapToLeftAmbient, Category.assoc,
    chartAmbientIso_hom_ι]
  exact (conormalOverlap_morphism_condition I a b).symm

instance ambientOverlapMap_isOpenImmersion : IsOpenImmersion (ambientOverlapMap I a b) := by
  have h : Spec.map (CommRingCat.ofHom (conormalOverlapLeft I a b)) =
      (conormalOverlapIso I a b).inv ≫ pullback.fst (chartι I a) (chartι I b) := by
    rw [← conormalOverlapIso_hom_left, Iso.inv_hom_id_assoc]
  change IsOpenImmersion
    ((Spec.map (CommRingCat.ofHom (conormalOverlapLeft I a b)) ≫
      (chartAmbientIso I a).hom) ≫ (chartAffineOpen I a).1.ι)
  rw [h]
  infer_instance

/-- The original overlap ratio as an actual global function on this
same ambient scheme, before passing to the exceptional quotient. -/
def ambientOverlapRatioSection :
    Γ(Spec (CommRingCat.of (conormalOverlapRing I a b)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (conormalOverlapRing I a b))).inv
    (conormalOverlapRatio I a b)

/-- Original first local equation restricted to the common ambient chart. -/
theorem overlapToLeftAmbient_equation :
    (overlapToLeftAmbient I a b).appTop
      (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a)) =
      (Scheme.ΓSpecIso (CommRingCat.of (conormalOverlapRing I a b))).inv
        (conormalOverlapEquationLeft I a b) := by
  change (Spec.map (CommRingCat.ofHom (conormalOverlapLeft I a b))).appTop
      ((chartAmbientIso I a).hom.appTop
        (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))) = _
  rw [chartAmbientIso_equation]
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (conormalOverlapLeft I a b)))
    (chartCenterEquation I a : chartRing I a)
  change (Scheme.ΓSpecIso (CommRingCat.of (conormalOverlapRing I a b))).inv
      (conormalOverlapLeft I a b (chartBaseMap I a (a : R))) = _ at h
  rw [conormalOverlapLeft_baseMap] at h
  exact h.symm

/-- Original second local equation restricted to this same ambient chart. -/
theorem overlapToRightAmbient_equation :
    (overlapToRightAmbient I a b).appTop
      (gluedAffineEquation (chartAffineOpen I b) (chartEquationSection I b)) =
      (Scheme.ΓSpecIso (CommRingCat.of (conormalOverlapRing I a b))).inv
        (conormalOverlapEquationRight I a b) := by
  change (Spec.map (CommRingCat.ofHom (conormalOverlapRight I a b))).appTop
      ((chartAmbientIso I b).hom.appTop
        (gluedAffineEquation (chartAffineOpen I b) (chartEquationSection I b))) = _
  rw [chartAmbientIso_equation]
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (conormalOverlapRight I a b)))
    (chartCenterEquation I b : chartRing I b)
  change (Scheme.ΓSpecIso (CommRingCat.of (conormalOverlapRing I a b))).inv
      (conormalOverlapRight I a b (chartBaseMap I b (b : R))) = _ at h
  rw [conormalOverlapRight_baseMap] at h
  exact h.symm

/-- The actual equation identity holds in the original common ambient
section ring. It is derived from the Rees relation, not supplied as data. -/
theorem ambientOverlap_equation_transition :
    (overlapToRightAmbient I a b).appTop
        (gluedAffineEquation (chartAffineOpen I b) (chartEquationSection I b)) =
      ambientOverlapRatioSection I a b *
        (overlapToLeftAmbient I a b).appTop
          (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a)) := by
  rw [overlapToRightAmbient_equation, overlapToLeftAmbient_equation]
  change (Scheme.ΓSpecIso (CommRingCat.of (conormalOverlapRing I a b))).inv
      (conormalOverlapEquationRight I a b : conormalOverlapRing I a b) = _
  rw [conormalOverlap_equation_transition, map_mul]
  rfl

/-- The first original equation map now takes values in the pullback of
one actual global kernel on the common ambient chart. -/
def leftAmbientKernelFrame :
    _root_.SheafOfModules.unit
      (Spec (CommRingCat.of (conormalOverlapRing I a b))).ringCatSheaf ⟶
      (schemeModulePullback (ambientOverlapMap I a b)).obj
        (schemeKernelIdeal (exceptionalIdeal I).gluedTo) :=
  kernelFrameRefinement (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1.ι
    (overlapToLeftAmbient I a b)
    (localKernelGlobalEquation (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1
      (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))
      (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I a)
        (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a)))

-- Share this exact transported map between the concrete frame and its
-- abstract normalization theorem, including both original equality proofs.
private def localEquationRefinementTransport
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0)
    (g : Z ⟶ U.toScheme) (j : Z ⟶ Y) (h : g ≫ U.ι = j) :
    _root_.SheafOfModules.unit Z.ringCatSheaf ⟶
      (schemeModulePullback j).obj (schemeKernelIdeal f) :=
  kernelFrameRefinement f U.ι g (localKernelGlobalEquation f U d hd) ≫
    (eqToIso (congrArg schemeModulePullback h)).hom.app (schemeKernelIdeal f)

/-- The original second equation map has that same actual global kernel
pullback as target, using the proved ambient-morphism equality. -/
def rightAmbientKernelFrame :
    _root_.SheafOfModules.unit
      (Spec (CommRingCat.of (conormalOverlapRing I a b))).ringCatSheaf ⟶
      (schemeModulePullback (ambientOverlapMap I a b)).obj
        (schemeKernelIdeal (exceptionalIdeal I).gluedTo) :=
  localEquationRefinementTransport (exceptionalIdeal I).gluedTo (chartAffineOpen I b).1
    (gluedAffineEquation (chartAffineOpen I b) (chartEquationSection I b))
    (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I b)
      (chartEquationSection I b) (exceptionalIdeal_chartEquationSection I b))
    (overlapToRightAmbient I a b) (ambientOverlapMap I a b)
    (ambientOverlapMap_right I a b)

/-- Actual regular principal generation makes the original local kernel
map an isomorphism; this property is derived from the Rees equation. -/
private theorem chartKernelGlobalEquation_isIso (a : I) :
    IsIso (localKernelGlobalEquation (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1
      (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))
      (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I a)
        (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a))) := by
  unfold localKernelGlobalEquation
  rw [← gluedAffineKernelIso_hom (exceptionalIdeal I) (chartAffineOpen I a)
    (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a)
    (chartEquationSection_regular I a)]
  infer_instance

/-- The first original map is an actual frame of the common ideal pullback. -/
instance leftAmbientKernelFrame_isIso : IsIso (leftAmbientKernelFrame I a b) := by
  letI := chartKernelGlobalEquation_isIso I a
  unfold leftAmbientKernelFrame kernelFrameRefinement schemeModulePullbackFrame
  infer_instance

/-- The second original map is also a frame of that same actual module. -/
instance rightAmbientKernelFrame_isIso : IsIso (rightAmbientKernelFrame I a b) := by
  letI := chartKernelGlobalEquation_isIso I b
  unfold rightAmbientKernelFrame localEquationRefinementTransport
    kernelFrameRefinement schemeModulePullbackFrame
  infer_instance

/-- Inclusion of the actual first frame is its original local multiplication map. -/
theorem leftAmbientKernelFrame_inclusion :
    leftAmbientKernelFrame I a b ≫
        pulledKernelInclusion (exceptionalIdeal I).gluedTo (ambientOverlapMap I a b) =
      schemeScalarEnd ((overlapToLeftAmbient I a b).appTop
        (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))) :=
  localKernelGlobalEquation_refinement_inclusion _ _ _ _ _

-- Normalize equality transport while the schemes and local equation remain
-- abstract, so the concrete Rees application is one theorem instantiation.
private theorem localEquationRefinement_transport_inclusion
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0)
    (g : Z ⟶ U.toScheme) (j : Z ⟶ Y) (h : g ≫ U.ι = j) :
    localEquationRefinementTransport f U d hd g j h ≫
      pulledKernelInclusion f j = schemeScalarEnd (g.appTop d) := by
  subst j
  simpa only [localEquationRefinementTransport, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id] using
    localKernelGlobalEquation_refinement_inclusion f U d hd g

set_option maxHeartbeats 800000 in
/-- The same inclusion normalization for the original second frame. -/
theorem rightAmbientKernelFrame_inclusion :
    rightAmbientKernelFrame I a b ≫
        pulledKernelInclusion (exceptionalIdeal I).gluedTo (ambientOverlapMap I a b) =
      schemeScalarEnd ((overlapToRightAmbient I a b).appTop
        (gluedAffineEquation (chartAffineOpen I b) (chartEquationSection I b))) := by
  exact localEquationRefinement_transport_inclusion (exceptionalIdeal I).gluedTo
    (chartAffineOpen I b).1
    (gluedAffineEquation (chartAffineOpen I b) (chartEquationSection I b))
    (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I b)
      (chartEquationSection I b) (exceptionalIdeal_chartEquationSection I b))
    (overlapToRightAmbient I a b) (ambientOverlapMap I a b)
    (ambientOverlapMap_right I a b)

/-- The actual original ideal-frame transition on the common ambient
chart is exactly the original Rees ratio. -/
theorem ambientKernelFrame_transition :
    rightAmbientKernelFrame I a b =
      schemeScalarEnd (ambientOverlapRatioSection I a b) ≫ leftAmbientKernelFrame I a b := by
  apply (pulledKernelInclusion_cancel (exceptionalIdeal I).gluedTo
    (ambientOverlapMap I a b) _ _).mp
  rw [rightAmbientKernelFrame_inclusion, Category.assoc,
    leftAmbientKernelFrame_inclusion, ← schemeScalarEnd_mul,
    ← ambientOverlap_equation_transition]

/-- Any further actual pullback preserves this already proved frame
identity. No cancellation after that pullback is needed or assumed. -/
theorem ambientKernelFrame_transition_pullback {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of (conormalOverlapRing I a b))) :
    schemeModulePullbackFrame g (rightAmbientKernelFrame I a b) =
      schemeScalarEnd (g.appTop (ambientOverlapRatioSection I a b)) ≫
        schemeModulePullbackFrame g (leftAmbientKernelFrame I a b) := by
  rw [ambientKernelFrame_transition]
  simp only [schemeModulePullbackFrame, Functor.map_comp]
  rw [← Category.assoc, schemeModulePullbackUnitIso_inv_scalar, Category.assoc]

end KltDP.Geometry.AffineBlowup
