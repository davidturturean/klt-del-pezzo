import KltDP.Geometry.PointBlowupCenterFiber
import KltDP.Geometry.AffineBlowupExceptionalInvertible
import KltDP.Geometry.GluedIdealSheafKernel
import KltDP.Geometry.SchemeConormalSourceIso
import KltDP.Geometry.SchemeConormalOpenImmersion
import KltDP.Geometry.SchemeKernelOpenPullback

/-!
# The actual exceptional ideal on the whole point blowup

The original affine exceptional scheme is the entire center fiber, with
its inclusion preserved. Its proved regular Rees-chart equations therefore
give regular equations for the original whole fiber's kernel on the affine
blowup piece. On the unchanged complement the actual fiber source is empty,
so the kernel is framed by one. These actual opens cover the whole scheme.

The resulting invertible sheaf has literally the original center-fiber
kernel as its object. Its affine comparison and complement frame preserve
the original ideal inclusions. No regularity, invertibility, class formula,
or determinant identity is supplied as a new hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupGluing

open SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

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

private def regularKernelOpenIso {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) (d : Γ(Y, U.1))
    (hker : f.ker.ideal U = Ideal.span {d})
    (hregular : d ∈ nonZeroDivisors Γ(Y, U.1)) :
    _root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf ≅
      schemeKernelIdeal (f ∣_ U.1) := by
  let e := U.1.topIso.commRingCatIsoToRingEquiv
  have htop : RingHom.ker (f ∣_ U.1).appTop.hom = Ideal.span {e.symm d} := by
    rw [kernel_restrict_top f U, hker]
    change (Ideal.span {d}).comap e.toRingHom = Ideal.span {e.symm d}
    rw [RingEquiv.toRingHom_eq_coe e, Ideal.comap_coe e, ← Ideal.map_symm e,
      Ideal.map_span, Set.image_singleton]
  have hz : (f ∣_ U.1).appTop (e.symm d) = 0 := by
    apply RingHom.mem_ker.mp
    rw [htop]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hr : e.symm d ∈ nonZeroDivisors Γ(U.1.toScheme, ⊤) := by
    apply mem_nonZeroDivisors_of_injective (f := e) e.injective
    simpa only [e.apply_symm_apply] using hregular
  letI : IsAffine U.1.toScheme := U.2
  letI : QuasiCompact (f ∣_ U.1) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U.1).flip inferInstance
  exact principalKernelSheafIso (f ∣_ U.1) (e.symm d) hz htop hr

private theorem emptyKernelGenerator_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEmpty X] :
    IsIso (schemeKernelGenerator f 1 (Subsingleton.elim _ _)) := by
  apply KltDP.SheafOfModules.isIso_of_bijective_on_basis
    (B := fun U : Y.Opens => U) _
    (Opens.isBasis_iff_nbhd.mpr (fun {U x} hx => ⟨U, ⟨U, rfl⟩, hx, le_rfl⟩))
  intro U
  apply schemeKernelGenerator_app_bijective f 1 (Subsingleton.elim _ _) U
  · rw [map_one, Ideal.span_singleton_one]
    apply top_unique
    intro r _
    exact Subsingleton.elim _ _
  · rw [map_one]
    exact one_mem _

private theorem kernel_eqToIso_hom_ι {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (eqToIso (congrArg schemeKernelIdeal h)).hom ≫ schemeKernelIdealι g =
      schemeKernelIdealι f := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))

/-- The original source-fiber isomorphism identifies the two actual ambient kernels. -/
def globalCenterFiberKernelIso :
    schemeKernelIdeal (globalCenterFiberι j q hclosed) ≅
      schemeKernelIdeal
        (AffineBlowup.exceptionalι q.asIdeal ≫ affineBlowupι j q hclosed) :=
  (schemeKernelPrecompIso (exceptionalGlobalFiberIso j q hclosed)
    (globalCenterFiberι j q hclosed)).symm ≪≫
      eqToIso (congrArg schemeKernelIdeal (exceptionalGlobalFiberIso_hom_ι j q hclosed))

theorem globalCenterFiberKernelIso_hom_ι :
    (globalCenterFiberKernelIso j q hclosed).hom ≫
        schemeKernelIdealι
          (AffineBlowup.exceptionalι q.asIdeal ≫ affineBlowupι j q hclosed) =
      schemeKernelIdealι (globalCenterFiberι j q hclosed) := by
  rw [globalCenterFiberKernelIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    kernel_eqToIso_hom_ι (exceptionalGlobalFiberIso_hom_ι j q hclosed),
    schemeKernelPrecompIso_inv_ι]

/-- Pullback to the original affine blowup recovers its original exceptional ideal module. -/
def globalCenterFiberIdealAffineIso :
    (schemeModulePullback (affineBlowupι j q hclosed)).obj
        (schemeKernelIdeal (globalCenterFiberι j q hclosed)) ≅
      AffineBlowup.exceptionalIdealModule q.asIdeal :=
  (schemeModulePullback (affineBlowupι j q hclosed)).mapIso
      (globalCenterFiberKernelIso j q hclosed) ≪≫
    schemeKernelPostcompOpenIso (AffineBlowup.exceptionalι q.asIdeal)
      (affineBlowupι j q hclosed)

/-- The affine comparison is normalized by the original inclusion into the structure module. -/
theorem globalCenterFiberIdealAffineIso_hom_ι :
    (globalCenterFiberIdealAffineIso j q hclosed).hom ≫
        schemeKernelIdealι (AffineBlowup.exceptionalι q.asIdeal) =
      pulledKernelInclusion (globalCenterFiberι j q hclosed) (affineBlowupι j q hclosed) := by
  calc
    _ = (schemeModulePullback (affineBlowupι j q hclosed)).map
        ((globalCenterFiberKernelIso j q hclosed).hom ≫
          schemeKernelIdealι
            (AffineBlowup.exceptionalι q.asIdeal ≫ affineBlowupι j q hclosed)) ≫
        (schemeModulePullbackUnitIso (affineBlowupι j q hclosed)).hom := by
      simp only [globalCenterFiberIdealAffineIso, Iso.trans_hom, Functor.mapIso_hom,
        Functor.map_comp, Category.assoc, schemeKernelPostcompOpenIso_hom_ι]
    _ = _ := by rw [globalCenterFiberKernelIso_hom_ι]; rfl

/-- The original affine exceptional square is an actual pullback of the entire fiber. -/
theorem exceptionalGlobalFiber_isPullback :
    IsPullback (AffineBlowup.exceptionalι q.asIdeal)
      (exceptionalGlobalFiberIso j q hclosed).hom
      (affineBlowupι j q hclosed) (globalCenterFiberι j q hclosed) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (exceptionalGlobalFiberIso_hom_ι j q hclosed).symm
    (fun s => s.snd ≫ (exceptionalGlobalFiberIso j q hclosed).inv)
    (fun s => ?_) (fun s => ?_) (fun s m _ hm => ?_))
  · apply (cancel_mono (affineBlowupι j q hclosed)).mp
    simp only [Category.assoc]
    rw [← exceptionalGlobalFiberIso_hom_ι, Iso.inv_hom_id_assoc]
    exact s.condition.symm
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · apply (cancel_mono (exceptionalGlobalFiberIso j q hclosed).hom).mp
    rw [hm, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual affine exceptional ideal gives the whole fiber ideal through the original appIso. -/
theorem globalCenterFiber_ideal_affine (U : (AffineBlowup.scheme q.asIdeal).affineOpens) :
    (AffineBlowup.exceptionalIdeal q.asIdeal).ideal U =
      ((globalCenterFiberι j q hclosed).ker.ideal
        ⟨affineBlowupι j q hclosed ''ᵁ U, U.2.image_of_isOpenImmersion _⟩).comap
          ((affineBlowupι j q hclosed).appIso U).inv.hom := by
  have h := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (globalCenterFiberι j q hclosed) (AffineBlowup.exceptionalι q.asIdeal)
    (exceptionalGlobalFiberIso j q hclosed).hom (affineBlowupι j q hclosed)
    (exceptionalGlobalFiber_isPullback j q hclosed) U
  simpa only [AffineBlowup.exceptionalι, Scheme.IdealSheafData.ker_gluedTo] using h

/-- The unchanged open is the inverse image of the original center complement. -/
def exceptionalComplementOpen : (scheme j q hclosed).Opens :=
  projection j q hclosed ⁻¹ᵁ puncture j q hclosed

instance globalCenterFiber_complement_isEmpty :
    IsEmpty ((globalCenterFiberι j q hclosed ⁻¹ᵁ exceptionalComplementOpen j q hclosed).toScheme) := by
  refine ⟨fun z => ?_⟩
  have hz : (globalCenterFiberι j q hclosed).base z.val ∈
      Set.range (globalCenterFiberι j q hclosed).base := ⟨z.val, rfl⟩
  rw [range_globalCenterFiberι] at hz
  have hn : (projection j q hclosed).base ((globalCenterFiberι j q hclosed).base z.val) ≠
      j.base q := z.property
  exact hn hz

/-- The actual original fiber kernel is framed by one on the unchanged complement. -/
def globalCenterFiberComplementFrame :
    _root_.SheafOfModules.unit (exceptionalComplementOpen j q hclosed).toScheme.ringCatSheaf ≅
      (schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).obj
        (schemeKernelIdeal (globalCenterFiberι j q hclosed)) := by
  let f := globalCenterFiberι j q hclosed ∣_ exceptionalComplementOpen j q hclosed
  letI := emptyKernelGenerator_isIso f
  exact asIso (schemeKernelGenerator f 1 (Subsingleton.elim _ _)) ≪≫
    localKernelToGlobalPullbackIso (globalCenterFiberι j q hclosed)
      (exceptionalComplementOpen j q hclosed)

theorem globalCenterFiberComplementFrame_inclusion :
    (globalCenterFiberComplementFrame j q hclosed).hom ≫
        pulledKernelInclusion (globalCenterFiberι j q hclosed)
          (exceptionalComplementOpen j q hclosed).ι =
      (schemeScalarEnd (Y := (exceptionalComplementOpen j q hclosed).toScheme) 1 :
        _root_.SheafOfModules.unit
            (exceptionalComplementOpen j q hclosed).toScheme.ringCatSheaf ⟶
          _root_.SheafOfModules.unit
            (exceptionalComplementOpen j q hclosed).toScheme.ringCatSheaf) :=
  localKernelGlobalEquation_inclusion (globalCenterFiberι j q hclosed)
    (exceptionalComplementOpen j q hclosed) 1 (Subsingleton.elim _ _)

/-- Regular Rees equations and the actual empty-complement frame prove ambient invertibility. -/
theorem globalCenterFiberIdeal_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (scheme j q hclosed).ringCatSheaf)
      (schemeKernelIdeal (globalCenterFiberι j q hclosed)) := by
  apply isInvertible_of_openCharts (X := scheme j q hclosed)
    (schemeKernelIdeal (globalCenterFiberι j q hclosed))
  intro x
  rcases pieces_cover j q hclosed x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · obtain ⟨U, ha, d, hd, hr⟩ :=
      AffineBlowup.exceptionalIdeal_locallyPrincipalRegular q.asIdeal a
    let V : (scheme j q hclosed).affineOpens :=
      ⟨affineBlowupι j q hclosed ''ᵁ U, U.2.image_of_isOpenImmersion _⟩
    let e := ((affineBlowupι j q hclosed).appIso U).symm.commRingCatIsoToRingEquiv
    have he : (globalCenterFiberι j q hclosed).ker.ideal V = Ideal.span {e d} := by
      have h := globalCenterFiber_ideal_affine j q hclosed U
      change (AffineBlowup.exceptionalIdeal q.asIdeal).ideal U = Ideal.span {d} at hd
      rw [hd] at h
      change Ideal.span {d} =
        ((globalCenterFiberι j q hclosed).ker.ideal V).comap e.toRingHom at h
      calc
        _ = (((globalCenterFiberι j q hclosed).ker.ideal V).comap e.toRingHom).map
            e.toRingHom := (Ideal.map_comap_of_surjective e.toRingHom e.surjective _).symm
        _ = (Ideal.span {d}).map e.toRingHom := by rw [← h]
        _ = _ := by
          rw [Ideal.map_span, Set.image_singleton]
          rfl
    have hreg : e d ∈ nonZeroDivisors Γ(scheme j q hclosed, V.1) := by
      apply mem_nonZeroDivisors_of_injective (f := e.symm) e.symm.injective
      simpa only [e.symm_apply_apply] using hr
    exact ⟨V.1, ⟨a, ha, rfl⟩, ⟨regularKernelOpenIso
      (globalCenterFiberι j q hclosed) V (e d) he hreg ≪≫
        (schemeKernelRestrictionIso (globalCenterFiberι j q hclosed) V.1).symm⟩⟩
  · refine ⟨exceptionalComplementOpen j q hclosed, ?_,
      ⟨globalCenterFiberComplementFrame j q hclosed ≪≫
        ((restrictionIsoPullback (exceptionalComplementOpen j q hclosed).ι).app _).symm⟩⟩
    change (complementι j q hclosed ≫ projection j q hclosed).base b ∈ puncture j q hclosed
    rw [complementι_projection]
    exact b.property

/-- The ambient exceptional line has literally the original whole center-fiber kernel. -/
def globalCenterFiberIdealLine : InvertibleSheaf (scheme j q hclosed) :=
  ⟨schemeKernelIdeal (globalCenterFiberι j q hclosed),
    globalCenterFiberIdeal_isInvertible j q hclosed⟩

theorem globalCenterFiberIdealLine_obj :
    (globalCenterFiberIdealLine j q hclosed).obj =
      schemeKernelIdeal (globalCenterFiberι j q hclosed) := rfl

end KltDP.Geometry.PointBlowupGluing
