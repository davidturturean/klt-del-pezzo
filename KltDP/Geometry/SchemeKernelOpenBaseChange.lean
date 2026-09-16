import KltDP.Geometry.SchemeKernelIdealIsoTransport

/-!
# Kernel modules of base changes along open immersions

For a morphism `f : Z ⟶ X` and an open `V` of `X`, the kernel module of the base change
`pullback.fst V.ι f : pullback V.ι f ⟶ V` is the inverse image along `V.ι` of the kernel module of
`f` (`kernelRestrictBaseChangeIso`; the base change is the accepted restriction `f ∣_ V` up to the
pullback symmetry and `pullbackRestrictIsoRestrict`, and `localKernelToGlobalPullbackIso` compares
the kernel of the restriction with the pulled-back kernel).  More generally, for an open immersion
`j : W ⟶ X` factored as an isomorphism `e : W ≅ V` onto an open followed by `V.ι`, the kernel
module of `pullback.fst j f` is `j^*` of the kernel module of `f` (`kernelOpenBaseChangeIso`,
through the transport along isomorphisms of `SchemeKernelIdealIsoTransport`).  Consequences:
invertibility and the Picard class of the kernel line of the base change
(`isInvertible_kernel_openBaseChange`, `kernelLine_openBaseChange_toPic`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.SchemeKernelOpenBaseChange

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {Z X : Scheme.{u}} (f : Z ⟶ X)

/-- The base change along `V.ι` is the restriction `f ∣_ V`, up to the pullback symmetry and the
accepted `pullbackRestrictIsoRestrict`. -/
def baseChangeRestrictIso (V : X.Opens) : pullback V.ι f ≅ (f ⁻¹ᵁ V).toScheme :=
  pullbackSymmetry V.ι f ≪≫ pullbackRestrictIsoRestrict f V

theorem baseChangeRestrictIso_hom_restrict (V : X.Opens) :
    (baseChangeRestrictIso f V).hom ≫ (f ∣_ V) = pullback.fst V.ι f := by
  rw [baseChangeRestrictIso, Iso.trans_hom, Category.assoc,
    pullbackRestrictIsoRestrict_hom_morphismRestrict, pullbackSymmetry_hom_comp_snd]

/-- **The kernel module of the base change along `V.ι` is the inverse image of the kernel
module.** -/
def kernelRestrictBaseChangeIso (V : X.Opens) :
    schemeKernelIdeal (pullback.fst V.ι f) ≅
      (schemeModulePullback V.ι).obj (schemeKernelIdeal f) :=
  (schemeKernelIdealEqIso (baseChangeRestrictIso_hom_restrict f V)).symm ≪≫
    schemeKernelPrecompIso (baseChangeRestrictIso f V) (f ∣_ V) ≪≫
    localKernelToGlobalPullbackIso f V

variable {W : Scheme.{u}} {V : X.Opens} (e : W ≅ V.toScheme)

/-- The base change along `e.hom ≫ V.ι` is the base change along `V.ι`, transported by `e`. -/
def baseChangeCompIso :
    pullback V.ι f ≅ pullback (e.hom ≫ V.ι) f :=
  (asIso (pullback.snd e.hom (pullback.fst V.ι f))).symm ≪≫
    pullbackRightPullbackFstIso V.ι f e.hom

theorem baseChangeCompIso_hom_fst :
    (baseChangeCompIso f e).hom ≫ pullback.fst (e.hom ≫ V.ι) f =
      pullback.fst V.ι f ≫ (e.symm).hom := by
  rw [baseChangeCompIso, Iso.trans_hom, Category.assoc, pullbackRightPullbackFstIso_hom_fst,
    Iso.symm_hom, asIso_inv, pullback_inv_snd_fst_of_left_isIso, Iso.symm_hom, IsIso.Iso.inv_hom]

/-- **The kernel module of the base change along an open immersion `j = e.hom ≫ V.ι` is `j^*` of
the kernel module.** -/
def kernelOpenBaseChangeIso (j : W ⟶ X) (hj : e.hom ≫ V.ι = j) :
    schemeKernelIdeal (pullback.fst j f) ≅ (schemeModulePullback j).obj (schemeKernelIdeal f) := by
  subst hj
  exact schemeKernelTransportIso (pullback.fst V.ι f) e.symm (pullback.fst (e.hom ≫ V.ι) f)
      (baseChangeCompIso f e) (baseChangeCompIso_hom_fst f e) ≪≫
    (schemeModulePullback e.hom).mapIso (kernelRestrictBaseChangeIso f V) ≪≫
    (schemeModulePullbackCompIso e.hom V.ι).app (schemeKernelIdeal f)

/-- The kernel line of the base change is invertible when the kernel line of `f` is. -/
theorem isInvertible_kernel_openBaseChange (j : W ⟶ X) (hj : e.hom ≫ V.ι = j)
    (hf : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (schemeKernelIdeal f)) :
    KltDP.SheafOfModules.IsInvertible (R := W.ringCatSheaf)
      (schemeKernelIdeal (pullback.fst j f)) :=
  isInvertible_of_iso (schemeModulePullback_isInvertible j (schemeKernelIdeal f) hf)
    (kernelOpenBaseChangeIso f e j hj).symm

/-- **The Picard class of the kernel line of the base change is the pullback of the class of the
kernel line.** -/
theorem kernelLine_openBaseChange_toPic (j : W ⟶ X) (hj : e.hom ≫ V.ι = j)
    (hf : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (schemeKernelIdeal f))
    (hf' : KltDP.SheafOfModules.IsInvertible (R := W.ringCatSheaf)
      (schemeKernelIdeal (pullback.fst j f))) :
    (InvertibleSheaf.toPic (⟨schemeKernelIdeal (pullback.fst j f), hf'⟩ : InvertibleSheaf W)) =
      schemePicardPullbackHom j
        (InvertibleSheaf.toPic (⟨schemeKernelIdeal f, hf⟩ : InvertibleSheaf X)) :=
  toPic_eq_pullback_of_iso j ⟨schemeKernelIdeal f, hf⟩ ⟨schemeKernelIdeal (pullback.fst j f), hf'⟩
    (kernelOpenBaseChangeIso f e j hj)

/-- The additive form. -/
theorem neg_kernelLine_openBaseChange_toPic (j : W ⟶ X) (hj : e.hom ≫ V.ι = j)
    (hf : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (schemeKernelIdeal f))
    (hf' : KltDP.SheafOfModules.IsInvertible (R := W.ringCatSheaf)
      (schemeKernelIdeal (pullback.fst j f))) :
    -Additive.ofMul
        (InvertibleSheaf.toPic (⟨schemeKernelIdeal (pullback.fst j f), hf'⟩ : InvertibleSheaf W)) =
      (schemePicardPullbackHom j).toAdditive
        (-Additive.ofMul (InvertibleSheaf.toPic (⟨schemeKernelIdeal f, hf⟩ : InvertibleSheaf X))) := by
  rw [map_neg, kernelLine_openBaseChange_toPic f e j hj hf hf']
  rfl

end KltDP.Geometry.SchemeKernelOpenBaseChange
