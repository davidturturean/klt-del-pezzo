import KltDP.Geometry.GluedIdealKernelTrivialization
import KltDP.Geometry.SchemeKernelOpenPullback

/-!
# Normalized frames of an original kernel on an affine ambient open

The original kernel ideal on an affine ambient open is the kernel of the
restricted section map after the canonical top-section comparison. Its proved
regular principal equation therefore gives the existing principal kernel frame,
followed by the existing comparison to the pullback of the original global kernel.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) (d : Γ(Y, U.1))
    (hker : f.ker.ideal U = Ideal.span {d})

/-- The literal restricted section map has the original kernel after top-section transport. -/
theorem schemeKernelAffineOpen_top :
    RingHom.ker (f ∣_ U.1).appTop.hom =
      (f.ker.ideal U).comap U.1.topIso.hom.hom := by
  have h : (f ∣_ U.1).appTop =
      (U.1.topIso.hom ≫ f.app U.1) ≫ (f ⁻¹ᵁ U.1).topIso.inv := by
    simpa only [Scheme.Γ_map_op, Category.assoc] using Γ_map_morphismRestrict f U.1
  have hinj : Function.Injective (f ⁻¹ᵁ U.1).topIso.inv.hom :=
    (f ⁻¹ᵁ U.1).topIso.symm.commRingCatIsoToRingEquiv.injective
  rw [h, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hinj,
    CommRingCat.hom_comp, ← RingHom.comap_ker, ← Scheme.Hom.ker_apply f U]

include hker in
/-- The same original equation generates that actual restricted kernel. -/
theorem schemeKernelAffineOpenEquation_kernel :
    RingHom.ker (f ∣_ U.1).appTop.hom = Ideal.span {gluedAffineEquation U d} := by
  rw [schemeKernelAffineOpen_top f U, hker]
  let e := U.1.topIso.commRingCatIsoToRingEquiv
  change (Ideal.span {d}).comap e.toRingHom = Ideal.span {e.symm d}
  rw [RingEquiv.toRingHom_eq_coe e, Ideal.comap_coe e, ← Ideal.map_symm e,
    Ideal.map_span, Set.image_singleton]

include hker in
/-- The original restricted inclusion kills the actual transported equation. -/
theorem schemeKernelAffineOpenEquation_zero :
    (f ∣_ U.1).appTop (gluedAffineEquation U d) = 0 := by
  apply RingHom.mem_ker.mp
  rw [schemeKernelAffineOpenEquation_kernel f U d hker]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The existing principal-kernel construction frames the original global kernel on this open. -/
def schemeKernelAffineOpenFrame (hregular : d ∈ nonZeroDivisors Γ(Y, U.1)) :
    _root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf ≅
      (schemeModulePullback U.1.ι).obj (schemeKernelIdeal f) := by
  letI : IsAffine U.1.toScheme := U.2
  letI : QuasiCompact (f ∣_ U.1) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U.1).flip inferInstance
  exact principalKernelSheafIso (f ∣_ U.1) (gluedAffineEquation U d)
      (schemeKernelAffineOpenEquation_zero f U d hker)
      (schemeKernelAffineOpenEquation_kernel f U d hker)
      (gluedAffineEquation_regular U d hregular) ≪≫
    localKernelToGlobalPullbackIso f U.1

/-- This is a frame over the actual structure module, normalized by the original equation. -/
theorem schemeKernelAffineOpenFrame_inclusion (hregular : d ∈ nonZeroDivisors Γ(Y, U.1)) :
    (schemeKernelAffineOpenFrame f U d hker hregular).hom ≫
        pulledKernelInclusion f U.1.ι = schemeScalarEnd (gluedAffineEquation U d) := by
  change (schemeKernelGenerator (f ∣_ U.1) (gluedAffineEquation U d)
      (schemeKernelAffineOpenEquation_zero f U d hker) ≫
        (localKernelToGlobalPullbackIso f U.1).hom) ≫ pulledKernelInclusion f U.1.ι = _
  rw [Category.assoc, localKernelToGlobalPullbackIso_inclusion,
    schemeKernelGenerator_comp_ι]

end KltDP.Geometry
