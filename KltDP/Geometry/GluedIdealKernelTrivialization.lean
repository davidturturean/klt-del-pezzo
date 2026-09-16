import KltDP.Geometry.GluedIdealKernel
import KltDP.Geometry.PrincipalKernelSheaf
import KltDP.Geometry.InvertibleSheaf

/-!
# Actual regular quotient-chart kernel and conormal trivializations

For a genuine affine open on which an actual ideal sheaf has a regular
principal equation, the actual restricted closed immersion has a
trivial kernel module and a trivial conormal module. Both isomorphisms
are constructed from that equation and the original maps.

These are sheaves on the ambient affine open and its inverse-image closed
scheme, respectively. Comparing them with restrictions of the global
kernel and global conormal sheaves is a separate base-change adapter.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
  (d : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {d})

/-- The chosen actual local equation in the section ring of the open
subscheme, using its canonical top-section isomorphism. -/
def gluedAffineEquation : Γ(U.1.toScheme, ⊤) := U.1.topIso.inv d

include hI in
/-- The actual restricted structural section map has the transported
principal ideal as its kernel. -/
theorem gluedAffineEquation_kernel :
    RingHom.ker (I.gluedTo ∣_ U.1).appTop.hom =
      Ideal.span {gluedAffineEquation U d} := by
  rw [I.ker_gluedTo_restrict_appTop U, hI]
  let e := U.1.topIso.commRingCatIsoToRingEquiv
  change (Ideal.span {d}).comap (e : Γ(U.1.toScheme, ⊤) →+* Γ(X, U.1)) =
    Ideal.span {e.symm d}
  rw [Ideal.comap_coe e, ← Ideal.map_symm e, Ideal.map_span, Set.image_singleton]

include hI in
/-- The local equation is killed by the actual restricted inclusion. -/
theorem gluedAffineEquation_eq_zero :
    (I.gluedTo ∣_ U.1).appTop (gluedAffineEquation U d) = 0 := by
  apply RingHom.mem_ker.mp
  rw [gluedAffineEquation_kernel I U d hI]
  exact Ideal.subset_span (Set.mem_singleton _)

variable (hregular : d ∈ nonZeroDivisors Γ(X, U.1))

include hregular in
/-- Regularity is transported through the original section-ring isomorphism. -/
theorem gluedAffineEquation_regular :
    gluedAffineEquation U d ∈ nonZeroDivisors Γ(U.1.toScheme, ⊤) := by
  let e := U.1.topIso.commRingCatIsoToRingEquiv
  apply mem_nonZeroDivisors_of_injective (f := e) e.injective
  change e (e.symm d) ∈ nonZeroDivisors Γ(X, U.1)
  simpa only [e.apply_symm_apply] using hregular

/-- The chosen regular equation gives an actual trivialization of the
kernel module of the restricted closed immersion. -/
def gluedAffineKernelIso :
    _root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf ≅
      schemeKernelIdeal (I.gluedTo ∣_ U.1) := by
  letI : IsAffine U.1.toScheme := U.2
  letI : IsClosedImmersion (I.gluedTo ∣_ U.1) :=
    IsLocalAtTarget.restrict (P := @IsClosedImmersion) I.gluedTo_isClosedImmersion U.1
  exact principalKernelSheafIso (I.gluedTo ∣_ U.1) (gluedAffineEquation U d)
    (gluedAffineEquation_eq_zero I U d hI)
    (gluedAffineEquation_kernel I U d hI)
    (gluedAffineEquation_regular U d hregular)

/-- The kernel trivialization is the actual lifted multiplication map. -/
theorem gluedAffineKernelIso_hom :
    (gluedAffineKernelIso I U d hI hregular).hom =
      schemeKernelGenerator (I.gluedTo ∣_ U.1) (gluedAffineEquation U d)
        (gluedAffineEquation_eq_zero I U d hI) := rfl

/-- Pulling back the constructed kernel trivialization gives an actual
trivialization of the conormal sheaf of the restricted closed immersion. -/
def gluedAffineConormalIso :
    _root_.SheafOfModules.unit (I.gluedTo ⁻¹ᵁ U.1).toScheme.ringCatSheaf ≅
      schemeConormalSheaf (I.gluedTo ∣_ U.1) :=
  (schemeModulePullbackUnitIso (I.gluedTo ∣_ U.1)).symm ≪≫
    (schemeModulePullback (I.gluedTo ∣_ U.1)).mapIso
      (gluedAffineKernelIso I U d hI hregular)

include hI hregular in
/-- The actual local kernel sheaf has rank one, by the constructed
structure-module isomorphism and the established local-basis criterion. -/
theorem gluedAffineKernel_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := U.1.toScheme.ringCatSheaf)
      (schemeKernelIdeal (I.gluedTo ∣_ U.1)) :=
  KltDP.SheafOfModules.IsInvertible.of_iso
    (R := U.1.toScheme.ringCatSheaf)
    (M := _root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf)
    (N := schemeKernelIdeal (I.gluedTo ∣_ U.1))
    (gluedAffineKernelIso I U d hI hregular)

include hI hregular in
/-- The actual local conormal sheaf has rank one. No conormal
invertibility is supplied as data. -/
theorem gluedAffineConormal_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (I.gluedTo ⁻¹ᵁ U.1).toScheme.ringCatSheaf)
      (schemeConormalSheaf (I.gluedTo ∣_ U.1)) :=
  KltDP.SheafOfModules.IsInvertible.of_iso
    (R := (I.gluedTo ⁻¹ᵁ U.1).toScheme.ringCatSheaf)
    (M := _root_.SheafOfModules.unit (I.gluedTo ⁻¹ᵁ U.1).toScheme.ringCatSheaf)
    (N := schemeConormalSheaf (I.gluedTo ∣_ U.1))
    (gluedAffineConormalIso I U d hI hregular)

end KltDP.Geometry
