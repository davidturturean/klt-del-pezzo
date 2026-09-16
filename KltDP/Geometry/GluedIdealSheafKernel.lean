import KltDP.Geometry.GluedIdealKernel

/-!
# The kernel of the original glued ideal subscheme

The affine calculation in `GluedIdealKernel` retains the canonical change
from ambient sections to sections of the open subscheme. Cancelling that
section-ring isomorphism recovers the original affine ideal. Ideal-sheaf
extensionality then identifies the kernel of the actual glued inclusion.

This adapts the `ker_subschemeι_app` and `ker_subschemeι` conclusions in
newer Mathlib to the quotient gluing already constructed in this project.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- On each affine open, the actual glued inclusion has the original ideal
as the kernel of its ambient section map. -/
theorem ker_gluedTo_app (U : X.affineOpens) :
    RingHom.ker (I.gluedTo.app U.1).hom = I.ideal U := by
  apply Ideal.comap_injective_of_surjective U.1.topIso.hom.hom
    U.1.topIso.commRingCatIsoToRingEquiv.surjective
  have h : (I.gluedTo ∣_ U.1).appTop =
      (U.1.topIso.hom ≫ I.gluedTo.app U.1) ≫
        (I.gluedTo ⁻¹ᵁ U.1).topIso.inv := by
    simpa only [Scheme.Γ_map_op, Category.assoc] using
      Γ_map_morphismRestrict I.gluedTo U.1
  have hinj : Function.Injective (I.gluedTo ⁻¹ᵁ U.1).topIso.inv.hom :=
    (I.gluedTo ⁻¹ᵁ U.1).topIso.symm.commRingCatIsoToRingEquiv.injective
  have hc := I.ker_gluedTo_restrict_appTop U
  rw [h, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hinj,
    CommRingCat.hom_comp, ← RingHom.comap_ker] at hc
  exact hc

/-- The kernel ideal sheaf of the actual glued inclusion is the original
ideal sheaf, without any additional hypothesis on the scheme or ideal. -/
@[simp]
theorem ker_gluedTo : I.gluedTo.ker = I := by
  apply Scheme.IdealSheafData.ext
  funext U
  exact (Scheme.Hom.ker_apply I.gluedTo U).trans (I.ker_gluedTo_app U)

end AlgebraicGeometry.Scheme.IdealSheafData
