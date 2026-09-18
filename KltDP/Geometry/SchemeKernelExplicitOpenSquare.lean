import KltDP.Geometry.SchemeKernelBaseChangeIsoLocus

/-!
# Actual kernels on a supplied open pullback square

The actual pullback comparison is composed with the existing normalized
open-base-change kernel comparison. Its inclusion is the original one.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.SchemeKernelExplicitOpenSquare

open SchemeKernelIdealIsoTransport SchemeKernelOpenBaseChange
open SchemeKernelBaseChangeIsoLocus

variable {Z X Z' W : Scheme.{u}} (a : Z' ⟶ W) (b : Z' ⟶ Z)
  (j : W ⟶ X) (f : Z ⟶ X) (H : IsPullback a b j f)
  {V : X.Opens} (e : W ≅ V.toScheme) (he : e.hom ≫ V.ι = j)

/-- The original square identifies the original local kernel with the
pullback of the original global kernel. -/
def iso : schemeKernelIdeal a ≅ (schemeModulePullback j).obj (schemeKernelIdeal f) :=
  schemeKernelIdealEqIso H.isoPullback_hom_fst.symm ≪≫
    schemeKernelPrecompIso H.isoPullback (pullback.fst j f) ≪≫
    kernelOpenBaseChangeIso f e j he

/-- Every comparison retains the original kernel inclusion. -/
theorem iso_inclusion :
    (iso a b j f H e he).hom ≫ pulledKernelInclusion f j = schemeKernelIdealι a := by
  simp only [iso, Iso.trans_hom, Category.assoc,
    kernelOpenBaseChangeIso_inclusion, schemeKernelPrecompIso_hom_ι,
    schemeKernelIdealEqIso_hom_ι]

end KltDP.Geometry.SchemeKernelExplicitOpenSquare

#print axioms KltDP.Geometry.SchemeKernelExplicitOpenSquare.iso_inclusion
