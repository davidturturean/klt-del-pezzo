import KltDP.Geometry.PrimeCurveClassPairing

/-!
# Actual line-bundle degree from an original curve-kernel pairing

Keep the original curve, closed immersion and kernel line. Apply the
proved symmetric pairing and kernel-class comparison before specializing
to a constructed surface, so the large surface is not unfolded repeatedly.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PrimeCurveClassPairing

open NormalProjectiveSurface

theorem restrictionDegree_eq_pairing_kernel_right
    {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
    (C : X.PrimeCurve) {Y : Scheme.{u}} (ι : Y ⟶ X.toScheme)
    [IsClosedImmersion ι] [IsReduced Y]
    (hC : (C : Set X.toScheme) = Set.range ι.base)
    (L : InvertibleSheaf X.toScheme) (hL : L.obj = schemeKernelIdeal ι)
    (M : InvertibleSheaf X.toScheme) (p : Additive X.toScheme.Pic)
    (hM : Additive.ofMul M.toPic = p) :
    C.restrictionDegree M = pairing X hregular p (-Additive.ofMul L.toPic) := by
  rw [pairing_symm, pairing_kernelLine_left X hregular C ι hC L hL p, ← hM]
  exact (C.picardRestrictionDegree_toPic M).symm

end KltDP.Geometry.PrimeCurveClassPairing

#print axioms KltDP.Geometry.PrimeCurveClassPairing.restrictionDegree_eq_pairing_kernel_right
