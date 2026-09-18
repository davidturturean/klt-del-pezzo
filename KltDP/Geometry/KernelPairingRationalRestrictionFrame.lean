import KltDP.Geometry.RationalProjectiveLineDegreeZero
import KltDP.Geometry.PrimeCurveClassPairing
import KltDP.Geometry.PrimeCurveOfClosedImmersion
import KltDP.Geometry.PrimeCurveInclusionLift

/-!
# Frames of original rational-curve restrictions from kernel pairings

The canonical prime-curve scheme and an original reduced closed immersion
are related by the existing inclusion lift. Euler transport identifies the
restriction degrees without replacing the original inclusion. On a rational
curve over the field, a zero kernel pairing therefore gives a frame of the
actual pulled-back invertible sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

open NormalProjectiveSurface ModuleCohomology

namespace PrimeCurveOriginalRestriction

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}
  (C : X.PrimeCurve) {Y : Scheme.{u}} (ι : Y ⟶ X.toScheme)
  [IsClosedImmersion ι] [AlgebraicGeometry.IsReduced Y]
  (hC : (C : Set X.toScheme) = Set.range ι.base)

include hC in
/-- The degree on the original closed curve is its intrinsic prime-curve
restriction degree, through the existing inclusion-lift isomorphism. -/
theorem eulerDegree_pullback_eq_restrictionDegree (M : InvertibleSheaf X.toScheme) :
    RationalTreePicard.eulerDegree (ι ≫ X.structureMorphism)
        (pullbackInvertibleSheaf ι M) = C.restrictionDegree M := by
  let e : Y ≅ C.toScheme := asIso (PrimeCurveInclusionLift.lift C ι hC)
  have he : e.hom ≫ C.toSpec = ι ≫ X.structureMorphism := by
    change PrimeCurveInclusionLift.lift C ι hC ≫
      (C.inclusion ≫ X.structureMorphism) = _
    rw [← Category.assoc, PrimeCurveInclusionLift.lift_inclusion]
  unfold RationalTreePicard.eulerDegree
  rw [eulerCharacteristic_eq_pullback_inv e (ι ≫ X.structureMorphism) C.toSpec he
      (pullbackInvertibleSheaf ι M).obj,
    eulerCharacteristic_unit_eq e (ι ≫ X.structureMorphism) C.toSpec he]
  change C.lineDegree (pullbackInvertibleSheaf
    (inv (PrimeCurveInclusionLift.lift C ι hC)) (pullbackInvertibleSheaf ι M)) = _
  rw [C.lineDegree_pullback_comp, ← PrimeCurveInclusionLift.inclusion_eq_inv_lift C ι hC]
  rfl

end PrimeCurveOriginalRestriction

open PrimeCurveOfClosedImmersion PrimeCurveClassPairing

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Vanishing of the actual kernel pairing trivializes the actual restriction
to a curve with a specified projective-line isomorphism over the original field. -/
def rationalRestrictionUnitIsoOfKernelPairingZero
    (X : NormalProjectiveSurface k)
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
    {Y : Scheme.{u}} (ι : Y ⟶ X.toScheme) [IsClosedImmersion ι]
    (e : Y ≅ projectiveSpace k 1)
    (he : e.hom ≫ projectiveSpaceToSpec k 1 = ι ≫ X.structureMorphism)
    (K M : InvertibleSheaf X.toScheme) (hK : K.obj = schemeKernelIdeal ι)
    (hM : pairing X hregular (Additive.ofMul M.toPic) (-Additive.ofMul K.toPic) = 0) :
    (pullbackInvertibleSheaf ι M).obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf := by
  letI : IsIntegral Y := isIntegral_of_iso_projectiveLine e
  let C : X.PrimeCurve := primeCurveOfIsoProjectiveLine X ι e
  have hC : (C : Set X.toScheme) = Set.range ι.base := rfl
  have hdegree : C.restrictionDegree M = 0 := by
    have h := (pairing_kernelLine_left X hregular C ι hC K hK
      (Additive.ofMul M.toPic)).symm.trans
        ((pairing_symm X hregular (-Additive.ofMul K.toPic) (Additive.ofMul M.toPic)).trans hM)
    change C.picardRestrictionDegree M.toPic = 0 at h
    rw [C.picardRestrictionDegree_toPic] at h
    exact h
  exact RationalTreePicard.unitIsoOfEulerDegreeZero e (ι ≫ X.structureMorphism) he
    (pullbackInvertibleSheaf ι M)
    ((PrimeCurveOriginalRestriction.eulerDegree_pullback_eq_restrictionDegree C ι hC M).trans
      hdegree)

end KltDP.Geometry
