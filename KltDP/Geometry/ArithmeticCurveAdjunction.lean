import KltDP.Geometry.CanonicalEulerDefectVanishes
import KltDP.Geometry.SmoothCurveCanonicalDegree
import KltDP.Geometry.ProjectiveStructureSheafHZero

/-!
# Arithmetic adjunction for the original integral prime curve

The curve may be singular. The proof applies the derived Euler form of
surface RR to -C and the original ideal-sequence Euler restriction identity.
Proper integral H0=1 and dimension-one vanishing identify chi(O_C)=1-h1(O_C).
No cotangent/dualizing identification on C or curve adjunction premise is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison

universe u

set_option autoImplicit false

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Arithmetic adjunction for any original prime curve on the regular
surface and any genuine canonical Cartier representative. -/
theorem arithmetic_canonical_row (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2)
    (C : X.PrimeCurve) :
    C.intersectionNumber K + C.selfIntersectionNumber hregular =
      2 * (CurveCanonical.genus C.toSpec : ℤ) - 2 := by
  letI := C.toSpec_isProper
  have hr := X.cartier_euler_riemannRoch_twice hregular K eK
    (-(X.primeCurveCartier hregular C))
  have hp : intersectionPairing X hregular (-(X.primeCurveCartier hregular C))
      (-(X.primeCurveCartier hregular C) - K) =
      C.selfIntersectionNumber hregular + C.intersectionNumber K := by
    rw [show -(X.primeCurveCartier hregular C) - K =
        -(X.primeCurveCartier hregular C + K) by abel,
      X.intersectionPairing_neg_left, X.intersectionPairing_neg_right, neg_neg,
      X.intersectionPairing_add_right,
      X.intersectionPairing_primeCurve hregular (X.primeCurveCartier hregular C) C,
      X.intersectionPairing_symm hregular (X.primeCurveCartier hregular C) K,
      X.intersectionPairing_primeCurve hregular K C]
    rfl
  rw [hp] at hr
  have he := X.eulerCharacteristic_unit_sub_neg_primeCurveCartier hregular C
  have hc := proper_eulerCharacteristic_eq_h0_sub_h1 C.toSpec
    C.dimension_one_toScheme.le (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf)
  have h₀ : cohomologyDimension C.toSpec
      (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) 0 = 1 :=
    StructureSheafCohomology.hZero_finrank_one C.toSpec
  rw [h₀] at hc
  change eulerCharacteristic C.toSpec (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) =
    1 - (CurveCanonical.genus C.toSpec : ℤ) at hc
  omega

/-- The original canonical degree written as the arithmetic canonical row. -/
theorem arithmetic_canonical_degree (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2)
    (C : X.PrimeCurve) :
    C.intersectionNumber K = 2 * (CurveCanonical.genus C.toSpec : ℤ) - 2 -
      C.selfIntersectionNumber hregular := by
  have h := X.arithmetic_canonical_row hregular K eK C
  omega

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.arithmetic_canonical_row
#print axioms KltDP.Geometry.NormalProjectiveSurface.arithmetic_canonical_row
#check @KltDP.Geometry.NormalProjectiveSurface.arithmetic_canonical_degree
#print axioms KltDP.Geometry.NormalProjectiveSurface.arithmetic_canonical_degree
