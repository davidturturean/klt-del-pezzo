import KltDP.Geometry.NefIntersectionSectionVanishing
import KltDP.Geometry.NefPositiveSelfIntersectionBig

/-! The original nef line pairs nonnegatively with any original effective
Cartier divisor. The existing Cartier representative and effective-Weil
intersection theorem supply this statement on the original Picard group. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S : NormalProjectiveSurface k)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)

local instance nefEffectiveSourceIntegral : IsIntegral S.toScheme := S.integral

/-- The original nef predicate controls the actual Picard pairing with an
effective divisor, with no assumed intersection or class identification. -/
theorem picardPairing_nonneg_of_nef_of_effective
    (H : InvertibleSheaf S.toScheme)
    (hH : Positivity.IsNef S.structureMorphism H)
    (D : CartierDivisor S.toScheme)
    (hD : EffectiveDivisor (S.cartierToWeilHom D)) :
    0 ≤ S.picardPairing hS H.toPic (cartierPicardClass S.toScheme D) := by
  let A := S.picardRepresentative H.toPic
  have hclass : cartierPicardClass S.toScheme A = H.toPic :=
    S.cartierPicardClass_picardRepresentative H.toPic
  have hA : Positivity.IsNef S.structureMorphism
      (cartierDivisorInvertibleSheaf S.toScheme A) :=
    NefPositiveSelfIntersectionBig.isNef_of_toPic_eq S hclass.symm hH
  have hnonneg := NefIntersectionSectionVanishing.intersection_nonneg
    S hS A hA (S.cartierToWeilHom D) hD
  have hrep : (S.regularCartierWeilEquiv hS).symm (S.cartierToWeilHom D) = D :=
    (S.regularCartierWeilEquiv hS).symm_apply_apply D
  rw [hrep, S.intersectionPairing_symm hS D A,
    ← S.picardPairing_class hS A D, hclass] at hnonneg
  exact hnonneg

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.picardPairing_nonneg_of_nef_of_effective
#print axioms KltDP.Geometry.NormalProjectiveSurface.picardPairing_nonneg_of_nef_of_effective
