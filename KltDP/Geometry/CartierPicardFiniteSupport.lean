import KltDP.Geometry.PrimeCurveCartierVanishingIdeal
import KltDP.Geometry.CartierPicardHom

/-!
# Actual Cartier Picard classes as sums over their actual finite Weil support

The established Cartier-Weil equivalence on the original regular surface
transports the ordinary finite-support expansion. Each summand is the
actual Cartier representative of that prime, with its actual coefficient.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The actual Cartier class is the sum of its actual prime-Cartier classes. -/
theorem cartierPicardHom_eq_sum_primeCurveCartier (D : CartierDivisor X.toScheme) :
    cartierPicardHom X.toScheme D =
      ∑ C ∈ (X.cartierToWeilHom D).support,
        (X.cartierToWeilHom D C) • cartierPicardHom X.toScheme
          (X.primeCurveCartier hregular C) := by
  classical
  have hD : D = ∑ C ∈ (X.cartierToWeilHom D).support,
      (X.cartierToWeilHom D C) • X.primeCurveCartier hregular C := by
    apply (X.regularCartierWeilEquiv hregular).injective
    change X.cartierToWeilHom D = X.cartierToWeilHom _
    rw [map_sum]
    simp only [map_zsmul, X.cartierToWeilHom_primeCurveCartier hregular,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    exact (Finsupp.sum_single (X.cartierToWeilHom D)).symm
  calc
    cartierPicardHom X.toScheme D = cartierPicardHom X.toScheme
        (∑ C ∈ (X.cartierToWeilHom D).support,
          (X.cartierToWeilHom D C) • X.primeCurveCartier hregular C) :=
      congrArg (cartierPicardHom X.toScheme) hD
    _ = _ := by simp only [map_sum, map_zsmul]

/-- A subgroup containing the actual support classes contains the original Cartier class. -/
theorem cartierPicardHom_mem_of_support (D : CartierDivisor X.toScheme)
    (H : AddSubgroup (Additive X.toScheme.Pic))
    (h : ∀ C : X.PrimeCurve, X.cartierToWeilHom D C ≠ 0 →
      cartierPicardHom X.toScheme (X.primeCurveCartier hregular C) ∈ H) :
    cartierPicardHom X.toScheme D ∈ H := by
  rw [X.cartierPicardHom_eq_sum_primeCurveCartier hregular D]
  exact H.sum_mem (fun C hC => H.zsmul_mem (h C (Finsupp.mem_support_iff.mp hC)) _)

end KltDP.Geometry.NormalProjectiveSurface
