import KltDP.Geometry.NumericalEquivalence

/-!
# Actual curve degrees from a rational Cartier class relation

Use the existing regular-surface Weil/Picard tensor equivalence and the
existing actual prime-curve degree. No new class space or degree is chosen.
-/

noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The existing rational Weil-to-Picard map retains the original O(D). -/
theorem rationalWeilToRationalPicard_cartier (D : CartierDivisor X.toScheme) :
    X.rationalWeilToRationalPicard hregular (X.rationalCartierToWeilHom D) =
      X.picardTensorInclusion (cartierPicardHom X.toScheme D) := by
  apply (X.regularPicardTensorRationalEquiv hregular).injective
  rw [rationalWeilToRationalPicard_apply, LinearEquiv.apply_symm_apply]
  exact (X.regularPicardTensorRationalEquiv_cartier hregular D).symm

/-- A proved class relation transports to the original rational Picard group. -/
theorem rationalWeilToRationalPicard_of_class_eq_smul_cartier
    (W : X.RationalWeilDivisor) (D : CartierDivisor X.toScheme) (c : ℚ)
    (h : X.rationalWeilClassMap W =
      c • X.rationalWeilClassMap (X.rationalCartierToWeilHom D)) :
    X.rationalWeilToRationalPicard hregular W =
      c • X.picardTensorInclusion (cartierPicardHom X.toScheme D) := by
  rw [rationalWeilToRationalPicard_apply, h, map_smul]
  exact congrArg (fun v : X.RationalPicard => c • v)
    (X.rationalWeilToRationalPicard_cartier hregular D)

/-- Evaluate a proved Cartier class relation on any actual prime curve. -/
theorem rationalRestrictionDegree_of_class_eq_smul_cartier
    (W : X.RationalWeilDivisor) (D : CartierDivisor X.toScheme) (c : ℚ)
    (h : X.rationalWeilClassMap W =
      c • X.rationalWeilClassMap (X.rationalCartierToWeilHom D))
    (C : X.PrimeCurve) :
    X.rationalPicardRestrictionDegree C (X.rationalWeilToRationalPicard hregular W) =
      c * (C.restrictionDegree (cartierDivisorInvertibleSheaf X.toScheme D) : ℚ) := by
  rw [X.rationalWeilToRationalPicard_of_class_eq_smul_cartier hregular W D c h,
    map_smul, rationalPicardRestrictionDegree_inclusion]
  change c * (C.picardRestrictionDegree
    (cartierDivisorInvertibleSheaf X.toScheme D).toPic : ℚ) = _
  rw [C.picardRestrictionDegree_toPic]

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.rationalRestrictionDegree_of_class_eq_smul_cartier
