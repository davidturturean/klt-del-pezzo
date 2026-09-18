import KltDP.Geometry.CartierPicardEndpointRationalClasses
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# Division of an actual integral Weil-class relation after rationalization

Use the existing original integral-to-rational class homomorphism. Its
codomain is the actual rational principal-divisor quotient, a Q-vector
space. Integer scalar transport and division by a nonzero integer are
ordinary algebra; no regularity or inverse Weil-to-Picard map is used.
-/

noncomputable section

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Divide an integral class relation in the existing rational Weil class space. -/
theorem rationalization_formula_of_integral_relation
    (c d : ℤ) (K A : X.WeilClassGroup) (hc : c ≠ 0)
    (h : c • K + d • A = 0) :
    X.weilClassRationalization K =
      (-(d : ℚ) / (c : ℚ)) • X.weilClassRationalization A := by
  let R := X.weilClassRationalization
  have hK : R (c • K) = c • R K := map_zsmul R _ _
  have hA : R (d • A) = d • R A := map_zsmul R _ _
  have hsum : c • R K + d • R A = 0 :=
    ((map_add R (c • K) (d • A)).trans
      (congrArg₂ (fun x y : X.RationalWeilClassGroup => x + y) hK hA)).symm.trans
      ((congrArg R h).trans (map_zero R))
  have hrat : (c : ℚ) • R K + (d : ℚ) • R A = 0 :=
    (congrArg₂ (fun x y : X.RationalWeilClassGroup => x + y)
      (Int.cast_smul_eq_zsmul ℚ c (R K))
      (Int.cast_smul_eq_zsmul ℚ d (R A))).trans hsum
  have heq : (c : ℚ) • R K = (-(d : ℚ)) • R A :=
    (eq_neg_of_add_eq_zero_left hrat).trans (neg_smul (d : ℚ) (R A)).symm
  have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hinv : R K = (c : ℚ)⁻¹ • ((-(d : ℚ)) • R A) :=
    (eq_inv_smul_iff₀ hcQ).mpr heq
  have hcoeff : (c : ℚ)⁻¹ * (-(d : ℚ)) = -(d : ℚ) / (c : ℚ) := by
    rw [div_eq_mul_inv, mul_comm]
  exact hinv.trans ((smul_smul ((c : ℚ)⁻¹) (-(d : ℚ)) (R A)).trans
    (congrArg (fun z : ℚ => z • R A) hcoeff))

end KltDP.Geometry.NormalProjectiveSurface
