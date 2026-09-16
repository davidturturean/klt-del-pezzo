import KltDP.Geometry.CartierPicardEndpointRationalClasses
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The actual Picard tensor product and rational divisor classes

The map from integral to rational Weil classes satisfies the three
localization axioms. Scalar multiplication by a nonzero integer is
invertible in the rational class space; every rational class has an
integral numerator; equality of integral images is killed by a nonzero
integer. The last two statements use the proved geometric class maps.

Mathlib's localization/base-change theorem then identifies the rational
class space with the actual tensor product of integral classes with ℚ.
On a regular surface the existing integral Weil/Picard equivalence gives
the corresponding actual Picard tensor product. These spaces remain
distinct from numerical divisor classes; no numerical quotient is used.
-/

noncomputable section

open TensorProduct

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The original class rationalization, regarded as an integer-linear map. -/
def weilClassRationalizationLinear : X.WeilClassGroup →ₗ[ℤ] X.RationalWeilClassGroup :=
  X.weilClassRationalization.toIntLinearMap

/-- The actual integral class map is a localization at the nonzero integers. -/
instance weilClassRationalization_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ) X.weilClassRationalizationLinear where
  map_units s := by
    rw [← (Algebra.lsmul ℤ (A := ℚ) ℤ X.RationalWeilClassGroup).commutes]
    exact (IsLocalization.map_units ℚ s).map _
  surj' c := by
    obtain ⟨D, rfl⟩ := X.rationalPrincipalSubmodule.mkQ_surjective c
    obtain ⟨n, hn, A, hA⟩ := X.exists_positive_integral_multiple D
    let s : nonZeroDivisors ℤ :=
      ⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr
        (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn))⟩
    refine ⟨(X.weilClassMap A, s), ?_⟩
    change (n : ℤ) • X.rationalWeilClassMap D =
      X.weilClassRationalization (X.weilClassMap A)
    rw [natCast_zsmul, X.weilClassRationalization_class]
    exact (X.rationalWeilClassMap.toAddMonoidHom.map_nsmul D n).symm.trans
      (congrArg X.rationalWeilClassMap hA.symm)
  exists_of_eq {c d} h := by
    have hzero : X.weilClassRationalization (c - d) = 0 := by
      change X.weilClassRationalization c = X.weilClassRationalization d at h
      rw [map_sub, h, sub_self]
    obtain ⟨n, hn, hcd⟩ := (X.weilClassRationalization_eq_zero_iff (c - d)).mp hzero
    let s : nonZeroDivisors ℤ :=
      ⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr
        (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn))⟩
    refine ⟨s, ?_⟩
    change (n : ℤ) • c = (n : ℤ) • d
    simpa only [natCast_zsmul, nsmul_sub, sub_eq_zero] using hcd

/-- The actual tensor product of integral Weil classes is the constructed
rational divisor class space, by the imported localization theorem. -/
def weilClassTensorRationalEquiv :
    ℚ ⊗[ℤ] X.WeilClassGroup ≃ₗ[ℚ] X.RationalWeilClassGroup :=
  (IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ
    X.weilClassRationalizationLinear).equiv

/-- The tensor equivalence preserves the original integral class inclusion. -/
theorem weilClassTensorRationalEquiv_one_tmul (c : X.WeilClassGroup) :
    X.weilClassTensorRationalEquiv (1 ⊗ₜ[ℤ] c) = X.weilClassRationalization c := by
  exact (IsBaseChange.equiv_tmul
    (IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ
      X.weilClassRationalizationLinear) (1 : ℚ) c).trans (one_smul ℚ _)

section Regular

variable [IsAlgClosed k]
variable (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The original Picard rationalization as an integer-linear map. -/
def regularPicardRationalizationLinear :
    Additive X.toScheme.Pic →ₗ[ℤ] X.RationalWeilClassGroup :=
  (X.regularPicardRationalization hregular).toIntLinearMap

/-- The proved integral Picard equivalence transports the actual localization
map; no rational Picard comparison is included among the hypotheses. -/
instance regularPicardRationalization_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ) (X.regularPicardRationalizationLinear hregular) := by
  change IsLocalizedModule (nonZeroDivisors ℤ)
    (X.weilClassRationalizationLinear.comp
      (X.regularWeilClassPicardEquiv hregular).symm.toIntLinearEquiv.toLinearMap)
  exact IsLocalizedModule.of_linearEquiv_right (nonZeroDivisors ℤ)
    X.weilClassRationalizationLinear
    (X.regularWeilClassPicardEquiv hregular).symm.toIntLinearEquiv

/-- The actual tensor product of the original sheaf Picard group is
identified with rational divisor classes on the regular surface. -/
def regularPicardTensorRationalEquiv :
    ℚ ⊗[ℤ] Additive X.toScheme.Pic ≃ₗ[ℚ] X.RationalWeilClassGroup :=
  (IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ
    (X.regularPicardRationalizationLinear hregular)).equiv

/-- The rational comparison carries the tensor image of an integral Picard
class to its already constructed rational divisor class. -/
theorem regularPicardTensorRationalEquiv_one_tmul (c : Additive X.toScheme.Pic) :
    X.regularPicardTensorRationalEquiv hregular (1 ⊗ₜ[ℤ] c) =
      X.regularPicardRationalization hregular c := by
  exact (IsBaseChange.equiv_tmul
    (IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ
      (X.regularPicardRationalizationLinear hregular)) (1 : ℚ) c).trans (one_smul ℚ _)

/-- For the original Cartier sheaf O(D), tensor rationalization gives
the class of its actual Cartier-to-Weil divisor. -/
theorem regularPicardTensorRationalEquiv_cartier (D : CartierDivisor X.toScheme) :
    X.regularPicardTensorRationalEquiv hregular
        (1 ⊗ₜ[ℤ] cartierPicardHom X.toScheme D) =
      X.rationalWeilClassMap (rationalizeWeilDivisor X (X.cartierToWeilHom D)) := by
  rw [X.regularPicardTensorRationalEquiv_one_tmul,
    X.regularPicardRationalization_of_cartier]

end Regular

end KltDP.Geometry.NormalProjectiveSurface
