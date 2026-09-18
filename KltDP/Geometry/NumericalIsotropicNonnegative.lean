import KltDP.Geometry.NumericalIsotropicHodge

/-! A nonnegative-square class orthogonal to a nonzero isotropic class
is proportional to it in the original numerical quotient. This extends
the existing isotropic Hodge argument without a new geometric input. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
universe u
namespace KltDP.Geometry.NumericalIsotropicHodge

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Hodge negativity forces proportionality even when the second square
is initially only known to be nonnegative. -/
theorem exists_smul_eq_of_nonneg (c d : X.NumericalClassGroup) (hc : c ≠ 0)
    (hcc : X.numericalIntersectionBilinForm hregular c c = 0)
    (hdd : 0 ≤ X.numericalIntersectionBilinForm hregular d d)
    (hcd : X.numericalIntersectionBilinForm hregular c d = 0) :
    ∃ a : ℚ, d = a • c := by
  obtain ⟨h, hh, _⟩ := RationalHodgeIndexProved.signature X hregular
  let B := X.numericalIntersectionBilinForm hregular
  have hhc : B h c ≠ 0 := by
    intro hzero
    apply hc
    exact NumericalHodgeConsequences.eq_zero_of_nonneg_square_of_orthogonal
      X hregular h c hh hzero (le_of_eq hcc.symm)
  let a : ℚ := B h d / B h c
  have hdc : B d c = 0 :=
    ((X.numericalIntersectionBilinForm_isSymm hregular).eq d c).trans hcd
  have hperp : B h (d - a • c) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul]
    dsimp only [a]
    rw [div_mul_cancel₀ _ hhc, sub_self]
  have hsquare : B (d - a • c) (d - a • c) = B d d := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hcc, hcd, hdc, B]
    ring
  have hzero := NumericalHodgeConsequences.eq_zero_of_nonneg_square_of_orthogonal
    X hregular h (d - a • c) hh hperp (by rw [hsquare]; exact hdd)
  exact ⟨a, sub_eq_zero.mp hzero⟩

end KltDP.Geometry.NumericalIsotropicHodge

#check @KltDP.Geometry.NumericalIsotropicHodge.exists_smul_eq_of_nonneg
#print axioms KltDP.Geometry.NumericalIsotropicHodge.exists_smul_eq_of_nonneg
