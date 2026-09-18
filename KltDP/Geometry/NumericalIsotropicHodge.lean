import KltDP.Geometry.NumericalHodgeConsequences

/-!
# Proportionality of orthogonal isotropic numerical classes

The actual numerical Hodge form has a positive direction. Subtracting the
corresponding scalar multiple makes two orthogonal square-zero classes
orthogonal to that direction, still with square zero. Strict Hodge negativity
then proves proportionality on the original numerical quotient.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NumericalIsotropicHodge

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Two orthogonal isotropic classes are proportional when the first is nonzero.
No finite-dimensionality or abstract signature premise is needed. -/
theorem exists_smul_eq (c d : X.NumericalClassGroup) (hc : c ≠ 0)
    (hcc : X.numericalIntersectionBilinForm hregular c c = 0)
    (hdd : X.numericalIntersectionBilinForm hregular d d = 0)
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
  have hsquare : B (d - a • c) (d - a • c) = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hcc, hdd, hcd, hdc, B]
    ring
  have hzero := NumericalHodgeConsequences.eq_zero_of_nonneg_square_of_orthogonal
    X hregular h (d - a • c) hh hperp (le_of_eq hsquare.symm)
  exact ⟨a, sub_eq_zero.mp hzero⟩

end KltDP.Geometry.NumericalIsotropicHodge
