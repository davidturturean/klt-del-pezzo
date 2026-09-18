import KltDP.Geometry.RationalHodgeIndexProved
import KltDP.LinearAlgebra.HodgePositiveOrthogonal

/-!
# Hodge inequalities for the original numerical divisor classes

The published surface theorem and its proved rationalization supply the
negative orthogonal complement. The following consequences apply to every
positive-square class in the original numerical quotient. They need neither
an ample representative of that class nor finite dimensionality.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NumericalHodgeConsequences

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Strict Hodge negativity for any positive-square numerical class. -/
theorem neg_of_orthogonal_to_positive (h c : X.NumericalClassGroup)
    (hpos : 0 < X.numericalIntersectionBilinForm hregular h h)
    (hperp : X.numericalIntersectionBilinForm hregular h c = 0) (hc : c ≠ 0) :
    X.numericalIntersectionBilinForm hregular c c < 0 := by
  obtain ⟨a, _ha, hnegative⟩ := RationalHodgeIndexProved.signature X hregular
  exact LinearAlgebra.HodgePositiveOrthogonal.neg_of_orthogonal_to_positive
    (X.numericalIntersectionBilinForm hregular)
    (X.numericalIntersectionBilinForm_isSymm hregular) a hnegative h hpos c hperp hc

/-- The Hodge square inequality uses the actual descended intersection form. -/
theorem square_inequality (h c : X.NumericalClassGroup)
    (hpos : 0 < X.numericalIntersectionBilinForm hregular h h) :
    X.numericalIntersectionBilinForm hregular h h *
        X.numericalIntersectionBilinForm hregular c c ≤
      (X.numericalIntersectionBilinForm hregular h c) ^ 2 := by
  obtain ⟨a, _ha, hnegative⟩ := RationalHodgeIndexProved.signature X hregular
  exact LinearAlgebra.HodgePositiveOrthogonal.square_inequality
    (X.numericalIntersectionBilinForm hregular)
    (X.numericalIntersectionBilinForm_isSymm hregular) a hnegative h hpos c

/-- A nonnegative-square numerical class orthogonal to a positive direction is zero. -/
theorem eq_zero_of_nonneg_square_of_orthogonal (h c : X.NumericalClassGroup)
    (hpos : 0 < X.numericalIntersectionBilinForm hregular h h)
    (hperp : X.numericalIntersectionBilinForm hregular h c = 0)
    (hcc : 0 ≤ X.numericalIntersectionBilinForm hregular c c) : c = 0 := by
  classical
  by_contra hc
  exact not_lt_of_ge hcc (neg_of_orthogonal_to_positive X hregular h c hpos hperp hc)

end KltDP.Geometry.NumericalHodgeConsequences
