import KltDP.Geometry.NefSelfIntersectionNonnegative
import KltDP.Geometry.NumericalHodgeConsequences

/-!
# The nef positive-span obstruction on the original smooth surface

The original nef line bundle has nonnegative square by the proved RR argument.
The actual numerical Hodge theorem therefore forces its class to vanish if it
is orthogonal to a positive-square class. Applied to the sum of classes with
squares -2 and -1, this proves the manuscript's intersection bound, with no
Hodge, square-positivity, or numerical finite-dimensionality assumption.
-/

noncomputable section

open AlgebraicGeometry
open KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Geometry.NefPositiveSpanProved

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- The actual numerical class of an original nef line bundle has nonnegative square. -/
theorem numerical_square_nonneg (L : InvertibleSheaf X.toScheme)
    (hL : Positivity.IsNef X.structureMorphism L) :
    0 ≤ X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
      (X.picardNumericalClass L.toPic) (X.picardNumericalClass L.toPic) := by
  change 0 ≤ X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
    (X.picardNumericalMap (Additive.ofMul L.toPic))
    (X.picardNumericalMap (Additive.ofMul L.toPic))
  rw [X.numericalIntersectionBilinForm_picard]
  exact_mod_cast NefSelfIntersectionNonnegative.selfIntersection_nonneg X L hL

/-- Orthogonality to any positive-square class forces the original nef line bundle
into the original all-prime-curve numerical kernel. -/
theorem numericallyTrivial_of_orthogonal_to_positive
    (L : InvertibleSheaf X.toScheme) (hL : Positivity.IsNef X.structureMorphism L)
    (v : X.NumericalClassGroup)
    (hv : 0 < X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth v v)
    (hperp : X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
      v (X.picardNumericalClass L.toPic) = 0) :
    X.NumericallyTrivial L.toPic := by
  have hzero := NumericalHodgeConsequences.eq_zero_of_nonneg_square_of_orthogonal
    X X.regularPoints_of_isSmooth v (X.picardNumericalClass L.toPic) hv hperp
    (numerical_square_nonneg X L hL)
  exact (X.picardNumericalMap_eq_zero_iff (Additive.ofMul L.toPic)).mp hzero

/-- Actual numerical classes of squares -2 and -1, both perpendicular to a
numerically nontrivial nef line bundle, meet at most once when their pairing is integral. -/
theorem intersection_le_one
    (L : InvertibleSheaf X.toScheme) (hL : Positivity.IsNef X.structureMorphism L)
    (hne : ¬ X.NumericallyTrivial L.toPic)
    (c p : X.NumericalClassGroup) (m : ℤ)
    (hcc : X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth c c = -2)
    (hpp : X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth p p = -1)
    (hcp : X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth c p = m)
    (hcL : X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
      c (X.picardNumericalClass L.toPic) = 0)
    (hpL : X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
      p (X.picardNumericalClass L.toPic) = 0) : m ≤ 1 := by
  by_contra hm
  have hmQ : (2 : ℚ) ≤ m := by exact_mod_cast (show (2 : ℤ) ≤ m by omega)
  have hpc := (X.numericalIntersectionBilinForm_isSymm X.regularPoints_of_isSmooth).eq p c
  have hv : 0 < X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
      (c + p) (c + p) := by
    simp only [map_add, LinearMap.add_apply, hcc, hpp, hpc, hcp]
    linarith
  have hperp : X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
      (c + p) (X.picardNumericalClass L.toPic) = 0 := by
    simp only [map_add, LinearMap.add_apply, hcL, hpL, add_zero]
  exact hne (numericallyTrivial_of_orthogonal_to_positive X L hL (c + p) hv hperp)

end KltDP.Geometry.NefPositiveSpanProved
