import KltDP.Geometry.NefPositiveSpanProved
import KltDP.Geometry.NumericalIsotropicHodge

/-!
# Orthogonal nontrivial nef classes are proportional

Nonnegative nef squares and the original numerical Hodge form first force
square zero. The proved isotropic Hodge consequence then proves proportionality
in the original numerical quotient, without a Picard-rank or pencil premise.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NefOrthogonalClassProportional

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- Two nef line bundles with zero mutual numerical pairing have proportional
numerical classes if the first is numerically nontrivial. -/
theorem exists_smul_eq (L M : InvertibleSheaf X.toScheme)
    (hL : Positivity.IsNef X.structureMorphism L)
    (hM : Positivity.IsNef X.structureMorphism M)
    (hne : ¬ X.NumericallyTrivial L.toPic)
    (horth : X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
      (X.picardNumericalClass L.toPic) (X.picardNumericalClass M.toPic) = 0) :
    ∃ a : ℚ, X.picardNumericalClass M.toPic = a • X.picardNumericalClass L.toPic := by
  let c := X.picardNumericalClass L.toPic
  let d := X.picardNumericalClass M.toPic
  let B := X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
  have hc : c ≠ 0 := by
    intro hc
    exact hne ((X.picardNumericalMap_eq_zero_iff (Additive.ofMul L.toPic)).mp hc)
  by_cases hd : d = 0
  · exact ⟨0, by simpa only [zero_smul] using hd⟩
  have hccNonneg : 0 ≤ B c c := NefPositiveSpanProved.numerical_square_nonneg X L hL
  have hddNonneg : 0 ≤ B d d := NefPositiveSpanProved.numerical_square_nonneg X M hM
  have hdc : B d c = 0 :=
    ((X.numericalIntersectionBilinForm_isSymm X.regularPoints_of_isSmooth).eq d c).trans horth
  have hcc : B c c = 0 := by
    by_contra hn
    have hpos : 0 < B c c := lt_of_le_of_ne hccNonneg (Ne.symm hn)
    exact hd (NumericalHodgeConsequences.eq_zero_of_nonneg_square_of_orthogonal
      X X.regularPoints_of_isSmooth c d hpos horth hddNonneg)
  have hdd : B d d = 0 := by
    by_contra hn
    have hpos : 0 < B d d := lt_of_le_of_ne hddNonneg (Ne.symm hn)
    exact hc (NumericalHodgeConsequences.eq_zero_of_nonneg_square_of_orthogonal
      X X.regularPoints_of_isSmooth d c hpos hdc hccNonneg)
  exact NumericalIsotropicHodge.exists_smul_eq X X.regularPoints_of_isSmooth
    c d hc hcc hdd horth

end KltDP.Geometry.NefOrthogonalClassProportional
