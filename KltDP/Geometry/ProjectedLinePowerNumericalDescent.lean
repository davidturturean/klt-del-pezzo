import KltDP.Geometry.ExceptionalAmpleProjectionNumerical

/-!
# An actual descended line-bundle power gives numerical projection descent

The inputs are the actual line bundle representing a positive integral
multiple of the constructed correction and an actual target line whose
pullback has that source line's positive power class. Rationalizing these
literal Picard identities clears the positive product and places the
original projection in the image of the original numerical pullback.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ActualExceptionalNumerical

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}

theorem lineClass_of_picard_power (A B : InvertibleSheaf S.toScheme) (m : ℕ)
    (h : A.toPic = B.toPic ^ m) :
    ExceptionalAmpleProjection.lineClass S A =
      (m : ℚ) • ExceptionalAmpleProjection.lineClass S B := by
  unfold ExceptionalAmpleProjection.lineClass
  rw [h, ofMul_pow, map_nsmul]
  simp only [Nat.cast_smul_eq_nsmul]

variable (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme π)

theorem pullback_lineClass (A : InvertibleSheaf X.toScheme) :
    BirationalNumericalPullback.pullback π hπ hbir
        (X.rationalPicardNumericalMap (ExceptionalAmpleProjection.lineClass X A)) =
      S.rationalPicardNumericalMap
        (ExceptionalAmpleProjection.lineClass S (pullbackInvertibleSheaf π A)) := by
  rw [BirationalNumericalPullback.pullback_mk, rationalPullback_lineClass]

variable [IsSmoothOfRelativeDimension 2 S.structureMorphism]

local instance projectedLineSourceSmooth : IsSmooth S.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism

/-- These original Picard equalities come from the actual correction line
and its descended power; no numerical membership or scalar correction is assumed. -/
theorem projection_mem_pullback_range_of_line_power
    (H L : InvertibleSheaf S.toScheme) (A : InvertibleSheaf X.toScheme)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hL : ExceptionalAmpleProjection.lineClass S L =
      (n : ℚ) • ExceptionalAmpleProjection.originalProjectedClass π hbir
        (ExceptionalAmpleProjection.lineClass S H))
    (hpower : (pullbackInvertibleSheaf π A).toPic = L.toPic ^ m) :
    projection π hπ hbir S.regularPoints_of_isSmooth
        (S.rationalPicardNumericalMap (ExceptionalAmpleProjection.lineClass S H)) ∈
      LinearMap.range (BirationalNumericalPullback.pullback π hπ hbir) := by
  have hvalue : BirationalNumericalPullback.pullback π hπ hbir
        (X.rationalPicardNumericalMap (ExceptionalAmpleProjection.lineClass X A)) =
      ((m : ℚ) * (n : ℚ)) • projection π hπ hbir S.regularPoints_of_isSmooth
        (S.rationalPicardNumericalMap (ExceptionalAmpleProjection.lineClass S H)) := by
    rw [pullback_lineClass, lineClass_of_picard_power (pullbackInvertibleSheaf π A) L m hpower,
      map_smul, hL, map_smul, originalProjectedClass_numerical_eq_projection π hπ hbir,
      smul_smul]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hmem := (LinearMap.range (BirationalNumericalPullback.pullback π hπ hbir)).smul_mem
    (((m : ℚ) * (n : ℚ))⁻¹)
    (show ((m : ℚ) * (n : ℚ)) • projection π hπ hbir S.regularPoints_of_isSmooth
        (S.rationalPicardNumericalMap (ExceptionalAmpleProjection.lineClass S H)) ∈
      LinearMap.range (BirationalNumericalPullback.pullback π hπ hbir) from
        ⟨X.rationalPicardNumericalMap (ExceptionalAmpleProjection.lineClass X A), hvalue⟩)
  simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hmq hnq), one_smul] using hmem

end KltDP.Geometry.ActualExceptionalNumerical

#check @KltDP.Geometry.ActualExceptionalNumerical.projection_mem_pullback_range_of_line_power
#print axioms KltDP.Geometry.ActualExceptionalNumerical.projection_mem_pullback_range_of_line_power
