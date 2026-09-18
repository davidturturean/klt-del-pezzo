import KltDP.Geometry.ActualExceptionalNumericalProjection
import KltDP.Geometry.ExceptionalAmpleProjectionLineBundle
import KltDP.Geometry.BirationalNumericalPullback

/-!
# The actual ample correction is the original linear numerical projection

The original inverse-matrix correction has zero degrees on the original
contracted primes, and its difference from the original input is the literal
finite sum of their original Cartier classes. The proved projection uniqueness
therefore identifies its numerical image with the actual linear projection.
Neither the coefficient vector nor this identification is supplied as a premise.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped BigOperators TensorProduct
universe u

namespace KltDP.Geometry.ActualExceptionalNumerical

open DisjointNegativeCurvesRank

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme π)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

include hπ hbir

theorem projectedClass_numerical_eq_projection [Fintype (ActualExceptionalIncidence.Vertices π)]
    (z : S.RationalPicard) :
    S.rationalPicardNumericalMap
        (ExceptionalAmpleProjection.projectedClass S hregular
          (fun C : ActualExceptionalIncidence.Vertices π => C.val) z) =
      projection π hπ hbir hregular (S.rationalPicardNumericalMap z) := by
  symm
  apply projection_eq_of_sub_mem π hπ hbir hregular
  · apply (mem_exceptionalOrthogonal_iff π _).mpr
    intro C
    rw [S.numericalRestrictionDegree_mk]
    exact ExceptionalAmpleProjection.degree_projectedClass_family S hregular
      (fun C : ActualExceptionalIncidence.Vertices π => C.val) π hπ hbir
      Subtype.val_injective (fun C => C.property) z C
  · let c := ExceptionalAmpleProjection.coefficients S hregular
      (fun C : ActualExceptionalIncidence.Vertices π => C.val) z
    have hsum : S.rationalPicardNumericalMap
        (∑ C : ActualExceptionalIncidence.Vertices π,
          c C • S.primeCurveRationalPicardClass hregular C.val) ∈
        exceptionalSpan π hregular := by
      rw [map_sum]
      apply (exceptionalSpan π hregular).sum_mem
      intro C hC
      rw [map_smul]
      apply (exceptionalSpan π hregular).smul_mem
      change curveClass S hregular C.val ∈ exceptionalSpan π hregular
      exact Submodule.subset_span ⟨C, rfl⟩
    rw [ExceptionalAmpleProjection.projectedClass, map_add]
    simpa only [sub_add_eq_sub_sub, sub_self, zero_sub] using
      (exceptionalSpan π hregular).neg_mem hsum

omit hregular in
theorem originalProjectedClass_numerical_eq_projection
    [IsSmoothOfRelativeDimension 2 S.structureMorphism] (z : S.RationalPicard) :
    letI : IsSmooth S.structureMorphism :=
      IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism
    S.rationalPicardNumericalMap (ExceptionalAmpleProjection.originalProjectedClass π hbir z) =
      projection π hπ hbir S.regularPoints_of_isSmooth (S.rationalPicardNumericalMap z) := by
  letI : IsSmooth S.structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism
  letI : Finite (ActualExceptionalIncidence.Vertices π) :=
    ActualExceptionalIncidence.finite_vertices π hbir
  letI := Fintype.ofFinite (ActualExceptionalIncidence.Vertices π)
  exact projectedClass_numerical_eq_projection π hπ hbir S.regularPoints_of_isSmooth z

omit hπ hbir hregular in
/-- The original tensor pullback agrees with the actual pulled-back line bundle. -/
theorem rationalPullback_lineClass (L : InvertibleSheaf X.toScheme) :
    BirationalNumericalPullback.rationalPullback π (ExceptionalAmpleProjection.lineClass X L) =
      ExceptionalAmpleProjection.lineClass S (pullbackInvertibleSheaf π L) := by
  change (1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul (schemePicardPullbackHom π L.toPic) =
    (1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul ((pullbackInvertibleSheaf π L).toPic)
  rw [schemePicardPullbackHom_toPic]

end KltDP.Geometry.ActualExceptionalNumerical

#check @KltDP.Geometry.ActualExceptionalNumerical.originalProjectedClass_numerical_eq_projection
#check @KltDP.Geometry.ActualExceptionalNumerical.rationalPullback_lineClass
#print axioms KltDP.Geometry.ActualExceptionalNumerical.originalProjectedClass_numerical_eq_projection
