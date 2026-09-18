import KltDP.Geometry.SemiampleProjectiveCurveDegree
import KltDP.Geometry.PrimeCurveRestrictionDegree

/-!
# Original prime curves under a positive-power projective map

These are the original prime curve inclusion, structure morphism, and
restriction degree. The actual positive-power projective map is reused
without any hypothesis that it contracts a prescribed curve.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.PrimeCurvePowerSystem

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open NormalProjectiveSurface SemiampleProjectiveMap ProjectiveSpaceDegreeOneSheaf

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)
  (L : InvertibleSheaf X.toScheme) (S : PowerSystem L) (C : X.PrimeCurve)

/-- The original projective degree-one pullback has the actual positive
power exponent times the original prime-curve restriction degree. -/
theorem pullback_degreeOne_degree :
    C.restrictionDegree
        (pullbackInvertibleSheaf (PowerSystem.toProjective L X.structureMorphism S)
          (degreeOne k S.dimension)) =
      (S.exponent : ℤ) * C.restrictionDegree L := by
  letI : IsProper (C.inclusion ≫ X.structureMorphism) := C.toSpec_isProper
  rw [C.restrictionDegree_pullback]
  exact PowerSystem.restricted_degreeOne_degree L X.structureMorphism S C.inclusion
    (le_of_eq C.dimension_one_toScheme)

/-- The restriction of the actual power-system map to the original
prime curve is constant over k exactly when its original L-degree is zero. -/
theorem factors_iff_restrictionDegree_zero [IsAlgClosed k] :
    (∃ p : Spec (CommRingCat.of k) ⟶ projectiveSpace k S.dimension,
      C.inclusion ≫ PowerSystem.toProjective L X.structureMorphism S = C.toSpec ≫ p ∧
        p ≫ projectiveSpaceToSpec k S.dimension = 𝟙 _) ↔
      C.restrictionDegree L = 0 := by
  letI : IsProper (C.inclusion ≫ X.structureMorphism) := C.toSpec_isProper
  exact PowerSystem.restriction_factors_iff_degree_zero
    L X.structureMorphism S C.inclusion (le_of_eq C.dimension_one_toScheme)

end KltDP.Geometry.PrimeCurvePowerSystem
