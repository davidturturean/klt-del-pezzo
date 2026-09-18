import KltDP.Geometry.BirationalProjectionDegree
import KltDP.Geometry.ActualExceptionalPullback

/-!
# Pullback on the original rational Picard groups and its actual degrees

The original sheaf Picard pullback is tensored with the identity on Q.
Its degrees are unchanged on original corresponding primes and vanish on
original contracted primes. The latter factorization is derived by the
existing exceptional-curve theorem; no coefficient equation is supplied.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u

namespace KltDP.Geometry.BirationalNumericalPullback

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme)

/-- Extension of the original sheaf Picard pullback to its actual rational tensor. -/
def rationalPullback : X.RationalPicard →ₗ[ℚ] S.RationalPicard :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
    (schemePicardPullbackHom π).toAdditive.toIntLinearMap

@[simp]
theorem rationalPullback_tmul (q : ℚ) (p : Additive X.toScheme.Pic) :
    rationalPullback π (q ⊗ₜ[ℤ] p) =
      q ⊗ₜ[ℤ] (schemePicardPullbackHom π).toAdditive p := rfl

theorem degree_above [IsProper π]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme π)
    (C : X.PrimeCurve) (v : X.RationalPicard) :
    S.rationalPicardRestrictionDegree (abovePrimeCurve π hbir C) (rationalPullback π v) =
      X.rationalPicardRestrictionDegree C v := by
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp only [map_zero]
  · intro q p
    change q * ((abovePrimeCurve π hbir C).picardRestrictionDegree
        (schemePicardPullbackHom π p.toMul) : ℚ) = q * (C.picardRestrictionDegree p.toMul : ℚ)
    rw [BirationalProjectionDegree.picardRestrictionDegree_pullback π hπ hbir C p.toMul]
  · intro a b ha hb
    simp only [map_add, ha, hb]

theorem picard_degree_exceptional [IsAlgClosed k]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (C : S.PrimeCurve) (hC : IsExceptionalCurve π C) (p : X.toScheme.Pic) :
    C.picardRestrictionDegree (schemePicardPullbackHom π p) = 0 := by
  obtain ⟨L, rfl⟩ := RationalTreePicard.toPic_surjective p
  rw [schemePicardPullbackHom_toPic, C.picardRestrictionDegree_toPic]
  exact IsExceptionalCurve.restrictionDegree_pullback_eq_zero π hπ C hC L

theorem degree_exceptional [IsAlgClosed k]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (C : S.PrimeCurve) (hC : IsExceptionalCurve π C) (v : X.RationalPicard) :
    S.rationalPicardRestrictionDegree C (rationalPullback π v) = 0 := by
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp only [map_zero]
  · intro q p
    change q * (C.picardRestrictionDegree (schemePicardPullbackHom π p.toMul) : ℚ) = 0
    rw [picard_degree_exceptional π hπ C hC p.toMul, Int.cast_zero, mul_zero]
  · intro a b ha hb
    simp only [map_add, ha, hb, add_zero]

end KltDP.Geometry.BirationalNumericalPullback

#check @KltDP.Geometry.BirationalNumericalPullback.rationalPullback
#print axioms KltDP.Geometry.BirationalNumericalPullback.degree_above
#print axioms KltDP.Geometry.BirationalNumericalPullback.degree_exceptional
