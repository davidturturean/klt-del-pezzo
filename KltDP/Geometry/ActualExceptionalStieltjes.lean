import KltDP.Geometry.ActualExceptionalNegativeDefinite
import KltDP.Geometry.PrimeCurvePairingSupport
import KltDP.LinearAlgebra.Stieltjes

/-!
# The actual exceptional matrix satisfies the Stieltjes maximum principle

The original proper birational map supplies strict negativity; intersections
of distinct actual primes supply the off-diagonal signs. The existing proved
Stieltjes theorem therefore determines the sign of coefficients from their
original intersection degrees, without an assumed matrix property.

The strict-negativity proof retains the selected isolated Hodge dependency.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory Matrix
universe u v

namespace KltDP.Geometry.ActualExceptionalStieltjes

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hbir : IsBirationalScheme π)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
  {I : Type v} [Fintype I]
  (C : I → S.PrimeCurve) (hinj : Function.Injective C)
  (hcontracted : ∀ i, IsExceptionalCurve π (C i))

include hπ hbir hinj hcontracted in
/-- The negative of the literal original exceptional intersection matrix
is positive definite. -/
theorem negativeIntersectionMatrix_posDef :
    (-NullCurveIntersectionMatrix.intersectionMatrix S hregular C).PosDef := by
  constructor
  · change (-NullCurveIntersectionMatrix.intersectionMatrix S hregular C)ᴴ = _
    ext i j
    change -(S.intersectionPairing hregular
      (S.primeCurveCartier hregular (C j)) (S.primeCurveCartier hregular (C i)) : ℚ) =
        -(S.intersectionPairing hregular
          (S.primeCurveCartier hregular (C i)) (S.primeCurveCartier hregular (C j)) : ℚ)
    rw [S.intersectionPairing_symm hregular]
  · intro a ha
    have hneg := ActualExceptionalNegativeDefinite.quadraticForm_neg
      π hπ hbir hregular C hinj hcontracted a ha
    simpa only [star_trivial, neg_mulVec, dotProduct_neg] using neg_pos.mpr hneg

include hinj in
/-- Off-diagonal signs follow from the actual distinct prime curves. -/
theorem negativeIntersectionMatrix_offDiagonal (i j : I) (hij : i ≠ j) :
    (-NullCurveIntersectionMatrix.intersectionMatrix S hregular C) i j ≤ 0 := by
  have hnonneg := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg
    S hregular (C i) (C j) (fun h => hij (hinj h))
  change -(S.intersectionPairing hregular
    (S.primeCurveCartier hregular (C i)) (S.primeCurveCartier hregular (C j)) : ℚ) ≤ 0
  exact neg_nonpos.mpr (by exact_mod_cast hnonneg)

include hπ hbir hinj hcontracted in
/-- Nonnegative original intersection degrees force nonpositive actual
exceptional coefficients. Matrix positivity and off-diagonal signs are derived. -/
theorem coeff_nonpositive_of_nonnegative_intersections (a : I → ℚ)
    (hdegree : ∀ i, 0 ≤
      (NullCurveIntersectionMatrix.intersectionMatrix S hregular C *ᵥ a) i) :
    ∀ i, a i ≤ 0 := by
  have himage : ∀ i, 0 ≤
      ((-NullCurveIntersectionMatrix.intersectionMatrix S hregular C) *ᵥ (-a)) i := by
    simpa only [neg_mulVec, mulVec_neg, neg_neg] using hdegree
  have h := KltDP.LinearAlgebra.nonneg_of_mulVec_nonneg
    (negativeIntersectionMatrix_posDef π hπ hbir hregular C hinj hcontracted)
    (negativeIntersectionMatrix_offDiagonal hregular C hinj) himage
  intro i
  exact neg_nonneg.mp (h i)

end KltDP.Geometry.ActualExceptionalStieltjes

#print axioms KltDP.Geometry.ActualExceptionalStieltjes.negativeIntersectionMatrix_posDef
#print axioms KltDP.Geometry.ActualExceptionalStieltjes.coeff_nonpositive_of_nonnegative_intersections
