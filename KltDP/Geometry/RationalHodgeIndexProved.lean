import KltDP.Geometry.RationalHodgeIndex
import KltDP.Geometry.SurfaceHodgeIndexProved

/-!
# Hodge index for the actual rational numerical classes

The full published surface theorem supplies the integral Hodge input. The
proved denominator-clearing adapter transports it to the existing rational
Picard group and its original numerical quotient. An actual ample sheaf gives
the named polarization; the final existential form constructs an ample sheaf
from the original projective embedding internally.

No Hodge hypothesis or finite-dimensionality premise is supplied by a consumer.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.RationalHodgeIndexProved

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Every rational numerical class orthogonal to an actual ample sheaf has
nonpositive self-intersection. -/
theorem numerical_nonpos_of_isAmple
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L)
    (c : X.NumericalClassGroup)
    (hperp : X.numericalIntersectionBilinForm hregular (X.picardNumericalClass L.toPic) c = 0) :
    X.numericalIntersectionBilinForm hregular c c ≤ 0 :=
  X.numericalIntersection_nonpos_of_integralHodge hregular L.toPic
    (SurfaceHodgeIndexProved.semidefinite_of_isAmple X hregular L hL) c hperp

/-- Every nonzero rational numerical class orthogonal to an actual ample sheaf
has strictly negative self-intersection. -/
theorem numerical_neg_of_isAmple
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L)
    (c : X.NumericalClassGroup)
    (hperp : X.numericalIntersectionBilinForm hregular (X.picardNumericalClass L.toPic) c = 0)
    (hc : c ≠ 0) : X.numericalIntersectionBilinForm hregular c c < 0 :=
  X.numericalIntersection_neg_of_integralHodge hregular L.toPic
    (AmpleSelfIntersectionPositive.selfIntersection_pos_of_isAmple X hregular L hL)
    (SurfaceHodgeIndexProved.semidefinite_of_isAmple X hregular L hL) c hperp hc

/-- Semidefiniteness on the original rationalized Picard group. -/
theorem rationalPicard_nonpos_of_isAmple
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L)
    (v : X.RationalPicard)
    (hperp : X.rationalPicardIntersectionBilinForm hregular
      (X.picardTensorInclusion (Additive.ofMul L.toPic)) v = 0) :
    X.rationalPicardIntersectionBilinForm hregular v v ≤ 0 :=
  X.rationalPicardIntersection_nonpos_of_integralHodge hregular L.toPic
    (SurfaceHodgeIndexProved.semidefinite_of_isAmple X hregular L hL) v hperp

/-- On rationalized Picard classes strictness is detected by the original
all-prime-curve numerical kernel. -/
theorem rationalPicard_neg_of_isAmple
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L)
    (v : X.RationalPicard)
    (hperp : X.rationalPicardIntersectionBilinForm hregular
      (X.picardTensorInclusion (Additive.ofMul L.toPic)) v = 0)
    (hv : v ∉ X.numericallyTrivialSubmodule) :
    X.rationalPicardIntersectionBilinForm hregular v v < 0 := by
  apply numerical_neg_of_isAmple X hregular L hL (X.rationalPicardNumericalMap v) hperp
  intro hzero
  exact hv ((Submodule.Quotient.mk_eq_zero X.numericallyTrivialSubmodule).mp hzero)

/-- Every original regular projective surface has a positive rational numerical
direction with a negative definite orthogonal complement. -/
theorem signature :
    ∃ h : X.NumericalClassGroup,
      0 < X.numericalIntersectionBilinForm hregular h h ∧
      ∀ c : X.NumericalClassGroup,
        X.numericalIntersectionBilinForm hregular h c = 0 → c ≠ 0 →
        X.numericalIntersectionBilinForm hregular c c < 0 :=
  X.numericalHodgeIndex_of_signature hregular (SurfaceHodgeIndexProved.signature X hregular)

end KltDP.Geometry.RationalHodgeIndexProved
