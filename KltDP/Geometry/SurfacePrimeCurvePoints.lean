import KltDP.Geometry.CodimensionOneOpen
import KltDP.Geometry.PointClosureCurve
import KltDP.Geometry.ClosedPointDimension

/-!
# Prime curves and actual codimension-one surface points

The existing prime-curve carrier consists of actual irreducible closed
subsets of dimension one. Their actual generic points have local ring
dimension one. Conversely, a point with such a local ring is neither the
surface generic point nor a closed point. Its actual closure is therefore
a curve, by the previously proved surface dimension arguments.

The resulting equivalence uses no supplied curve correspondence. The
closed-point dimension theorem uses the original algebraically closed
field and finite-type surface hypotheses. These hypotheses are retained.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- The actual generic point of each existing prime curve has a
one-dimensional local ring. -/
def primeCurveToCodimensionOnePoint (C : X.PrimeCurve) : CodimensionOnePoint X.toScheme :=
  ⟨C.genericPoint, C.ringKrullDim_stalk_genericPoint⟩

/-- A point with a one-dimensional local ring cannot be the generic
point, whose local ring is the actual function field. -/
theorem codimensionOnePoint_ne_genericPoint (x : CodimensionOnePoint X.toScheme) :
    x.val ≠ genericPoint X.toScheme := by
  intro h
  have hd := x.property
  rw [h] at hd
  change ringKrullDim X.toScheme.functionField = 1 at hd
  rw [ringKrullDim_eq_zero_of_field] at hd
  norm_num at hd

/-- Closed points have two-dimensional local rings, so an actual
codimension-one point is nonclosed. -/
theorem codimensionOnePoint_not_isClosed (x : CodimensionOnePoint X.toScheme) :
    ¬ IsClosed ({x.val} : Set X.toScheme) := by
  intro hclosed
  have hd := X.closed_stalk_dimension_two x.val hclosed
  rw [x.property] at hd
  norm_num at hd

/-- The inverse curve is the actual closure of the selected point. -/
def codimensionOnePointToPrimeCurve (x : CodimensionOnePoint X.toScheme) : X.PrimeCurve :=
  X.primeCurveOfNonclosedPoint x.val
    (X.codimensionOnePoint_ne_genericPoint x) (X.codimensionOnePoint_not_isClosed x)

@[simp] theorem codimensionOnePointToPrimeCurve_genericPoint
    (x : CodimensionOnePoint X.toScheme) :
    (X.codimensionOnePointToPrimeCurve x).genericPoint = x.val :=
  X.primeCurveOfNonclosedPoint_genericPoint x.val
    (X.codimensionOnePoint_ne_genericPoint x) (X.codimensionOnePoint_not_isClosed x)

/-- The original prime-curve type is equivalent to the actual points
of local-ring dimension one; both maps are explicitly geometric. -/
def primeCurveCodimensionOneEquiv : X.PrimeCurve ≃ CodimensionOnePoint X.toScheme where
  toFun := X.primeCurveToCodimensionOnePoint
  invFun := X.codimensionOnePointToPrimeCurve
  left_inv C := by
    apply PrimeCurve.genericPoint_injective
    exact X.codimensionOnePointToPrimeCurve_genericPoint _
  right_inv x := by
    apply Subtype.ext
    exact X.codimensionOnePointToPrimeCurve_genericPoint x

/-- The inverse equivalence's curve has exactly the closure of the input
point, retaining its actual closed support. -/
theorem codimensionOnePointToPrimeCurve_coe (x : CodimensionOnePoint X.toScheme) :
    (X.codimensionOnePointToPrimeCurve x : Set X.toScheme) = closure {x.val} := rfl

end KltDP.Geometry.NormalProjectiveSurface
