import KltDP.Geometry.PointBlowupSurface
import KltDP.Geometry.PointBlowupProper
import KltDP.Geometry.SurfacePrimeCurvePoints

/-!
# Prime-divisor points away from the actual point-blowup fiber

The actual puncture isomorphism identifies all codimension-one points
outside the exceptional fiber with the original surface's prime curves.
No curve generic point is the selected closed point. Consequently every
original curve has a unique actual codimension-one point above its generic
point, and the closure of that point maps onto the original curve.

The source support is its actual irreducible point closure. This file does
not silently equip the constructed source with a normal-projective-surface
structure or assert that this closure has dimension one before those
properties are established. The codimension-one assertion uses its actual
stalk dimension, and the target is the existing actual prime-curve type.
Finite sums retain every coefficient through the actual correspondence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupGluing

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k)
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))

/-- Every actual codimension-one point of the original surface belongs
to the puncture, because it cannot be the closed center. -/
theorem codimensionOnePoint_mem_puncture (x : CodimensionOnePoint X.toScheme) :
    x.val ∈ puncture j q hclosed := by
  change x.val ≠ j.base q
  intro h
  apply X.codimensionOnePoint_not_isClosed x
  rw [h]
  exact hclosed

/-- Actual codimension-one points on the constructed source which are
outside the actual fiber over the selected point. -/
abbrev OutsideCodimensionOnePoint :=
  CodimensionOnePointInOpen ((projection j q hclosed) ⁻¹ᵁ puncture j q hclosed)

/-- The defining exclusion concerns the actual original projection. -/
theorem outsideCodimensionOnePoint_avoids_center
    (x : OutsideCodimensionOnePoint X j q hclosed) :
    (projection j q hclosed).base x.val.val ≠ j.base q := x.property

/-- The actual puncture isomorphism, followed by the established surface
generic-point/curve equivalence, gives the prime correspondence. -/
def outsidePrimeCurveEquiv : OutsideCodimensionOnePoint X j q hclosed ≃ X.PrimeCurve := by
  letI : IsIso ((projection j q hclosed) ∣_ puncture j q hclosed) :=
    projection_restrict_puncture_isIso j q hclosed
  exact (codimensionOneOverOpenEquiv (projection j q hclosed) (puncture j q hclosed)).trans
    ((Equiv.subtypeUnivEquiv (codimensionOnePoint_mem_puncture X j q hclosed)).trans
      X.primeCurveCodimensionOneEquiv.symm)

/-- The prime correspondence maps the actual source point to the
actual generic point of its selected original curve. -/
theorem outsidePrimeCurveEquiv_genericPoint
    (x : OutsideCodimensionOnePoint X j q hclosed) :
    (projection j q hclosed).base x.val.val =
      (outsidePrimeCurveEquiv X j q hclosed x).genericPoint := by
  letI : IsIso ((projection j q hclosed) ∣_ puncture j q hclosed) :=
    projection_restrict_puncture_isIso j q hclosed
  change (projection j q hclosed).base x.val.val =
    (X.codimensionOnePointToPrimeCurve
      (codimensionOneOverOpenEquiv (projection j q hclosed) (puncture j q hclosed) x).val).genericPoint
  rw [X.codimensionOnePointToPrimeCurve_genericPoint]
  exact (codimensionOneOverOpenEquiv_apply_val
    (projection j q hclosed) (puncture j q hclosed) x).symm

/-- The actual codimension-one point of the strict transform is
constructed as the inverse image under the proved correspondence. -/
def strictTransformPoint (C : X.PrimeCurve) : OutsideCodimensionOnePoint X j q hclosed :=
  (outsidePrimeCurveEquiv X j q hclosed).symm C

@[simp] theorem strictTransformPoint_projection (C : X.PrimeCurve) :
    (projection j q hclosed).base (strictTransformPoint X j q hclosed C).val.val =
      C.genericPoint := by
  simpa only [strictTransformPoint, Equiv.apply_symm_apply] using
    outsidePrimeCurveEquiv_genericPoint X j q hclosed
      ((outsidePrimeCurveEquiv X j q hclosed).symm C)

/-- Every original prime curve has precisely one actual codimension-one
point outside the exceptional fiber over its actual generic point. -/
theorem existsUnique_strictTransformPoint (C : X.PrimeCurve) :
    ∃! x : OutsideCodimensionOnePoint X j q hclosed,
      (projection j q hclosed).base x.val.val = C.genericPoint := by
  refine ⟨strictTransformPoint X j q hclosed C,
    strictTransformPoint_projection X j q hclosed C, ?_⟩
  intro x hx
  apply (outsidePrimeCurveEquiv X j q hclosed).injective
  apply NormalProjectiveSurface.PrimeCurve.genericPoint_injective
  simpa only [strictTransformPoint, Equiv.apply_symm_apply] using
    (outsidePrimeCurveEquiv_genericPoint X j q hclosed x).symm.trans hx

/-- The actual irreducible closed support of the strict transform point.
Its carrier is a closure in the whole constructed blowup scheme. -/
def strictTransformClosedSupport (C : X.PrimeCurve) :
    IrreducibleCloseds (scheme j q hclosed) :=
  ⟨closure {(strictTransformPoint X j q hclosed C).val.val},
    isIrreducible_singleton.closure, isClosed_closure⟩

/-- Properness of the actual projection identifies the image of the
whole closed support with the whole original curve. -/
theorem strictTransformClosedSupport_image (C : X.PrimeCurve) :
    (projection j q hclosed).base ''
      (strictTransformClosedSupport X j q hclosed C : Set (scheme j q hclosed)) =
        (C : Set X.toScheme) := by
  letI : IsProper (projection j q hclosed) :=
    projection_isProper_of_fg j q hclosed (X.affine_point_ideal_fg j q)
  change (projection j q hclosed).base ''
    closure {(strictTransformPoint X j q hclosed C).val.val} = _
  rw [← (projection j q hclosed).isClosedMap.closure_image_eq_of_continuous
    (projection j q hclosed).continuous, Set.image_singleton,
    strictTransformPoint_projection, C.closure_genericPoint]

/-- Finite integer sums on the actual source points outside the fiber
are equivalent to the existing Weil divisors of the original surface. -/
def outsideWeilDivisorEquiv :
    (OutsideCodimensionOnePoint X j q hclosed →₀ ℤ) ≃+ X.WeilDivisor :=
  Finsupp.domCongr (outsidePrimeCurveEquiv X j q hclosed)

/-- The construction preserves the integer coefficient of every
corresponding prime generator. -/
theorem outsideWeilDivisorEquiv_coefficient
    (D : OutsideCodimensionOnePoint X j q hclosed →₀ ℤ)
    (x : OutsideCodimensionOnePoint X j q hclosed) :
    outsideWeilDivisorEquiv X j q hclosed D
        (outsidePrimeCurveEquiv X j q hclosed x) = D x := by
  change D ((outsidePrimeCurveEquiv X j q hclosed).symm
    (outsidePrimeCurveEquiv X j q hclosed x)) = D x
  rw [Equiv.symm_apply_apply]

end KltDP.Geometry.PointBlowupGluing
