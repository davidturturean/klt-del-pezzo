import KltDP.Geometry.PointBlowupPrimeCorrespondence
import KltDP.Geometry.ProperOpenDimension
import KltDP.Geometry.IntegralSurfacePointClosure

/-!
# Actual point-blowup dimension and strict-transform curve supports

The actual glued source has dimension two, proved from its integrality,
the proper projection and the actual isomorphism over the puncture. Its
one-dimensional local-ring points therefore have one-dimensional actual
closures. In particular the strict-transform support constructed in the
preceding module is an actual dimension-one irreducible closed subset.

The source is not equipped with an assumed normal-projective-surface
wrapper. All dimension and finite-type inputs used below are derived from
the original surface and the constructed point-blowup projection.
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

/-- The actual glued source's natural field structure is locally of
finite type, as a composite of the proper projection and the original
surface structure morphism. -/
theorem surface_structure_locallyOfFiniteType :
    LocallyOfFiniteType (projection j q hclosed ≫ X.structureMorphism) := by
  letI : IsProper (projection j q hclosed) :=
    projection_isProper_of_fg j q hclosed (X.affine_point_ideal_fg j q)
  letI : LocallyOfFiniteType X.structureMorphism := X.projective.locallyOfFiniteType
  infer_instance

/-- The constructed global blowup has dimension two. The comparison is
proved at an actual closed point of its nonempty isomorphism open. -/
theorem surface_scheme_dimension_two : topologicalKrullDim (scheme j q hclosed) = 2 := by
  letI : IsIntegral (scheme j q hclosed) := surface_scheme_isIntegral X j q hclosed
  letI : IsProper (projection j q hclosed) :=
    projection_isProper_of_fg j q hclosed (X.affine_point_ideal_fg j q)
  letI : LocallyOfFiniteType X.structureMorphism := X.projective.locallyOfFiniteType
  letI : Nonempty (puncture j q hclosed) :=
    puncture_nonempty j q hclosed (X.affine_closed_point_ideal_ne_bot j q hclosed)
  letI : IsIso ((projection j q hclosed) ∣_ puncture j q hclosed) :=
    projection_restrict_puncture_isIso j q hclosed
  exact (topologicalKrullDim_eq_of_proper_isomorphism_open
    (projection j q hclosed) X.structureMorphism (puncture j q hclosed)).trans X.dimension_two

/-- Every actual codimension-one point on the source has a genuinely
one-dimensional closure in the whole constructed scheme. -/
theorem surface_codimensionOnePoint_closure_dimension_one
    (x : CodimensionOnePoint (scheme j q hclosed)) :
    topologicalKrullDim (closure ({x.val} : Set (scheme j q hclosed))) = 1 := by
  letI : IsIntegral (scheme j q hclosed) := surface_scheme_isIntegral X j q hclosed
  letI : LocallyOfFiniteType (projection j q hclosed ≫ X.structureMorphism) :=
    surface_structure_locallyOfFiniteType X j q hclosed
  exact IntegralSurfacePointClosure.codimensionOnePoint_closure_dimension_one
    (scheme j q hclosed) (projection j q hclosed ≫ X.structureMorphism)
    (surface_scheme_dimension_two X j q hclosed) x

/-- The previously constructed strict-transform support has dimension
one, measured in its actual subspace topology. -/
theorem strictTransformClosedSupport_dimension_one (C : X.PrimeCurve) :
    topologicalKrullDim
      (strictTransformClosedSupport X j q hclosed C : Set (scheme j q hclosed)) = 1 :=
  surface_codimensionOnePoint_closure_dimension_one X j q hclosed
    (strictTransformPoint X j q hclosed C).val

/-- The actual strict-transform support, now with its proved dimension
one; this uses exactly the same geometric carrier as the surface curve
definition without assuming missing source normality or projectivity. -/
def strictTransformCurve (C : X.PrimeCurve) :
    {Z : IrreducibleCloseds (scheme j q hclosed) //
      topologicalKrullDim (Z : Set (scheme j q hclosed)) = 1} :=
  ⟨strictTransformClosedSupport X j q hclosed C,
    strictTransformClosedSupport_dimension_one X j q hclosed C⟩

/-- The whole actual strict-transform curve maps onto the whole original
curve under the actual proper blowup projection. -/
theorem strictTransformCurve_image (C : X.PrimeCurve) :
    (projection j q hclosed).base ''
      ((strictTransformCurve X j q hclosed C).val : Set (scheme j q hclosed)) =
        (C : Set X.toScheme) :=
  strictTransformClosedSupport_image X j q hclosed C

end KltDP.Geometry.PointBlowupGluing
