import KltDP.Geometry.PointBlowupCurveDimension
import KltDP.Geometry.IntegralSurfacePrimeCurve

/-!
# Actual nonexceptional prime curves of the point blowup

The already constructed source is integral, finite type, and dimension
two. Its actual dimension-one irreducible closed curves are therefore
identified by their actual codimension-one generic points. Restricting
to the complement of the actual exceptional fiber and using the actual
puncture isomorphism yields the desired whole prime-curve correspondence.

No source surface wrapper, prime correspondence, Picard lattice or
intersection formula is an assumed input. Finite integer sums on the
actual nonexceptional curves are transported to the original Weil divisors.
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

/-- Actual dimension-one irreducible closed source curves whose actual
generic point does not map to the selected center. -/
def OutsidePrimeCurve :=
  {C : IntegralSurfacePointClosure.Curve (scheme j q hclosed) //
    (projection j q hclosed).base
      (IntegralSurfacePointClosure.curveGenericPoint (scheme j q hclosed) C) ≠ j.base q}

/-- The generic-point exclusion is exactly the geometric statement that
the actual whole curve is not contained in the actual exceptional fiber. -/
theorem curve_not_in_center_fiber_iff
    (C : IntegralSurfacePointClosure.Curve (scheme j q hclosed)) :
    ¬ (C.val : Set (scheme j q hclosed)) ⊆
        (projection j q hclosed).base ⁻¹' {j.base q} ↔
      (projection j q hclosed).base
        (IntegralSurfacePointClosure.curveGenericPoint (scheme j q hclosed) C) ≠ j.base q := by
  have hgeneric := C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed
  have hclosedFiber : IsClosed ((projection j q hclosed).base ⁻¹' {j.base q}) :=
    hclosed.preimage (projection j q hclosed).continuous
  exact not_congr (hgeneric.mem_closed_set_iff hclosedFiber).symm

/-- The actual nonexceptional prime curves are identified with the
already constructed codimension-one points outside the exceptional fiber. -/
def outsideCurvePointEquiv :
    OutsidePrimeCurve X j q hclosed ≃ OutsideCodimensionOnePoint X j q hclosed := by
  letI : IsIntegral (scheme j q hclosed) := surface_scheme_isIntegral X j q hclosed
  letI : LocallyOfFiniteType (projection j q hclosed ≫ X.structureMorphism) :=
    surface_structure_locallyOfFiniteType X j q hclosed
  exact (IntegralSurfacePointClosure.curveCodimensionOneEquiv
    (scheme j q hclosed) (projection j q hclosed ≫ X.structureMorphism)
    (surface_scheme_dimension_two X j q hclosed)).subtypeEquiv (fun _ => Iff.rfl)

/-- Every original prime curve corresponds to exactly one actual
nonexceptional prime curve of the constructed blowup. -/
def outsideCurveEquiv : OutsidePrimeCurve X j q hclosed ≃ X.PrimeCurve :=
  (outsideCurvePointEquiv X j q hclosed).trans (outsidePrimeCurveEquiv X j q hclosed)

/-- The actual proper projection sends the generic point of the source
curve to the generic point of the corresponding original curve. -/
theorem outsideCurveEquiv_genericPoint (C : OutsidePrimeCurve X j q hclosed) :
    (projection j q hclosed).base
        (IntegralSurfacePointClosure.curveGenericPoint (scheme j q hclosed) C.val) =
      (outsideCurveEquiv X j q hclosed C).genericPoint := by
  exact outsidePrimeCurveEquiv_genericPoint X j q hclosed
    (outsideCurvePointEquiv X j q hclosed C)

/-- The point correspondence identifies the whole actual curve image,
not only its generic point. -/
theorem outsideCurveEquiv_image (C : OutsidePrimeCurve X j q hclosed) :
    (projection j q hclosed).base '' (C.val.val : Set (scheme j q hclosed)) =
      (outsideCurveEquiv X j q hclosed C : Set X.toScheme) := by
  letI : IsIntegral (scheme j q hclosed) := surface_scheme_isIntegral X j q hclosed
  letI : IsProper (projection j q hclosed) :=
    projection_isProper_of_fg j q hclosed (X.affine_point_ideal_fg j q)
  rw [← IntegralSurfacePointClosure.curveGenericPoint_closure (scheme j q hclosed) C.val,
    ← (projection j q hclosed).isClosedMap.closure_image_eq_of_continuous
      (projection j q hclosed).continuous,
    Set.image_singleton, outsideCurveEquiv_genericPoint,
    NormalProjectiveSurface.PrimeCurve.closure_genericPoint]

/-- Finite integer sums on actual nonexceptional prime curves are
equivalent to the existing Weil divisors of the original surface. -/
def outsideCurveWeilEquiv :
    (OutsidePrimeCurve X j q hclosed →₀ ℤ) ≃+ X.WeilDivisor :=
  Finsupp.domCongr (outsideCurveEquiv X j q hclosed)

theorem outsideCurveWeilEquiv_coefficient
    (D : OutsidePrimeCurve X j q hclosed →₀ ℤ)
    (C : OutsidePrimeCurve X j q hclosed) :
    outsideCurveWeilEquiv X j q hclosed D
        (outsideCurveEquiv X j q hclosed C) = D C := by
  change D ((outsideCurveEquiv X j q hclosed).symm
    (outsideCurveEquiv X j q hclosed C)) = D C
  rw [Equiv.symm_apply_apply]

end KltDP.Geometry.PointBlowupGluing
