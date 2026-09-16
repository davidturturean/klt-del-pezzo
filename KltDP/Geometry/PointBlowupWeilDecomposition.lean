import KltDP.Geometry.PointBlowupCurveEquiv
import Mathlib.Logic.Equiv.Sum

/-!
# Actual finite divisor sums on the point blowup

Partition the actual dimension-one irreducible closed source curves by
containment in the actual fiber over the center. The complementary curves
are identified with the original surface's prime curves by the proved
puncture correspondence. The pinned finite-support sum equivalence then
gives an additive decomposition with all coefficients preserved.

The fiber summand still consists of actual curves. No uniqueness or
irreducibility of the exceptional fiber is assumed, and no Picard-group,
linear-equivalence, pullback, or intersection formula is asserted.
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

/-- Actual prime curves contained in the whole actual center fiber. -/
def CenterFiberCurve :=
  {C : IntegralSurfacePointClosure.Curve (scheme j q hclosed) //
    (C.val : Set (scheme j q hclosed)) ⊆
      (projection j q hclosed).base ⁻¹' {j.base q}}

/-- All finite integer sums of actual dimension-one irreducible closed
subsets of the constructed source, before quotienting by any relation. -/
abbrev SourceWeilDivisor :=
  IntegralSurfacePointClosure.Curve (scheme j q hclosed) →₀ ℤ

/-- The actual generic point of a curve contained in the fiber maps to
the center, as a consequence of containment of the whole closed curve. -/
theorem centerFiberCurve_genericPoint (C : CenterFiberCurve X j q hclosed) :
    (projection j q hclosed).base
      (IntegralSurfacePointClosure.curveGenericPoint (scheme j q hclosed) C.val) =
        j.base q := by
  have hg := C.val.val.isIrreducible.isGenericPoint_genericPoint C.val.val.isClosed
  exact C.property hg.mem

/-- The complement of actual fiber containment is exactly the existing
nonexceptional curve type; its underlying curve does not change. -/
def notCenterFiberCurveEquiv :
    {C : IntegralSurfacePointClosure.Curve (scheme j q hclosed) //
      ¬ (C.val : Set (scheme j q hclosed)) ⊆
        (projection j q hclosed).base ⁻¹' {j.base q}} ≃
      OutsidePrimeCurve X j q hclosed :=
  (Equiv.refl (IntegralSurfacePointClosure.Curve (scheme j q hclosed))).subtypeEquiv
    (fun C => curve_not_in_center_fiber_iff X j q hclosed C)

/-- Every actual source prime curve is either an actual curve in the
fiber or the unique nonexceptional curve corresponding to an original prime. -/
def sourceCurveSumEquiv :
    IntegralSurfacePointClosure.Curve (scheme j q hclosed) ≃
      CenterFiberCurve X j q hclosed ⊕ X.PrimeCurve := by
  classical
  exact (Equiv.sumCompl (fun C : IntegralSurfacePointClosure.Curve (scheme j q hclosed) =>
    (C.val : Set (scheme j q hclosed)) ⊆
      (projection j q hclosed).base ⁻¹' {j.base q})).symm.trans
    (Equiv.sumCongr (Equiv.refl _)
      ((notCenterFiberCurveEquiv X j q hclosed).trans
        (outsideCurveEquiv X j q hclosed)))

/-- The inverse on the fiber side retains precisely the actual curve. -/
theorem sourceCurveSumEquiv_symm_inl (C : CenterFiberCurve X j q hclosed) :
    (sourceCurveSumEquiv X j q hclosed).symm (Sum.inl C) = C.val := rfl

/-- The inverse on the original-surface side is the established actual
strict-transform curve, not a new chosen label. -/
theorem sourceCurveSumEquiv_symm_inr (C : X.PrimeCurve) :
    (sourceCurveSumEquiv X j q hclosed).symm (Sum.inr C) =
      ((outsideCurveEquiv X j q hclosed).symm C).val := rfl

theorem sourceCurveSumEquiv_apply_center (C : CenterFiberCurve X j q hclosed) :
    sourceCurveSumEquiv X j q hclosed C.val = Sum.inl C := by
  simpa only [sourceCurveSumEquiv_symm_inl] using
    (sourceCurveSumEquiv X j q hclosed).apply_symm_apply (Sum.inl C)

theorem sourceCurveSumEquiv_apply_outside (C : OutsidePrimeCurve X j q hclosed) :
    sourceCurveSumEquiv X j q hclosed C.val =
      Sum.inr (outsideCurveEquiv X j q hclosed C) := by
  apply (sourceCurveSumEquiv X j q hclosed).symm.injective
  rw [Equiv.symm_apply_apply, sourceCurveSumEquiv_symm_inr, Equiv.symm_apply_apply]

/-- An additive decomposition of actual finite divisor sums. The first
summand retains all actual curves over the center; the second is the
existing original surface's actual Weil-divisor group. -/
def sourceWeilDecomposition :
    SourceWeilDivisor X j q hclosed ≃+
      (CenterFiberCurve X j q hclosed →₀ ℤ) × X.WeilDivisor :=
  (Finsupp.domCongr (sourceCurveSumEquiv X j q hclosed)).trans
    Finsupp.sumFinsuppAddEquivProdFinsupp

/-- Every coefficient over the center is unchanged. -/
theorem sourceWeilDecomposition_center_coefficient
    (D : SourceWeilDivisor X j q hclosed) (C : CenterFiberCurve X j q hclosed) :
    (sourceWeilDecomposition X j q hclosed D).1 C = D C.val := by
  change D ((sourceCurveSumEquiv X j q hclosed).symm (Sum.inl C)) = D C.val
  rw [sourceCurveSumEquiv_symm_inl]

/-- Each coefficient on the original surface is the coefficient of its
actual corresponding nonexceptional source curve. -/
theorem sourceWeilDecomposition_original_coefficient
    (D : SourceWeilDivisor X j q hclosed) (C : X.PrimeCurve) :
    (sourceWeilDecomposition X j q hclosed D).2 C =
      D ((outsideCurveEquiv X j q hclosed).symm C).val := by
  change D ((sourceCurveSumEquiv X j q hclosed).symm (Sum.inr C)) = _
  rw [sourceCurveSumEquiv_symm_inr]

end KltDP.Geometry.PointBlowupGluing
