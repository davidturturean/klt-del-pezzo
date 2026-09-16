import KltDP.Geometry.PointBlowupCurveDimension
import KltDP.Geometry.IsomorphismOpenPointClosure

/-!
# The conventional strict-transform support on the actual point blowup

The previously constructed strict-transform point and curve are identified
with the closure of the whole inverse image of the original curve away
from the selected closed point. On that open, the support is exactly the
whole inverse image. This relates the actual generic-point construction
to the usual geometric definition, without assuming a closure comparison.

This is a statement about actual closed supports. It does not identify
the ideal sheaf of a schematic closure or a divisor class.
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

/-- The actual point-closure support is the conventional strict transform:
the closure of the whole inverse image of the original curve off the center. -/
theorem strictTransformClosedSupport_eq_closure_preimage (C : X.PrimeCurve) :
    (strictTransformClosedSupport X j q hclosed C : Set (scheme j q hclosed)) =
      closure ((projection j q hclosed).base ⁻¹'
        ((C : Set X.toScheme) \ {j.base q})) := by
  letI : IsIso ((projection j q hclosed) ∣_ puncture j q hclosed) :=
    projection_restrict_puncture_isIso j q hclosed
  change closure ({(strictTransformPoint X j q hclosed C).val.val} :
      Set (scheme j q hclosed)) =
    closure ((projection j q hclosed).base ⁻¹'
      ((C : Set X.toScheme) ∩ (puncture j q hclosed : Set X.toScheme)))
  exact (closure_preimage_inter_eq_lifted_point_closure
    (projection j q hclosed) (puncture j q hclosed) C.closure_genericPoint
    (codimensionOnePoint_mem_puncture X j q hclosed
      (X.primeCurveToCodimensionOnePoint C))
    (strictTransformPoint X j q hclosed C).val.val
    (strictTransformPoint_projection X j q hclosed C)).symm

/-- On the actual center complement, no points are added to the full
inverse image when its closure is taken in the entire blowup. -/
theorem strictTransformClosedSupport_inter_puncture (C : X.PrimeCurve) :
    (strictTransformClosedSupport X j q hclosed C : Set (scheme j q hclosed)) ∩
        ((projection j q hclosed) ⁻¹ᵁ puncture j q hclosed :
          Set (scheme j q hclosed)) =
      (projection j q hclosed).base ⁻¹'
        ((C : Set X.toScheme) \ {j.base q}) := by
  apply Set.ext
  intro z
  constructor
  · rintro ⟨hzC, hzU⟩
    have hzImage := Set.mem_image_of_mem (projection j q hclosed).base hzC
    rw [strictTransformClosedSupport_image X j q hclosed C] at hzImage
    exact ⟨hzImage, hzU⟩
  · intro hz
    refine ⟨?_, hz.2⟩
    rw [strictTransformClosedSupport_eq_closure_preimage]
    exact subset_closure hz

/-- The dimension-one actual curve constructed earlier has precisely
the support in the conventional strict-transform definition. -/
theorem strictTransformCurve_support_eq_closure_preimage (C : X.PrimeCurve) :
    ((strictTransformCurve X j q hclosed C).val : Set (scheme j q hclosed)) =
      closure ((projection j q hclosed).base ⁻¹'
        ((C : Set X.toScheme) \ {j.base q})) :=
  strictTransformClosedSupport_eq_closure_preimage X j q hclosed C

end KltDP.Geometry.PointBlowupGluing
