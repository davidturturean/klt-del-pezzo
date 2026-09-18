import KltDP.Geometry.NormalModelLocalFrameConstructor
import KltDP.Geometry.CanonicalPrincipalShiftCoordinate

/-!
# Principal rescaling of an actual local canonical frame

The actual neighborhood, model map and point are retained. The original
Cartier principal shift constructs the corrected canonical identification;
the original local equation theorem supplies its equation chart. The frame
order changes by the precise original scalar order.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical.LocalFrame

open CartierRationalCoordinate

attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] {V : Scheme.{u}} [IsIntegral V]
    {σ : V ⟶ Spec (CommRingCat.of k)} {x : V} (F : LocalFrame σ x)

/-- Correct the actual canonical identification, retaining the original model point. -/
def rescale (q : F.neighborhood.functionFieldˣ) : LocalFrame σ x := by
  letI : IsSmoothOfRelativeDimension 2 (F.toModel ≫ σ) := F.smooth
  exact ofCanonicalDivisor σ F.toModel F.point x F.point_eq
    (rescaleDivisor F.neighborhood F.divisor q)
    (rescaleIso F.neighborhood F.divisor
      (SmoothCanonicalExteriorComparison.relativeDifferentialExterior (F.toModel ≫ σ) 2)
      F.canonicalIso q)

/-- The corrected frame has the exact original rational-coordinate multiplier. -/
theorem rescale_coordinate (q : F.neighborhood.functionFieldˣ) :
    coordinate (F.rescale q).neighborhood (F.rescale q).divisor
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior
          ((F.rescale q).toModel ≫ σ) 2) (F.rescale q).canonicalIso =
      coordinate F.neighborhood F.divisor
          (SmoothCanonicalExteriorComparison.relativeDifferentialExterior (F.toModel ≫ σ) 2)
          F.canonicalIso ≫
        (rationalFunctionMulIso F.neighborhood q).hom := by
  exact coordinate_rescaleIso F.neighborhood F.divisor
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior (F.toModel ≫ σ) 2)
    F.canonicalIso q

/-- The order correction uses the original point on the same neighborhood. -/
theorem rescale_order [IsDiscreteValuationRing (V.presheaf.stalk x)]
    (q : F.neighborhood.functionFieldˣ) :
    (F.rescale q).order = F.order - stalkDivisorOrder F.neighborhood F.point q := by
  calc
    _ = cartierOrderAt F.neighborhood (rescaleDivisor F.neighborhood F.divisor q)
        F.point := order_eq_cartierOrderAt (F.rescale q)
    _ = cartierOrderAt F.neighborhood F.divisor F.point -
        stalkDivisorOrder F.neighborhood F.point q :=
      rescaleDivisor_order F.neighborhood F.divisor q F.point
    _ = _ := congrArg (fun n : ℤ => n - stalkDivisorOrder F.neighborhood F.point q)
      (order_eq_cartierOrderAt F).symm

end KltDP.Geometry.NormalModelCanonical.LocalFrame

#check @KltDP.Geometry.NormalModelCanonical.LocalFrame.rescale_coordinate
#print axioms KltDP.Geometry.NormalModelCanonical.LocalFrame.rescale_coordinate
#check @KltDP.Geometry.NormalModelCanonical.LocalFrame.rescale_order
#print axioms KltDP.Geometry.NormalModelCanonical.LocalFrame.rescale_order
