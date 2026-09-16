import KltDP.Geometry.DivisorOrder
import KltDP.Geometry.NormalStalkDVR

/-!
# Orders of rational functions along actual prime curves

The generic-point DVR property is proved for each prime curve, so these
orders require no additional local-dimension or valuation-ring hypotheses.
They specialize the existing stalk valuation homomorphism. The family of
orders takes values in a function space; finite principal support must be
proved before it defines a finitely supported Weil divisor.
-/

noncomputable section

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}

local instance (C : X.PrimeCurve) : IsDiscreteValuationRing (X.stalk C.genericPoint) :=
  C.genericPoint_isDiscreteValuationRing

/-- The integer order along the actual curve, on nonzero rational functions
of the original surface. -/
def orderHom (C : X.PrimeCurve) : Additive X.toScheme.functionFieldˣ →+ ℤ :=
  stalkDivisorOrderHom X.toScheme C.genericPoint

def order (C : X.PrimeCurve) (f : X.toScheme.functionFieldˣ) : ℤ :=
  C.orderHom (Additive.ofMul f)

theorem order_eq_stalkDivisorOrder (C : X.PrimeCurve)
    (f : X.toScheme.functionFieldˣ) :
    C.order f = stalkDivisorOrder X.toScheme C.genericPoint f := rfl

@[simp] theorem order_one (C : X.PrimeCurve) : C.order 1 = 0 :=
  C.orderHom.map_zero

theorem order_mul (C : X.PrimeCurve) (f g : X.toScheme.functionFieldˣ) :
    C.order (f * g) = C.order f + C.order g :=
  C.orderHom.map_add (Additive.ofMul f) (Additive.ofMul g)

@[simp] theorem order_inv (C : X.PrimeCurve) (f : X.toScheme.functionFieldˣ) :
    C.order f⁻¹ = -C.order f :=
  C.orderHom.map_neg (Additive.ofMul f)

/-- Units in the actual generic-point local ring have order zero. -/
@[simp] theorem order_map_local_unit (C : X.PrimeCurve)
    (r : (X.stalk C.genericPoint)ˣ) :
    C.order (Units.map (algebraMap (X.stalk C.genericPoint) X.toScheme.functionField) r) =
      0 :=
  stalkDivisorOrder_map_unit X.toScheme C.genericPoint r

/-- A local uniformizer supplies an actual rational function of order one.
This also checks the order's sign convention and nontriviality. -/
theorem exists_order_one (C : X.PrimeCurve) :
    ∃ f : X.toScheme.functionFieldˣ, C.order f = 1 := by
  obtain ⟨r, hr, horder⟩ := RingTheory.exists_uniformizer_divisorOrder_one
    (X.stalk C.genericPoint) X.toScheme.functionField
  exact ⟨RingTheory.fractionFieldUnit (X.stalk C.genericPoint)
    X.toScheme.functionField r hr.ne_zero, horder⟩

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
