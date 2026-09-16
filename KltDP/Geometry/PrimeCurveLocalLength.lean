import KltDP.Geometry.PrimeCurveCartierRestriction
import KltDP.Geometry.DivisorOrderLength
import KltDP.Geometry.CartierWeilMap

/-!
# Local lengths of the restricted divisor at DVR points of the curve

For a point `y` of the curve scheme whose stalk `O_{C,y}` is a discrete valuation
ring (the curve is regular at `y`), the local contribution of a nonzero stalk
element `f` is the length of `O_{C,y} ⧸ (f)`. By the accepted `DivisorOrderLength`
it equals the stalk divisor order of `f`, and therefore, for a restricted chart of
`D` at `y`, the Cartier order of `D|_C` at `y` equals the length of the quotient
by the germ of the restricted equation.

The `k`-dimension of `O_{C,y} ⧸ (f)` (length times the residue degree `[κ(y):k]`)
is not proved here; see `F03_RESTRICTION_ADAPTERS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)

/-- Stalks of the integral curve scheme are domains (needed by the DVR predicate). -/
local instance primeCurveLocalLength_stalkIsDomain (y : C.toScheme) :
    IsDomain (C.toScheme.presheaf.stalk y) :=
  integralSchemeStalk_isDomain C.toScheme y

variable (y : C.toScheme)

variable (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)

/-- The germ at `y` of a restricted equation is nonzero (the curve is integral). -/
theorem germ_restrictedCoefficient_ne_zero (hC : C.NotInSupport D hD) (c : C.GenericChart D)
    (hy : y ∈ C.chartPreimage D c.1) :
    C.toScheme.presheaf.germ (C.chartPreimage D c.1) y hy (C.restrictedCoefficient D c.1) ≠ 0 := by
  intro h
  apply C.restrictedCoefficient_ne_zero D hD c.1 c.2 hC
  apply germ_injective_of_isIntegral (X := C.toScheme) y hy
  rw [h, map_zero]

variable [IsDiscreteValuationRing (C.toScheme.presheaf.stalk y)]

/-- The local length of a stalk element: `length (O_{C,y} ⧸ (f))`, as a natural number. -/
def localLength (f : C.toScheme.presheaf.stalk y) : ℕ :=
  (Module.length (C.toScheme.presheaf.stalk y)
    (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f})).toNat

/-- For nonzero `f` the length is finite. -/
theorem localLength_length_ne_top (f : C.toScheme.presheaf.stalk y) (hf : f ≠ 0) :
    Module.length (C.toScheme.presheaf.stalk y)
      (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f}) ≠ ⊤ :=
  stalk_length_quotient_span_ne_top C.toScheme y f hf

/-- The accepted stalk divisor order of a nonzero stalk element is its local length. -/
theorem stalkDivisorOrder_eq_localLength (f : C.toScheme.presheaf.stalk y) (hf : f ≠ 0) :
    stalkDivisorOrder C.toScheme y
        (RingTheory.fractionFieldUnit (C.toScheme.presheaf.stalk y) C.toScheme.functionField f hf) =
      (C.localLength y f : ℤ) :=
  stalkDivisorOrder_eq_quotient_length C.toScheme y f hf

/-- The Cartier order of `D|_C` at a DVR point `y` of the curve is the length of
`O_{C,y} ⧸ (d|_C)` for the restricted equation `d|_C` of any chart of `D` at `y`. -/
theorem cartierOrderAt_restrictCartier_eq_localLength (hC : C.NotInSupport D hD)
    (c : C.GenericChart D) (hy : y ∈ C.chartPreimage D c.1) :
    cartierOrderAt C.toScheme (C.restrictCartier D hD hC) y =
      (C.localLength y (C.toScheme.presheaf.germ (C.chartPreimage D c.1) y hy
        (C.restrictedCoefficient D c.1)) : ℤ) := by
  letI : Nonempty (C.chartPreimage D c.1) := ⟨⟨y, hy⟩⟩
  have hf := C.germ_restrictedCoefficient_ne_zero y D hD hC c hy
  rw [cartierOrderAt_eq_of_equation C.toScheme (C.restrictCartier D hD hC) y
    (C.chartPreimage D c.1) hy (C.restrictedEquation D hD c.1 c.2 hC)
    (C.restrictCartier_spec D hD hC c).symm,
    ← C.stalkDivisorOrder_eq_localLength y _ hf]
  congr 1
  apply Units.ext
  change C.toScheme.germToFunctionField (C.chartPreimage D c.1) (C.restrictedCoefficient D c.1) =
    algebraMap (C.toScheme.presheaf.stalk y) C.toScheme.functionField
      (C.toScheme.presheaf.germ (C.chartPreimage D c.1) y hy (C.restrictedCoefficient D c.1))
  exact (ConcreteCategory.congr_hom (C.toScheme.presheaf.germ_stalkSpecializes hy
    ((genericPoint_spec C.toScheme).specializes trivial)) (C.restrictedCoefficient D c.1)).symm

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
