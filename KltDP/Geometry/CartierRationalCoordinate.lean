import KltDP.Geometry.CartierFrames
import KltDP.Geometry.CartierWeilMap

/-!
# The original rational coordinate determined by a Cartier module isomorphism

An actual isomorphism O(D) ≅ M gives the map M → K_X obtained from its
inverse and the original fractional-module inclusion. Thus it records
the rational choice in the isomorphism. The image of the actual Cartier
frame has coordinate f⁻¹ for the original equation f. At any original
DVR stalk, the negative order of this coordinate is cartierOrderAt D.
No global Weil-divisor packaging or new generic stalk module is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierRationalCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The actual fractional-module inclusion transported by the given
module isomorphism. This retains the rational choice in that isomorphism. -/
def coordinate (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
    (M : X.Modules) (e : cartierDivisorModule X D ≅ M) :
    M ⟶ rationalFunctionModule X :=
  e.inv ≫ cartierDivisorModuleInclusion X D

/-- Its composition with the original Cartier-module identification is
the original inclusion, with no scalar correction. -/
theorem hom_comp_coordinate (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
    (M : X.Modules) (e : cartierDivisorModule X D ≅ M) :
    e.hom ≫ coordinate X D M e = cartierDivisorModuleInclusion X D := by
  simp only [coordinate, Iso.hom_inv_id_assoc]

/-- The actual section of M obtained from the original Cartier frame. -/
def frame (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
    (M : X.Modules) (e : cartierDivisorModule X D ≅ M)
    (c : CartierEquationChart X D) : M.val.obj (op c.openSet) :=
  e.hom.val.app (op c.openSet) (cartierFrame X D c)

/-- The chosen module isomorphism retains the exact inverse original
equation as the rational value of the induced local frame. -/
theorem coordinate_frame_value (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
    (M : X.Modules) (e : cartierDivisorModule X D ≅ M)
    (c : CartierEquationChart X D) :
    rationalFunctionModuleSectionsEquiv X c.openSet
      ((coordinate X D M e).val.app (op c.openSet) (frame X D M e c)) =
        ((c.equation⁻¹ : X.functionFieldˣ) : X.functionField) := by
  have h := congrArg (fun t : cartierDivisorModule X D ⟶ rationalFunctionModule X =>
    rationalFunctionModuleSectionsEquiv X c.openSet
      (t.val.app (op c.openSet) (cartierFrame X D c))) (hom_comp_coordinate X D M e)
  exact h.trans (cartierFrame_field X D c)

/-- The actual frame coordinate is nonzero, without a nonzero premise. -/
theorem coordinate_frame_value_ne_zero (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
    (M : X.Modules) (e : cartierDivisorModule X D ≅ M)
    (c : CartierEquationChart X D) :
    rationalFunctionModuleSectionsEquiv X c.openSet
      ((coordinate X D M e).val.app (op c.openSet) (frame X D M e c)) ≠ 0 := by
  rw [coordinate_frame_value]
  exact Units.ne_zero _

/-- The unit of the original function field formed from that actual
nonzero coordinate, rather than from an independently chosen function. -/
def frameValueUnit (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
    (M : X.Modules) (e : cartierDivisorModule X D ≅ M)
    (c : CartierEquationChart X D) : X.functionFieldˣ :=
  Units.mk0 (rationalFunctionModuleSectionsEquiv X c.openSet
    ((coordinate X D M e).val.app (op c.openSet) (frame X D M e c)))
      (coordinate_frame_value_ne_zero X D M e c)

theorem frameValueUnit_eq (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
    (M : X.Modules) (e : cartierDivisorModule X D ≅ M)
    (c : CartierEquationChart X D) : frameValueUnit X D M e c = c.equation⁻¹ :=
  Units.ext (coordinate_frame_value X D M e c)

local instance integralStalkDomain (X : Scheme.{u}) [IsIntegral X] (x : X) :
    IsDomain (X.presheaf.stalk x) := integralSchemeStalk_isDomain X x

/-- Pointwise order normalization works on every integral scheme at
every actual DVR stalk, without a normal-projective-surface package. -/
theorem cartierOrderAt_eq_neg_frame_order (X : Scheme.{u}) [IsIntegral X]
    (D : CartierDivisor X) (M : X.Modules) (e : cartierDivisorModule X D ≅ M)
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (c : CartierEquationChart X D) (hx : x ∈ c.openSet) :
    cartierOrderAt X D x = -stalkDivisorOrder X x (frameValueUnit X D M e c) := by
  rw [frameValueUnit_eq, stalkDivisorOrder_inv, neg_neg]
  exact cartierOrderAt_eq_of_equation X D x c.openSet hx c.equation c.represents

end KltDP.Geometry.CartierRationalCoordinate

#check @KltDP.Geometry.CartierRationalCoordinate.coordinate
#check @KltDP.Geometry.CartierRationalCoordinate.coordinate_frame_value
#check @KltDP.Geometry.CartierRationalCoordinate.cartierOrderAt_eq_neg_frame_order
#print axioms KltDP.Geometry.CartierRationalCoordinate.coordinate_frame_value
#print axioms KltDP.Geometry.CartierRationalCoordinate.cartierOrderAt_eq_neg_frame_order
