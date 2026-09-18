import KltDP.Geometry.CartierRationalCoordinate

/-!
# The actual coefficient of a section in an original Cartier frame

The coefficient is the inverse of the accepted equation-section linear
equivalence, after the given actual module identification. Its original
rational germ is the actual rational coordinate times the original equation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.CartierRationalCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] integralSchemeStalk_isDomain

variable (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
    (M : X.Modules) (e : cartierDivisorModule X D ≅ M)
    (c : CartierEquationChart X D)

/-- The regular coefficient of the original section in the actual equation
frame, obtained from the existing linear equivalence. -/
def sectionCoefficient (s : M.val.obj (op c.openSet)) : Γ(X, c.openSet) :=
  (cartierEquationSectionEquiv X D c.openSet c.equation c.represents).symm
    (e.inv.val.app (op c.openSet) s)

/-- This is the coefficient of the literal original frame, not merely a
scalar with the same divisor or generic value. -/
theorem sectionCoefficient_smul_frame (s : M.val.obj (op c.openSet)) :
    sectionCoefficient X D M e c s • frame X D M e c = s := by
  let t := cartierEquationSectionEquiv X D c.openSet c.equation c.represents
  have hf : cartierFrame X D c = t 1 := by
    apply Subtype.ext
    apply (rationalFunctionModuleSectionsEquiv X c.openSet).injective
    rw [cartierFrame_field, cartierEquationSectionEquiv_apply_field, map_one, one_mul]
  have ht : sectionCoefficient X D M e c s • cartierFrame X D c =
      e.inv.val.app (op c.openSet) s := by
    rw [hf, ← t.map_smul]
    simpa only [smul_eq_mul, mul_one] using
      t.apply_symm_apply (e.inv.val.app (op c.openSet) s)
  change sectionCoefficient X D M e c s •
    e.hom.val.app (op c.openSet) (cartierFrame X D c) = s
  rw [← (e.hom.val.app (op c.openSet)).hom.map_smul, ht]
  exact congrArg (fun a : M ⟶ M => a.val.app (op c.openSet) s) e.inv_hom_id

/-- The original structure-sheaf germ of this coefficient is the actual
rational coordinate of the same section multiplied by the equation. -/
theorem sectionCoefficient_field (s : M.val.obj (op c.openSet)) :
    X.germToFunctionField c.openSet (sectionCoefficient X D M e c s) =
      rationalFunctionModuleSectionsEquiv X c.openSet
        ((coordinate X D M e).val.app (op c.openSet) s) *
          (c.equation : X.functionField) := by
  let t := cartierEquationSectionEquiv X D c.openSet c.equation c.represents
  have hv := congrArg
    (fun a : (cartierDivisorModule X D).val.obj (op c.openSet) =>
      rationalFunctionModuleSectionsEquiv X c.openSet a.val)
    (t.apply_symm_apply (e.inv.val.app (op c.openSet) s))
  have hvalue : rationalFunctionModuleSectionsEquiv X c.openSet
      ((coordinate X D M e).val.app (op c.openSet) s) =
    X.germToFunctionField c.openSet (sectionCoefficient X D M e c s) *
      (↑(c.equation⁻¹) : X.functionField) :=
    hv.symm.trans (cartierEquationSectionEquiv_apply_field X D c.openSet
      c.equation c.represents (sectionCoefficient X D M e c s))
  rw [hvalue, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

/-- For an actual nonzero coordinate, the coefficient's original field
image has order equal to the coordinate order plus the Cartier coefficient. -/
theorem sectionCoefficient_order
    (s : M.val.obj (op c.openSet)) (r : X.functionFieldˣ)
    (hr : (r : X.functionField) = rationalFunctionModuleSectionsEquiv X c.openSet
      ((coordinate X D M e).val.app (op c.openSet) s))
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] (hx : x ∈ c.openSet) :
    (r * c.equation : X.functionField) =
        X.germToFunctionField c.openSet (sectionCoefficient X D M e c s) ∧
      stalkDivisorOrder X x (r * c.equation) =
        stalkDivisorOrder X x r + cartierOrderAt X D x := by
  constructor
  · exact (congrArg (fun a : X.functionField => a * (c.equation : X.functionField)) hr).trans
      (sectionCoefficient_field X D M e c s).symm
  · rw [stalkDivisorOrder_mul,
      cartierOrderAt_eq_of_equation X D x c.openSet hx c.equation c.represents]

end KltDP.Geometry.CartierRationalCoordinate

#check @KltDP.Geometry.CartierRationalCoordinate.sectionCoefficient_smul_frame
#check @KltDP.Geometry.CartierRationalCoordinate.sectionCoefficient_order
#print axioms KltDP.Geometry.CartierRationalCoordinate.sectionCoefficient_smul_frame
#print axioms KltDP.Geometry.CartierRationalCoordinate.sectionCoefficient_order
