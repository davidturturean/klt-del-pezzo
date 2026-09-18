import KltDP.Geometry.CartierRationalCoordinate
import KltDP.Geometry.CartierPrincipalShift

/-!
# Coordinates of the same actual module under its original scalar comparison

The inclusion square for the original change of Cartier-module identification
determines the coordinates on that same module, including their values on
the original Cartier frames. This is a generic consumer of the inclusion
square; it does not replace the separate theorem producing its multiplier.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.CartierRationalCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] (D E : CartierDivisor X)
    (M : X.Modules) (eD : cartierDivisorModule X D ≅ M)
    (eE : cartierDivisorModule X E ≅ M) (q : X.functionFieldˣ)
    (hq : (eD ≪≫ eE.symm).hom ≫ cartierDivisorModuleInclusion X E =
      cartierDivisorModuleInclusion X D ≫ (rationalFunctionMulIso X q).hom)

include hq

/-- The coordinate change uses the scalar of the given module isomorphisms. -/
theorem coordinate_eq_mul_of_inclusion :
    coordinate X E M eE =
      coordinate X D M eD ≫ (rationalFunctionMulIso X q).hom := by
  have h := congrArg
    (fun f : cartierDivisorModule X D ⟶ rationalFunctionModule X => eD.inv ≫ f) hq
  simpa only [coordinate, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc] using h

/-- The same comparison holds in the original function field on every
nonempty open, for every original section of the common module. -/
theorem coordinate_value_eq_mul_of_inclusion (U : X.Opens) [Nonempty U]
    (s : M.val.obj (op U)) :
    rationalFunctionModuleSectionsEquiv X U
        ((coordinate X E M eE).val.app (op U) s) =
      (q : X.functionField) * rationalFunctionModuleSectionsEquiv X U
        ((coordinate X D M eD).val.app (op U) s) := by
  have h := congrArg (fun f : M ⟶ rationalFunctionModule X =>
    rationalFunctionModuleSectionsEquiv X U (f.val.app (op U) s))
    (coordinate_eq_mul_of_inclusion X D E M eD eE q hq)
  exact h.trans (rationalFunctionMulIso_hom_app_field X q U
    ((coordinate X D M eD).val.app (op U) s))

/-- The original D-frame has its actual E-coordinate q/f. -/
theorem coordinate_frame_value_eq_mul_of_inclusion (c : CartierEquationChart X D) :
    rationalFunctionModuleSectionsEquiv X c.openSet
        ((coordinate X E M eE).val.app (op c.openSet) (frame X D M eD c)) =
      (q : X.functionField) * (↑(c.equation⁻¹) : X.functionField) := by
  rw [coordinate_value_eq_mul_of_inclusion X D E M eD eE q hq,
    coordinate_frame_value]

end KltDP.Geometry.CartierRationalCoordinate

#check @KltDP.Geometry.CartierRationalCoordinate.coordinate_frame_value_eq_mul_of_inclusion
#print axioms KltDP.Geometry.CartierRationalCoordinate.coordinate_frame_value_eq_mul_of_inclusion
