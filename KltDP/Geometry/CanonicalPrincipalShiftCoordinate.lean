import KltDP.Geometry.CartierRationalCoordinateOpenPullback
import KltDP.Geometry.CartierPrincipalShift
import KltDP.Geometry.CartierWeilMap

/-!
# Actual principal shifts of canonical coordinates

The existing principal-shift isomorphism changes the given rational coordinate
by the corresponding original unit. Its original DVR order changes by precisely
the negative order of that same unit. No regularity of the scalar near the point
or coordinate-compatibility assertion is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.CartierRationalCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] integralSchemeStalk_isDomain

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual inverse multiplication by q⁻¹ is multiplication by q. -/
theorem rationalFunctionMulIso_inv_inv (q : X.functionFieldˣ) :
    (rationalFunctionMulIso X q⁻¹).inv = (rationalFunctionMulIso X q).hom := by
  classical
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  by_cases hU : Nonempty U.unop
  · letI := hU
    apply (rationalFunctionModuleSectionsEquiv X U.unop).injective
    exact (rationalFunctionMulIso_inv_app_field X q⁻¹ U.unop s).trans
      ((congrArg (fun r : X.functionFieldˣ =>
        (r : X.functionField) * rationalFunctionModuleSectionsEquiv X U.unop s)
        (inv_inv q)).trans (rationalFunctionMulIso_hom_app_field X q U.unop s).symm)
  · letI := OpenImmersionRational.sectionRing_subsingleton_of_empty U.unop hU
    letI : Subsingleton ((rationalFunctionModule X).val.obj U) :=
      Module.subsingleton Γ(X, U.unop) _
    exact Subsingleton.elim _ _

/-- The actual Cartier correction which multiplies the given coordinate by q. -/
def rescaleDivisor (D : CartierDivisor X) (q : X.functionFieldˣ) : CartierDivisor X :=
  D + principalCartierDivisorHom X (Additive.ofMul q⁻¹)

/-- The original principal-shift map followed by the given identification. -/
def rescaleIso (D : CartierDivisor X) (M : X.Modules)
    (e : cartierDivisorModule X D ≅ M) (q : X.functionFieldˣ) :
    cartierDivisorModule X (rescaleDivisor X D q) ≅ M :=
  cartierPrincipalShiftIso X D q⁻¹ ≪≫ e

/-- Rescaling retains the literal given coordinate and actual multiplication map. -/
theorem coordinate_rescaleIso (D : CartierDivisor X) (M : X.Modules)
    (e : cartierDivisorModule X D ≅ M) (q : X.functionFieldˣ) :
    coordinate X (rescaleDivisor X D q) M (rescaleIso X D M e q) =
      coordinate X D M e ≫ (rationalFunctionMulIso X q).hom := by
  calc
    _ = coordinate X D M e ≫ (rationalFunctionMulIso X q⁻¹).inv := by
      simp only [coordinate, rescaleIso, rescaleDivisor, Iso.trans_inv, Category.assoc]
      rw [cartierPrincipalShiftIso_inv_inclusion]
    _ = _ := congrArg (fun a => coordinate X D M e ≫ a)
      (rationalFunctionMulIso_inv_inv X q)

/-- The correction has exactly its original principal order, with fixed sign. -/
theorem rescaleDivisor_order (D : CartierDivisor X) (q : X.functionFieldˣ)
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    cartierOrderAt X (rescaleDivisor X D q) x =
      cartierOrderAt X D x - stalkDivisorOrder X x q := by
  rw [rescaleDivisor, cartierOrderAt_add, cartierOrderAt_principal,
    stalkDivisorOrder_inv, sub_eq_add_neg]

/-- An actually proved zero scalar order leaves the original Cartier order unchanged. -/
theorem rescaleDivisor_order_of_zero (D : CartierDivisor X) (q : X.functionFieldˣ)
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hq : stalkDivisorOrder X x q = 0) :
    cartierOrderAt X (rescaleDivisor X D q) x = cartierOrderAt X D x := by
  rw [rescaleDivisor_order, hq, sub_zero]

end KltDP.Geometry.CartierRationalCoordinate

#check @KltDP.Geometry.CartierRationalCoordinate.coordinate_rescaleIso
#print axioms KltDP.Geometry.CartierRationalCoordinate.coordinate_rescaleIso
#check @KltDP.Geometry.CartierRationalCoordinate.rescaleDivisor_order
#print axioms KltDP.Geometry.CartierRationalCoordinate.rescaleDivisor_order
