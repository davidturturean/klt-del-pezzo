import KltDP.Geometry.CartierMapCoefficientOrder
import KltDP.Geometry.OriginalDifferentialImageSection

/-!
# Coefficient order for the original differential image

The original imageSection is expanded with abstract original schemes and
ground morphisms. The field-value input is the actual differential applied
to the original pullback section; the coefficient and signed order are
obtained from the proved abstract module-map calculation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.OriginalDifferentialCoefficientOrder

open CartierRationalCoordinate NormalizedDifferentialCoefficientOrder

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] integralSchemeStalk_isDomain

/-- The literal original differential image has the Cartier-difference
order once its established coordinate value on the target frame is supplied. -/
theorem coefficient_order
    {k : Type u} [CommRing k] {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (sA : A ⟶ Spec (CommRingCat.of k)) (sB : B ⟶ Spec (CommRingCat.of k))
    (q : B ⟶ A) [GenericPointPreserving q] (hq : q ≫ sA = sB)
    (DA : CartierDivisor A) (DB : CartierDivisor B)
    (eA : cartierDivisorModule A DA ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2)
    (eB : cartierDivisorModule B DB ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2)
    (cS : CartierEquationChart B DB) (cT : CartierEquationChart A DA)
    (hST : cS.openSet ≤ q ⁻¹ᵁ cT.openSet)
    (hvalue : rationalFunctionModuleSectionsEquiv B (q ⁻¹ᵁ cT.openSet)
        ((coordinate B DB (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2)
            eB).val.app (op (q ⁻¹ᵁ cT.openSet))
          ((SchemeKaehlerExteriorPullbackTransport.map sA q sB hq 2).val.app
            (op (q ⁻¹ᵁ cT.openSet))
              (pullbackSection q (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2)
                cT.openSet (frame A DA
                  (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eA cT)))) =
      functionFieldMap q (rationalFunctionModuleSectionsEquiv A cT.openSet
        ((coordinate A DA (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2)
            eA).val.app (op cT.openSet)
          (frame A DA (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eA cT))))
    (y : B) [IsDiscreteValuationRing (B.presheaf.stalk y)] (hy : y ∈ cS.openSet) :
    let M := SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2
    let t := imageSection sA sB q hq cT.openSet
      (frame A DA (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eA cT)
    let s := M.val.map (homOfLE hST).op t
    let r := Units.map (functionFieldMap q).hom.toMonoidHom cT.equation⁻¹ * cS.equation
    (r : B.functionField) = B.germToFunctionField cS.openSet
        (sectionCoefficient B DB M eB cS s) ∧
      stalkDivisorOrder B y r =
        cartierOrderAt B DB y -
          cartierOrderAt B (DominantCartierPullback.pullbackHom q DA) y := by
  exact CartierMapCoefficientOrder.coefficient_order_of_frame_value q DA DB
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2)
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2)
    eA eB (SchemeKaehlerExteriorPullbackTransport.map sA q sB hq 2)
    cS cT hST hvalue y hy

end KltDP.Geometry.OriginalDifferentialCoefficientOrder

#check @KltDP.Geometry.OriginalDifferentialCoefficientOrder.coefficient_order
#print axioms KltDP.Geometry.OriginalDifferentialCoefficientOrder.coefficient_order
