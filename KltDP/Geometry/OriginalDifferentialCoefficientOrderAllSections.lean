import KltDP.Geometry.OriginalDifferentialCoefficientOrder

/-!
# Specialize the original all-section value before choosing a canonical frame

The already-proved coefficient-order theorem is applied with abstract
original schemes, Cartier divisors and module identifications. In this
context the original all-section value is specialized to the actual target
frame. The concrete canonical pullback is substituted only by the consumer.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.OriginalDifferentialCoefficientOrder

open CartierRationalCoordinate NormalizedDifferentialCoefficientOrder

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] integralSchemeStalk_isDomain

/-- Original value compatibility on all sections gives the original
coefficient and signed Cartier order on the actual target frame. -/
theorem coefficient_order_of_all_section_values
    {k : Type u} [CommRing k] {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (sA : A ⟶ Spec (CommRingCat.of k)) (sB : B ⟶ Spec (CommRingCat.of k))
    (q : B ⟶ A) [GenericPointPreserving q] (hq : q ≫ sA = sB)
    (DA : CartierDivisor A) (DB : CartierDivisor B)
    (eA : cartierDivisorModule A DA ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2)
    (eB : cartierDivisorModule B DB ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2)
    (hvalues : ∀ (T : A.Opens) [Nonempty T]
        (s : (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2).val.obj
          (op T)),
      rationalFunctionModuleSectionsEquiv B (q ⁻¹ᵁ T)
        ((coordinate B DB (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2)
            eB).val.app (op (q ⁻¹ᵁ T))
          ((SchemeKaehlerExteriorPullbackTransport.map sA q sB hq 2).val.app
            (op (q ⁻¹ᵁ T))
              (pullbackSection q (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2)
                T s))) =
        functionFieldMap q (rationalFunctionModuleSectionsEquiv A T
          ((coordinate A DA (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2)
            eA).val.app (op T) s)))
    (cS : CartierEquationChart B DB) (cT : CartierEquationChart A DA)
    (hST : cS.openSet ≤ q ⁻¹ᵁ cT.openSet)
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
  exact coefficient_order sA sB q hq DA DB eA eB cS cT hST
    (hvalues cT.openSet
      (frame A DA (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eA cT))
    y hy

end KltDP.Geometry.OriginalDifferentialCoefficientOrder

#check @KltDP.Geometry.OriginalDifferentialCoefficientOrder.coefficient_order_of_all_section_values
#print axioms KltDP.Geometry.OriginalDifferentialCoefficientOrder.coefficient_order_of_all_section_values
