import KltDP.Geometry.OriginalDifferentialCoefficientOrderAllSections
import KltDP.Geometry.RationalDifferentialExistsSquareValue

/-!
# Original coefficient order directly from an existing open square

Evaluate the original square and compute the coefficient order before
specializing the schemes or their Cartier identifications. The concrete
canonical caller supplies the already proved original square directly;
no concrete all-section field-value conversion is needed there.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.OriginalDifferentialCoefficientOrder

open CartierRationalCoordinate NormalizedDifferentialCoefficientOrder OpenImmersionRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] integralSchemeStalk_isDomain

local instance squareOrderOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- The existing original differential-coordinate square determines the
literal section coefficient and signed Cartier order on its original charts. -/
theorem coefficient_order_of_exists_open_square
    {k : Type u} [CommRing k] {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (sA : A ⟶ Spec (CommRingCat.of k)) (sB : B ⟶ Spec (CommRingCat.of k))
    (q : B ⟶ A) [GenericPointPreserving q] (hq : q ≫ sA = sB)
    (DA : CartierDivisor A) (DB : CartierDivisor B)
    (eA : cartierDivisorModule A DA ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2)
    (eB : cartierDivisorModule B DB ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2)
    (hsquare : ∃ (Z : B.Opens) (hne : Nonempty Z.toScheme),
      letI : Nonempty Z.toScheme := hne
      letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
      ∃ ht : IsOpenImmersion (Z.ι ≫ q),
        letI : IsOpenImmersion (Z.ι ≫ q) := ht
        (schemeModulePullback Z.ι).map
            (SchemeKaehlerExteriorPullbackTransport.map sA q sB hq 2 ≫
              coordinate B DB
                (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2) eB) ≫
            (rationalModulePullbackIso Z.ι).hom =
          (schemeModulePullbackCompIso Z.ι q).hom.app
              (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) ≫
            (schemeModulePullback (Z.ι ≫ q)).map
              (coordinate A DA
                (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eA) ≫
              (rationalModulePullbackIso (Z.ι ≫ q)).hom)
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
  exact coefficient_order_of_all_section_values sA sB q hq DA DB eA eB
    (RationalDifferentialSquareValue.field_value_of_exists_open_square_comp q
      (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2)
      (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2)
      (SchemeKaehlerExteriorPullbackTransport.map sA q sB hq 2)
      (coordinate B DB (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2) eB)
      (coordinate A DA (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eA)
      hsquare) cS cT hST y hy

end KltDP.Geometry.OriginalDifferentialCoefficientOrder

#check @KltDP.Geometry.OriginalDifferentialCoefficientOrder.coefficient_order_of_exists_open_square
#print axioms KltDP.Geometry.OriginalDifferentialCoefficientOrder.coefficient_order_of_exists_open_square
