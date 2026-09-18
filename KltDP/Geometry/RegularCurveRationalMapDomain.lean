import KltDP.Geometry.RegularCurveValuationStalk
import KltDP.Geometry.ProperFunctionFieldStalkLift
import KltDP.Geometry.PartialMapStalkGenerization

/-! Properness makes the domain of the original rational map all of an
integral regular curve. The local representatives come from the actual
valuation stalk lifts and agree on the original function field. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.RegularCurveRationalMapDomain

attribute [local instance] integralSchemeStalk_isDomain

theorem domain_eq_top {X Y B : Scheme.{u}} [IsIntegral X]
    (hregular : ∀ x : X, RegularPoint X x)
    (hdim : topologicalKrullDim X ≤ 1)
    (sX : X ⟶ B) (sY : Y ⟶ B) [IsProper sY]
    (t : Spec X.functionField ⟶ Y)
    (ht : t ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX) :
    (Scheme.RationalMap.ofFunctionField sX sY t ht).domain = ⊤ := by
  apply top_le_iff.mp
  intro x _
  letI : ValuationRing (X.presheaf.stalk x) :=
    RegularCurveValuationStalk.valuationRing X hregular hdim x
  obtain ⟨φ, hφ, hgeneric⟩ :=
    ProperFunctionFieldStalkLift.exists_lift sX sY t ht x
  let p := Scheme.PartialMap.ofFromSpecStalk sX sY φ hφ
  have hx : x ∈ p.domain :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY φ hφ
  refine Scheme.RationalMap.mem_domain.mpr ⟨p, hx, ?_⟩
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_ofFunctionField]
  change p.fromFunctionField = t
  rw [← PartialMapStalkGenerization.fromFunctionField p hx]
  exact (congrArg (fun q => Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ q)
    (Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY φ hφ)).trans hgeneric

end KltDP.Geometry.RegularCurveRationalMapDomain
