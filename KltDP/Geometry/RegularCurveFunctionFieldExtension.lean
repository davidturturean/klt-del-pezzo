import KltDP.Geometry.RegularCurveRationalMapDomain
import KltDP.Geometry.RationalMapGlobalOfDomain

/-! A map from the original function-field spectrum of an integral
regular curve to a proper scheme extends uniquely over the original
separated base. No global morphism or birationality is assumed. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.RegularCurveFunctionFieldExtension

theorem exists_extension {X Y B : Scheme.{u}} [IsIntegral X] [B.IsSeparated]
    (hregular : ∀ x : X, RegularPoint X x)
    (hdim : topologicalKrullDim X ≤ 1)
    (sX : X ⟶ B) (sY : Y ⟶ B) [IsProper sY]
    (t : Spec X.functionField ⟶ Y)
    (ht : t ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX) :
    ∃ g : X ⟶ Y, g ≫ sY = sX ∧
      X.fromSpecStalk (genericPoint X) ≫ g = t := by
  letI : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from sY]
    infer_instance⟩
  let r := Scheme.RationalMap.ofFunctionField sX sY t ht
  have hr : r.domain = ⊤ :=
    RegularCurveRationalMapDomain.domain_eq_top hregular hdim sX sY t ht
  let g := RationalMapGlobalOfDomain.hom r hr
  have hg : X.fromSpecStalk (genericPoint X) ≫ g = t :=
    (RationalMapGlobalOfDomain.fromFunctionField r hr).trans
      (Scheme.RationalMap.fromFunctionField_ofFunctionField sX sY t ht)
  letI : IsDominant (X.fromSpecStalk (genericPoint X)) :=
    DominantOpenSection.fromSpecStalk_genericPoint_isDominant X
  refine ⟨g, ?_, hg⟩
  apply ext_of_isDominant (X.fromSpecStalk (genericPoint X))
  rw [← Category.assoc, hg, ht]

theorem unique {X Y B : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ B) (sY : Y ⟶ B) [IsSeparated sY]
    {g h : X ⟶ Y} (hg : g ≫ sY = sX) (hh : h ≫ sY = sX)
    (heq : X.fromSpecStalk (genericPoint X) ≫ g =
      X.fromSpecStalk (genericPoint X) ≫ h) : g = h := by
  letI : IsDominant (X.fromSpecStalk (genericPoint X)) :=
    DominantOpenSection.fromSpecStalk_genericPoint_isDominant X
  exact ext_of_isDominant_of_isSeparated sY (hg.trans hh.symm)
    (X.fromSpecStalk (genericPoint X)) heq

end KltDP.Geometry.RegularCurveFunctionFieldExtension
