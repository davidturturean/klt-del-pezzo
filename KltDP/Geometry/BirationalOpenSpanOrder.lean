import KltDP.Geometry.StalkDivisorOrderPullback
import KltDP.Geometry.CartierDivisorPullbackComp
import KltDP.Geometry.ImmersionBirational

/-!
# Original function-field orders through a common open neighborhood

The original model V and its completion Z share the original open U.
A source point maps to that same open point of Z by an isomorphic stalk
map. The two original triangles over X identify orders of every original
unit of K(X), using the existing order-transport and function-field
composition theorems. No global map from the source to V is required.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.BirationalOpenSpanOrder

attribute [local instance] integralSchemeStalk_isDomain

private theorem mapUnit_comp
    {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B] [IsIntegral C]
    (f : A ⟶ B) (g : B ⟶ C) [GenericPointPreserving f] [GenericPointPreserving g]
    (a : C.functionFieldˣ) :
    Units.map (functionFieldMap f).hom.toMonoidHom
        (Units.map (functionFieldMap g).hom.toMonoidHom a) =
      Units.map (functionFieldMap (f ≫ g)).hom.toMonoidHom a := by
  apply Units.ext
  change functionFieldMap f (functionFieldMap g a) = functionFieldMap (f ≫ g) a
  rw [CartierDivisorPullbackComp.functionFieldMap_comp]
  rfl

private theorem mapUnit_congr
    {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (f g : A ⟶ B) [GenericPointPreserving f] [GenericPointPreserving g]
    (h : f = g) (a : B.functionFieldˣ) :
    Units.map (functionFieldMap f).hom.toMonoidHom a =
      Units.map (functionFieldMap g).hom.toMonoidHom a := by
  subst g
  rfl

/-- The original units of the base function field have the same orders
at corresponding DVR points, through the original common-open diagram. -/
theorem order_eq_through_original_open
    {U V Z S X : Scheme.{u}}
    [IsIntegral U] [IsIntegral V] [IsIntegral Z] [IsIntegral S] [IsIntegral X]
    (j : U ⟶ V) (i : U ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion i]
    (v : V ⟶ X) (p : Z ⟶ X) (q : S ⟶ Z)
    [GenericPointPreserving v] [GenericPointPreserving p] [GenericPointPreserving q]
    (hcomm : j ≫ v = i ≫ p) (s : S) (y : U) (hsy : q.base s = i.base y)
    [IsDiscreteValuationRing (V.presheaf.stalk (j.base y))]
    [IsDiscreteValuationRing (S.presheaf.stalk s)] [IsIso (q.stalkMap s)]
    (a : X.functionFieldˣ) :
    stalkDivisorOrder S s (Units.map (functionFieldMap (q ≫ p)).hom.toMonoidHom a) =
      stalkDivisorOrder V (j.base y) (Units.map (functionFieldMap v).hom.toMonoidHom a) := by
  letI : GenericPointPreserving j := ⟨genericPoint_eq_of_isOpenImmersion j⟩
  letI : GenericPointPreserving i := ⟨genericPoint_eq_of_isOpenImmersion i⟩
  letI : IsDiscreteValuationRing (U.presheaf.stalk y) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  letI : IsDiscreteValuationRing (Z.presheaf.stalk (i.base y)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv.symm
  have hunit :
      Units.map (functionFieldMap j).hom.toMonoidHom
          (Units.map (functionFieldMap v).hom.toMonoidHom a) =
        Units.map (functionFieldMap i).hom.toMonoidHom
          (Units.map (functionFieldMap p).hom.toMonoidHom a) := by
    rw [mapUnit_comp, mapUnit_comp]
    exact mapUnit_congr (j ≫ v) (i ≫ p) hcomm a
  rw [← mapUnit_comp q p a]
  calc
    stalkDivisorOrder S s (Units.map (functionFieldMap q).hom.toMonoidHom
        (Units.map (functionFieldMap p).hom.toMonoidHom a)) =
        stalkDivisorOrder Z (i.base y) (Units.map (functionFieldMap p).hom.toMonoidHom a) :=
      stalkDivisorOrder_map_of_stalkMap_isIso q s (i.base y) hsy _
    _ = stalkDivisorOrder U y (Units.map (functionFieldMap i).hom.toMonoidHom
        (Units.map (functionFieldMap p).hom.toMonoidHom a)) :=
      (stalkDivisorOrder_map_of_stalkMap_isIso i y (i.base y) rfl _).symm
    _ = stalkDivisorOrder U y (Units.map (functionFieldMap j).hom.toMonoidHom
        (Units.map (functionFieldMap v).hom.toMonoidHom a)) :=
      congrArg (stalkDivisorOrder U y) hunit.symm
    _ = stalkDivisorOrder V (j.base y) (Units.map (functionFieldMap v).hom.toMonoidHom a) :=
      stalkDivisorOrder_map_of_stalkMap_isIso j y (j.base y) rfl _

end KltDP.Geometry.BirationalOpenSpanOrder

#check @KltDP.Geometry.BirationalOpenSpanOrder.order_eq_through_original_open
#print axioms KltDP.Geometry.BirationalOpenSpanOrder.order_eq_through_original_open
