import KltDP.Geometry.StalkDivisorOrderPullback
import KltDP.Geometry.CartierOpenRestrictionEquations
import KltDP.Geometry.CartierWeilMap

/-!
# Actual local Cartier orders under an open immersion

The original open-immersion function-field isomorphism and the existing
function-field map have the same generic-stalk formula. The proved stalk
order compatibility therefore applies to the actual transported equations.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.OpenImmersionRational

attribute [local instance] integralSchemeStalk_isDomain

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f]

/-- The two existing field-map interfaces retain the same actual stalk map. -/
theorem functionFieldMap_eq_functionFieldIso_hom [GenericPointPreserving f] :
    functionFieldMap f = (functionFieldIso f).hom := rfl

/-- A corresponding original open-immersion stalk is a DVR whenever the
target stalk is a DVR; the equivalence is the original stalk map. -/
theorem stalk_isDiscreteValuationRing_of_isOpenImmersion (y : Y) (x : X)
    (hxy : f.base y = x) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    IsDiscreteValuationRing (Y.presheaf.stalk y) := by
  subst x
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv

/-- Original rational-function orders agree along the original field
isomorphism of an open immersion at corresponding DVR points. -/
theorem stalkDivisorOrder_functionFieldIso (y : Y) (x : X) (hxy : f.base y = x)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (g : X.functionFieldˣ) :
    stalkDivisorOrder Y y (Units.map (functionFieldIso f).hom.hom.toMonoidHom g) =
      stalkDivisorOrder X x g := by
  letI : GenericPointPreserving f := ⟨genericPoint_eq_of_isOpenImmersion f⟩
  exact stalkDivisorOrder_map_of_stalkMap_isIso f y x hxy g

/-- Restriction of an arbitrary actual Cartier divisor preserves its
local order at corresponding original DVR points. -/
theorem cartierOrderAt_cartierRestrictionHom (D : CartierDivisor X)
    (y : Y) (x : X) (hxy : f.base y = x)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    cartierOrderAt Y (cartierRestrictionHom f D) y = cartierOrderAt X D x := by
  obtain ⟨g, V, hxV, hg⟩ := exists_cartierOrderEquation X D x
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hyV : y ∈ f ⁻¹ᵁ V := by
    change f.base y ∈ V
    rwa [hxy]
  letI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨y, hyV⟩⟩
  calc
    cartierOrderAt Y (cartierRestrictionHom f D) y =
        stalkDivisorOrder Y y
          (Units.map (functionFieldIso f).hom.hom.toMonoidHom g) :=
      cartierOrderAt_eq_of_equation Y (cartierRestrictionHom f D) y (f ⁻¹ᵁ V) hyV _
        (cartierRestriction_globalEquation_preimage f D V g hg)
    _ = stalkDivisorOrder X x g := stalkDivisorOrder_functionFieldIso f y x hxy g
    _ = cartierOrderAt X D x :=
      (cartierOrderAt_eq_of_equation X D x V hxV g hg).symm

end KltDP.Geometry.OpenImmersionRational
