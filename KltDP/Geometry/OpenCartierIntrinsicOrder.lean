import KltDP.Geometry.CartierOrderOpenRestriction
import KltDP.Geometry.OpenCartierWeil

/-!
# The intrinsic local order of the existing open Cartier extension

The existing coefficient, defined by transport to the surface function
field, is the intrinsic Cartier order on the original open subscheme.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.OpenCartierWeil

open OpenImmersionRational
attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}
    (U : X.toScheme.Opens) [Nonempty U.toScheme]

local instance : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- At an original prime generic point in the open, the actual extended
coefficient equals the intrinsic Cartier order on that same open. -/
theorem restrictedCoefficient_eq_cartierOrderAt (E : CartierDivisor U.toScheme)
    (C : X.PrimeCurve) (hC : C.genericPoint ∈ U)
    [IsDiscreteValuationRing
      (U.toScheme.presheaf.stalk (⟨C.genericPoint, hC⟩ : U.toScheme))] :
    restrictedCoefficient U E C =
      cartierOrderAt U.toScheme E (⟨C.genericPoint, hC⟩ : U.toScheme) := by
  let y : U.toScheme := ⟨C.genericPoint, hC⟩
  letI : IsDiscreteValuationRing (X.toScheme.presheaf.stalk C.genericPoint) :=
    C.genericPoint_isDiscreteValuationRing
  rw [restrictedCoefficient_of_mem U E C hC]
  change stalkDivisorOrder X.toScheme C.genericPoint
      (transportUnit U (cartierOrderEquation U.toScheme E y)) =
    stalkDivisorOrder U.toScheme y (cartierOrderEquation U.toScheme E y)
  have h := stalkDivisorOrder_functionFieldIso U.ι y C.genericPoint rfl
    (transportUnit U (cartierOrderEquation U.toScheme E y))
  rw [transportUnit_hom] at h
  exact h.symm

end KltDP.Geometry.OpenCartierWeil
