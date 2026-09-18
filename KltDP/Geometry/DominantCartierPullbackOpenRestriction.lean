import KltDP.Geometry.DominantCartierPullbackEquations
import KltDP.Geometry.CartierOpenRestrictionEquations

/-!
On an original open immersion the signed dominant Cartier pullback equals
the existing Cartier restriction homomorphism. The two actual generic
stalk field maps agree; their transported equations consequently agree
on the inverse images of the original divisor's covering equation charts.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.DominantCartierPullback

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

local instance openGenericPointPreserving (π : X ⟶ Y) [IsOpenImmersion π] :
    GenericPointPreserving π := ⟨genericPoint_eq_of_isOpenImmersion π⟩

variable (π : X ⟶ Y) [IsOpenImmersion π]

/-- The original dominant field map is the forward generic-stalk map
of the existing open-immersion field isomorphism. -/
theorem functionFieldMap_eq_functionFieldIso :
    functionFieldMap π = (OpenImmersionRational.functionFieldIso π).hom := rfl

/-- The signed pullback agrees with the existing actual Cartier
restriction on every open immersion of integral schemes. -/
theorem pullbackHom_eq_cartierRestrictionHom :
    pullbackHom π = OpenImmersionRational.cartierRestrictionHom π := by
  apply AddMonoidHom.ext
  intro D
  refine cartierDivisor_eq_of_restrict_eq X
    (fun c : CartierEquationChart Y D => π ⁻¹ᵁ c.openSet)
    (preimageEquationCharts_cover π D) _ _ (fun c => ?_)
  have hp := pullbackHom_globalEquation_preimage π D c.openSet c.equation c.represents
  have ho := OpenImmersionRational.cartierRestriction_globalEquation_preimage
    π D c.openSet c.equation c.represents
  rw [functionFieldMap_eq_functionFieldIso] at hp
  exact hp.symm.trans ho

end KltDP.Geometry.DominantCartierPullback
