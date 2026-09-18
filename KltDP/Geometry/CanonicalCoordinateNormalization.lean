import KltDP.Geometry.CanonicalNormalizationOrder
import KltDP.Geometry.CartierModuleIsoMultiplier
import KltDP.Geometry.CartierCoordinateMultiplierComparison

/-!
# The actual coordinate scalar has zero order on every original model

Two identifications with the same actual module give their own rational
multiplier through the original fractional inclusions. If the two Cartier
divisors have the same exact Weil extension from a big open, this particular
multiplier has zero order on every original integral model at every DVR
stalk. No independently chosen Picard-class scalar is substituted for it.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalNormalization

attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme]

local instance : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- The original scalar of the given identifications is invisible to all
original model orders once their target Weil normalization agrees. -/
theorem exists_coordinate_scalar_order_zero_on_models
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (D E : CartierDivisor U.toScheme) (M : U.toScheme.Modules)
    (eD : cartierDivisorModule U.toScheme D ≅ M)
    (eE : cartierDivisorModule U.toScheme E ≅ M)
    (hext : OpenCartierWeil.restrictedWeilHom U D =
      OpenCartierWeil.restrictedWeilHom U E) :
    ∃ q : U.toScheme.functionFieldˣ,
      D - E = principalCartierDivisorHom U.toScheme (Additive.ofMul q) ∧
      CartierRationalCoordinate.coordinate U.toScheme E M eE =
        CartierRationalCoordinate.coordinate U.toScheme D M eD ≫
          (rationalFunctionMulIso U.toScheme q).hom ∧
      ∀ (V : Scheme.{u}) [IsIntegral V] (v : V ⟶ X.toScheme)
        [GenericPointPreserving v] (x : V)
        [IsDiscreteValuationRing (V.presheaf.stalk x)],
        stalkDivisorOrder V x
          (Units.map (functionFieldMap v).hom.toMonoidHom
            (OpenCartierWeil.transportUnit U q)) = 0 := by
  obtain ⟨q, hq, hsquare⟩ :=
    CartierModuleIsoMultiplier.exists_multiplier U.toScheme D E (eD ≪≫ eE.symm)
  refine ⟨q, hq,
    CartierRationalCoordinate.coordinate_eq_mul_of_inclusion
      U.toScheme D E M eD eE q hsquare, ?_⟩
  intro V hV v hv x hx
  exact principal_difference_order_zero X U hU D E q hq hext v x

end KltDP.Geometry.CanonicalNormalization

#check @KltDP.Geometry.CanonicalNormalization.exists_coordinate_scalar_order_zero_on_models
#print axioms KltDP.Geometry.CanonicalNormalization.exists_coordinate_scalar_order_zero_on_models
