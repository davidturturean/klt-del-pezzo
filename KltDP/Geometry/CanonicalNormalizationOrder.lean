import KltDP.Geometry.OpenCartierWeilPrincipal
import KltDP.Geometry.NormalCartierWeilInjective
import KltDP.Geometry.DominantCartierPullback
import KltDP.Geometry.SmoothCanonicalCartierExterior

/-!
# Fixed canonical normalization has zero order on every original model

A principal difference whose exact Weil extension is zero is already zero
as a Cartier divisor on the original normal target. Its signed pullback
to any original integral model is zero, so the original transported rational
function has order zero at every DVR stalk. No properness or projectivity
of that model is required.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.CanonicalNormalization

attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- An actual zero principal Weil divisor stays order zero under every
original dominant Cartier pullback, including nonproper models. -/
theorem order_eq_zero_of_principalDivisor_eq_zero
    (X : NormalProjectiveSurface k) {V : Scheme.{u}} [IsIntegral V]
    (v : V ⟶ X.toScheme) [GenericPointPreserving v]
    (q : X.toScheme.functionFieldˣ) (hq : X.principalDivisor q = 0)
    (x : V) [IsDiscreteValuationRing (V.presheaf.stalk x)] :
    stalkDivisorOrder V x (Units.map (functionFieldMap v).hom.toMonoidHom q) = 0 := by
  have hX : principalCartierDivisorHom X.toScheme (Additive.ofMul q) = 0 :=
    (X.cartierToWeilHom_eq_zero_iff _).mp ((X.cartierToWeilHom_principal q).trans hq)
  have hV : principalCartierDivisorHom V
      (Additive.ofMul (Units.map (functionFieldMap v).hom.toMonoidHom q)) = 0 := by
    rw [← DominantCartierPullback.pullbackHom_principal, hX, map_zero]
  rw [← cartierOrderAt_principal, hV, cartierOrderAt_zero]

variable (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme]
local instance : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- Every principal difference of canonical representatives with the same
exact target Weil divisor has zero original order on every integral model. -/
theorem principal_difference_order_zero
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (D E : CartierDivisor U.toScheme) (f : U.toScheme.functionFieldˣ)
    (hDE : D - E = principalCartierDivisorHom U.toScheme (Additive.ofMul f))
    (hext : OpenCartierWeil.restrictedWeilHom U D = OpenCartierWeil.restrictedWeilHom U E)
    {V : Scheme.{u}} [IsIntegral V] (v : V ⟶ X.toScheme) [GenericPointPreserving v]
    (x : V) [IsDiscreteValuationRing (V.presheaf.stalk x)] :
    stalkDivisorOrder V x
      (Units.map (functionFieldMap v).hom.toMonoidHom (OpenCartierWeil.transportUnit U f)) = 0 := by
  apply order_eq_zero_of_principalDivisor_eq_zero X v _ _ x
  have h := OpenCartierWeil.restrictedWeilHom_sub_of_principal U hU D E f hDE
  rw [hext, sub_self] at h
  exact h.symm

/-- The actual top-differential isomorphisms produce the principal
difference; exact target normalization makes all its model orders zero. -/
theorem exists_principal_difference_order_zero_on_models
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (D E : CartierDivisor U.toScheme)
    (eD : cartierDivisorModule U.toScheme D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    (eE : cartierDivisorModule U.toScheme E ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    (hext : OpenCartierWeil.restrictedWeilHom U D = OpenCartierWeil.restrictedWeilHom U E) :
    ∃ f : U.toScheme.functionFieldˣ,
      D - E = principalCartierDivisorHom U.toScheme (Additive.ofMul f) ∧
      ∀ (V : Scheme.{u}) [IsIntegral V] (v : V ⟶ X.toScheme) [GenericPointPreserving v]
        (x : V) [IsDiscreteValuationRing (V.presheaf.stalk x)],
        stalkDivisorOrder V x
          (Units.map (functionFieldMap v).hom.toMonoidHom (OpenCartierWeil.transportUnit U f)) = 0 := by
  obtain ⟨f, hf⟩ := SmoothCanonicalCartierExterior.exterior_choices_principal
    (U.ι ≫ X.structureMorphism) 2 D E eD eE
  refine ⟨f, hf, ?_⟩
  intro V hV v hv x hx
  exact principal_difference_order_zero X U hU D E f hf hext v x

end KltDP.Geometry.CanonicalNormalization

#check @KltDP.Geometry.CanonicalNormalization.exists_principal_difference_order_zero_on_models
#print axioms KltDP.Geometry.CanonicalNormalization.order_eq_zero_of_principalDivisor_eq_zero
#print axioms KltDP.Geometry.CanonicalNormalization.exists_principal_difference_order_zero_on_models
