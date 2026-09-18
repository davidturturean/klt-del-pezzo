import KltDP.Geometry.CartierModuleIsoChartUnit
import KltDP.Geometry.CartierPrincipalShift
import KltDP.Geometry.RationalModuleOpenRestriction

/-!
# The literal rational inclusion square of a Cartier-module isomorphism

The unit computed from a common original equation chart acts on every
original section. Thus the original isomorphism, followed by the original
fractional-module inclusion, is exactly multiplication by that unit.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierModuleIsoMultiplier

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] (D E : CartierDivisor X)
    (e : cartierDivisorModule X D ≅ cartierDivisorModule X E)
    (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D)
    (hg : cartierEquationClassHom X U (Additive.ofMul g) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op E)

/-- The actual chart unit is the multiplier on every original section. -/
theorem value_eq_chartMultiplierUnit (V : X.Opens) [Nonempty V]
    (s : (cartierDivisorModule X D).val.obj (op V)) :
    value X D (e.hom ≫ cartierDivisorModuleInclusion X E) V s =
      (chartMultiplierUnit X D E e U f g hf hg : X.functionField) *
        rationalFunctionModuleSectionsEquiv X V s.val := by
  exact (value_eq_multiplier X D (e.hom ≫ cartierDivisorModuleInclusion X E)
    U f hf V s).trans
    (congrArg (fun q : X.functionField =>
      q * rationalFunctionModuleSectionsEquiv X V s.val)
      (multiplier_eq_chartMultiplierUnit X D E e U f g hf hg))

/-- The equality concerns the given isomorphism and both original inclusions. -/
theorem hom_inclusion_eq_chartMultiplierUnit :
    e.hom ≫ cartierDivisorModuleInclusion X E =
      cartierDivisorModuleInclusion X D ≫
        (rationalFunctionMulIso X (chartMultiplierUnit X D E e U f g hf hg)).hom := by
  classical
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  by_cases hV : Nonempty V.unop
  · letI := hV
    apply (rationalFunctionModuleSectionsEquiv X V.unop).injective
    change value X D (e.hom ≫ cartierDivisorModuleInclusion X E) V.unop s =
      rationalFunctionModuleSectionsEquiv X V.unop
        ((rationalFunctionMulIso X
          (chartMultiplierUnit X D E e U f g hf hg)).hom.val.app V s.val)
    exact (value_eq_chartMultiplierUnit X D E e U f g hf hg V.unop s).trans
      (rationalFunctionMulIso_hom_app_field X
        (chartMultiplierUnit X D E e U f g hf hg) V.unop s.val).symm
  · letI := OpenImmersionRational.sectionRing_subsingleton_of_empty V.unop hV
    letI : Subsingleton ((rationalFunctionModule X).val.obj V) :=
      Module.subsingleton Γ(X, V.unop) _
    exact Subsingleton.elim _ _

/-- Two actual common equation charts give the same unit for the same map. -/
theorem chartMultiplierUnit_eq (V : X.Opens) [Nonempty V]
    (f' g' : X.functionFieldˣ)
    (hf' : cartierEquationClassHom X V (Additive.ofMul f') =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : V ≤ ⊤)).op D)
    (hg' : cartierEquationClassHom X V (Additive.ofMul g') =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : V ≤ ⊤)).op E) :
    chartMultiplierUnit X D E e U f g hf hg =
      chartMultiplierUnit X D E e V f' g' hf' hg' := by
  apply Units.ext
  apply mul_right_cancel₀ (Units.ne_zero (f'⁻¹))
  have h₁ := value_eq_chartMultiplierUnit X D E e U f g hf hg V
    ((cartierEquationSectionEquiv X D V f' hf') 1)
  have h₂ := value_eq_chartMultiplierUnit X D E e V f' g' hf' hg' V
    ((cartierEquationSectionEquiv X D V f' hf') 1)
  simpa only [cartierEquationSectionEquiv_apply_field, map_one, one_mul] using
    h₁.symm.trans h₂

end KltDP.Geometry.CartierModuleIsoMultiplier

#check @KltDP.Geometry.CartierModuleIsoMultiplier.hom_inclusion_eq_chartMultiplierUnit
#print axioms KltDP.Geometry.CartierModuleIsoMultiplier.hom_inclusion_eq_chartMultiplierUnit
#check @KltDP.Geometry.CartierModuleIsoMultiplier.chartMultiplierUnit_eq
#print axioms KltDP.Geometry.CartierModuleIsoMultiplier.chartMultiplierUnit_eq
