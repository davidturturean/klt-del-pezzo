import KltDP.Geometry.CartierModuleHomRationalMultiplier

/-!
# The actual unit coordinate of a Cartier-module isomorphism

On a common original equation chart, the given module isomorphism induces
a linear automorphism of the original section ring. Its image of 1 is a
genuine regular unit. That unit and the two original equations determine
the nonzero rational multiplier of the given isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierModuleIsoMultiplier

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- A linear automorphism of a ring has a unit as its value at 1. -/
theorem linearEquiv_apply_one_isUnit {R : Type*} [CommRing R] (e : R ≃ₗ[R] R) :
    IsUnit (e 1) := by
  obtain ⟨r, hr⟩ := e.surjective 1
  have hmul : e r = r * e 1 := by
    simpa only [smul_eq_mul, mul_one] using e.map_smul r (1 : R)
  exact isUnit_of_mul_eq_one_right r (e 1) (hmul.symm.trans hr)

variable (X : Scheme.{u}) [IsIntegral X] (D E : CartierDivisor X)
    (e : cartierDivisorModule X D ≅ cartierDivisorModule X E)
    (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D)
    (hg : cartierEquationClassHom X U (Additive.ofMul g) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op E)

/-- Evaluation retains the actual given isomorphism of Cartier modules. -/
def sectionEquiv :
    (cartierDivisorModule X D).val.obj (op U) ≃ₗ[Γ(X, U)]
      (cartierDivisorModule X E).val.obj (op U) :=
  ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso e).toLinearEquiv

/-- Original equation coordinates on either side of the original isomorphism. -/
def chartCoordinateEquiv : Γ(X, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  (cartierEquationSectionEquiv X D U f hf).trans
    ((sectionEquiv X D E e U).trans (cartierEquationSectionEquiv X E U g hg).symm)

/-- The actual coordinate of the image of the original 1/f frame is a unit. -/
def chartCoordinateUnit : Γ(X, U)ˣ :=
  (linearEquiv_apply_one_isUnit (chartCoordinateEquiv X D E e U f g hf hg)).unit

theorem chartCoordinateUnit_spec :
    (chartCoordinateUnit X D E e U f g hf hg : Γ(X, U)) =
      chartCoordinateEquiv X D E e U f g hf hg 1 :=
  (linearEquiv_apply_one_isUnit (chartCoordinateEquiv X D E e U f g hf hg)).unit_spec

/-- The section equality uses the given isomorphism itself. -/
theorem equationFrame_map :
    (cartierEquationSectionEquiv X E U g hg)
        (chartCoordinateUnit X D E e U f g hf hg : Γ(X, U)) =
      e.hom.val.app (op U) ((cartierEquationSectionEquiv X D U f hf) 1) := by
  calc
    _ = (cartierEquationSectionEquiv X E U g hg)
        (chartCoordinateEquiv X D E e U f g hf hg 1) :=
      congrArg (cartierEquationSectionEquiv X E U g hg)
        (chartCoordinateUnit_spec X D E e U f g hf hg)
    _ = _ := (cartierEquationSectionEquiv X E U g hg).apply_symm_apply _

/-- Its original rational value is the original regular unit divided by g. -/
theorem value_equationFrame_eq_coordinateUnit :
    value X D (e.hom ≫ cartierDivisorModuleInclusion X E) U
        ((cartierEquationSectionEquiv X D U f hf) 1) =
      (X.germToFunctionField U).hom (chartCoordinateUnit X D E e U f g hf hg) *
        (↑(g⁻¹) : X.functionField) := by
  exact (congrArg (fun s : (cartierDivisorModule X E).val.obj (op U) =>
    rationalFunctionModuleSectionsEquiv X U s.val)
      (equationFrame_map X D E e U f g hf hg).symm).trans
    (cartierEquationSectionEquiv_apply_field X E U g hg
      (chartCoordinateUnit X D E e U f g hf hg))

/-- The nonzero multiplier comes from the given isomorphism and original
equations; its principal sign is D minus E. -/
def chartMultiplierUnit : X.functionFieldˣ :=
  Units.map (X.germToFunctionField U).hom.toMonoidHom
      (chartCoordinateUnit X D E e U f g hf hg) * g⁻¹ * f

theorem multiplier_eq_chartMultiplierUnit :
    multiplier X D (e.hom ≫ cartierDivisorModuleInclusion X E) U f hf =
      (chartMultiplierUnit X D E e U f g hf hg : X.functionField) := by
  rw [multiplier, value_equationFrame_eq_coordinateUnit X D E e U f g hf hg]
  rfl

end KltDP.Geometry.CartierModuleIsoMultiplier

#check @KltDP.Geometry.CartierModuleIsoMultiplier.multiplier_eq_chartMultiplierUnit
#print axioms KltDP.Geometry.CartierModuleIsoMultiplier.multiplier_eq_chartMultiplierUnit
