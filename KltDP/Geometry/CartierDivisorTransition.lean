import KltDP.Geometry.CartierDivisorTrivialization

/-!
# Actual overlap coordinates for O(D)

With coordinates `a ↦ a/f`, changing from equation `f` to equation `g`
multiplies the regular coefficient by `g/f`. This is the inverse of the
previously constructed transition unit whose image is `f/g`. The equality
below is an equality of actual sections of the constructed module O(D),
proved through its injective inclusion into rational functions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- The overlap change of regular coefficient has the inverse ratio
required by `O(D) = f⁻¹ O`: the same section has `g`-coordinate
`a * (f/g)⁻¹` when its `f`-coordinate is `a`. -/
theorem cartierEquationSectionEquiv_changeEquation (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D)
    (hg : cartierEquationClassHom X U (Additive.ofMul g) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D)
    (a : Γ(X, U)) :
    cartierEquationSectionEquiv X D U g hg
        (a * (↑((cartierTransitionUnit X U f g (hf.trans hg.symm))⁻¹) : Γ(X, U))) =
      cartierEquationSectionEquiv X D U f hf a := by
  have hu : Units.map (X.germToFunctionField U).hom.toMonoidHom
      ((cartierTransitionUnit X U f g (hf.trans hg.symm))⁻¹) * g⁻¹ = f⁻¹ := by
    rw [map_inv, map_cartierTransitionUnit]
    calc
      (f / g)⁻¹ * g⁻¹ = (g * g⁻¹) * f⁻¹ := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, mul_comm, mul_left_comm]
      _ = f⁻¹ := by rw [mul_inv_cancel, one_mul]
  apply Subtype.ext
  apply (rationalFunctionModuleSectionsEquiv X U).injective
  rw [cartierEquationSectionEquiv_apply_field, cartierEquationSectionEquiv_apply_field, map_mul]
  change X.germToFunctionField U a *
      (↑(Units.map (X.germToFunctionField U).hom.toMonoidHom
        ((cartierTransitionUnit X U f g (hf.trans hg.symm))⁻¹)) : X.functionField) *
        (↑(g⁻¹) : X.functionField) =
    X.germToFunctionField U a * (↑(f⁻¹) : X.functionField)
  rw [mul_assoc, ← Units.val_mul, hu]

end KltDP.Geometry
