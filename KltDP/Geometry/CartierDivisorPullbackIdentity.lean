import KltDP.Geometry.CartierDivisorPullbackComp

/-!
# The identity law for the pullback of Cartier divisors

The accepted tree carries every law of the pullback of a Cartier divisor with regular equations
along a generic-point-preserving morphism of integral schemes **except** the identity law:
composition (`pullbackDivisor_comp`), additivity (`pullbackDivisor_add`), the zero divisor
(`pullbackDivisor_zero`), natural multiples (`pullbackDivisor_nsmul`) and the additive homomorphism
`pullbackDivisorHom` are all accepted, while `pullbackDivisor (𝟙 X) D hD = D` is declared nowhere.
This module supplies it:

* `functionFieldMap_id` — the function-field map of `𝟙 X` is the identity, by germ extensionality
  (the pattern of the accepted `functionFieldMap_comp`);
* `pulledEquation_id` — the pulled-back equation of a regular chart along `𝟙 X` is the chart's own
  equation;
* **`pullbackDivisor_id`** — the identity law, proved by comparing both sides on `D`'s own regular
  charts, where the left side is the class of the pulled-back equation
  (`pullbackDivisor_restrict_le`) and the right side is `c.chart.represents`;
* `pullbackDivisor_eq_of_hom_eq_id` — the form consumers actually meet: a morphism *equal to* the
  identity (for instance the degenerate step `between A (Nat.zero_le 0)` of a blowup tower, which
  `between_refl` identifies with `𝟙`) pulls every divisor with regular equations back to itself;
* `pullbackDivisorHom_id` — the same law for the additive homomorphism.

With the accepted `pullbackDivisor_comp` this completes the functor laws.

Consumers have worked around the absence chart by chart: the accepted
`KltDP/Examples/FrobeniusTowerCartierIdentity.zero_case` reduces the stage-`0` case of the fibre
identity to `between_refl` together with `appLE_congr_hom`, `Scheme.id_app` and a plain restriction
of the chart generator, and the lane-F graph analogue repeats the manoeuvre, recording in its own
docstring that it proceeds this way "rather than through a generic `pullbackDivisor_id`, which the
accepted tree does not have".

Nothing is admitted, no literature literal is used, and the entire import closure is accepted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierDivisorPullbackIdentity

open KltDP.Geometry KltDP.Geometry.CartierDivisorPullbackAdd
open KltDP.Geometry.CartierDivisorPullbackComp

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} [IsIntegral X]

/-- **The function-field map of the identity is the identity.** Germ extensionality: on the germ of
a section `s` over a nonempty open `U`, the map sends `germ U s` to `germ ((𝟙 X) ⁻¹ᵁ U) ((𝟙 X).app U s)`
(the accepted `functionFieldMap_germ`), and both the preimage and the section map of `𝟙 X` are the
identity. -/
theorem functionFieldMap_id : functionFieldMap (𝟙 X) = 𝟙 X.functionField := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  haveI : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  ext s
  simp only [CommRingCat.comp_apply, CommRingCat.id_apply]
  change functionFieldMap (𝟙 X) (X.germToFunctionField U s) = X.germToFunctionField U s
  rw [functionFieldMap_germ]
  rfl

/-- The pulled-back equation of a regular chart along the identity is the chart's own equation. -/
theorem pulledEquation_id (D : CartierDivisor X) (c : RegularCartierEquationChart X D) :
    pulledEquation (𝟙 X) D c = c.chart.equation := by
  apply Units.ext
  rw [pulledEquation_val, functionFieldMap_id]
  exact CommRingCat.id_apply _ _

/-- **The identity law for the pullback of Cartier divisors**: `(𝟙 X)^*D = D`.

Both sides are compared on the cover of `X` by the opens of the regular charts of `D` itself. On
such a chart the pullback restricts to the class of the pulled-back equation
(`pullbackDivisor_restrict_le`, applicable because `c.chart.openSet ≤ (𝟙 X) ⁻¹ᵁ c.chart.openSet`
holds by `le_rfl`), which is the chart's equation by `pulledEquation_id`; and that class is the
restriction of `D` by the chart's own `represents` field. -/
theorem pullbackDivisor_id (D : CartierDivisor X) (hD : HasRegularCartierEquations X D) :
    pullbackDivisor (𝟙 X) D hD = D := by
  have hcover : (⊤ : X.Opens) ≤
      iSup (fun c : RegularCartierEquationChart X D => c.chart.openSet) := by
    intro x _
    obtain ⟨c, hc⟩ := hD x
    exact Opens.mem_iSup.mpr ⟨c, hc⟩
  refine cartierDivisor_eq_of_restrict_eq X
    (fun c : RegularCartierEquationChart X D => c.chart.openSet) hcover _ D (fun c => ?_)
  rw [pullbackDivisor_restrict_le (𝟙 X) D hD c (W := c.chart.openSet) le_rfl, pulledEquation_id]
  exact c.chart.represents

/-- **The form consumers meet**: a morphism equal to the identity pulls back every Cartier divisor
with regular equations to itself. This is the shape of the degenerate step of a blowup tower, where
`between A (Nat.zero_le 0) = 𝟙` holds only propositionally (`between_refl`). -/
theorem pullbackDivisor_eq_of_hom_eq_id (π : X ⟶ X) [GenericPointPreserving π] (hπ : π = 𝟙 X)
    (D : CartierDivisor X) (hD : HasRegularCartierEquations X D) :
    pullbackDivisor π D hD = D := by
  rw [pullbackDivisor_congr_hom hπ D hD, pullbackDivisor_id]

/-- The identity law for the additive pullback homomorphism on the divisors with regular
equations. -/
theorem pullbackDivisorHom_id (D : regularDivisors X) :
    pullbackDivisorHom (𝟙 X) D = (D : CartierDivisor X) := by
  rw [pullbackDivisorHom_apply, pullbackDivisor_id]

end KltDP.Geometry.CartierDivisorPullbackIdentity
