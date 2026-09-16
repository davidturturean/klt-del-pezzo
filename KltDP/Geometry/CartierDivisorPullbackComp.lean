import KltDP.Geometry.CartierDivisorPullbackAdd

/-!
# Pullback of Cartier divisors along a composite

The function-field map of a composite of generic-point-preserving morphisms of integral schemes is
the composite of the function-field maps (`functionFieldMap_comp`, by extensionality on germs), and
the accepted `pullbackDivisor` is functorial: `(f ≫ g)^*D = f^*(g^*D)` (`pullbackDivisor_comp`),
both sides being compared on the preimages of the regular charts of `D`.  Together with
`CartierDivisorPullbackAdd` this makes the pullback of Cartier divisors with regular equations an
additive functor in the morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierDivisorPullbackComp

open KltDP.Geometry KltDP.Geometry.CartierDivisorPullbackAdd

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
  (f : X ⟶ Y) (g : Y ⟶ Z) [GenericPointPreserving f] [GenericPointPreserving g]

/-- Composites of generic-point-preserving morphisms preserve the generic point. -/
instance genericPointPreserving_comp : GenericPointPreserving (f ≫ g) :=
  ⟨by rw [Scheme.comp_base_apply, GenericPointPreserving.base_genericPoint (π := f),
    GenericPointPreserving.base_genericPoint (π := g)]⟩

/-- The function-field map of a composite. -/
theorem functionFieldMap_comp :
    functionFieldMap (f ≫ g) = functionFieldMap g ≫ functionFieldMap f := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  haveI : Nonempty U := ⟨⟨genericPoint Z, hU⟩⟩
  ext s
  simp only [CommRingCat.comp_apply]
  change functionFieldMap (f ≫ g) (Z.germToFunctionField U s) =
    functionFieldMap f (functionFieldMap g (Z.germToFunctionField U s))
  rw [functionFieldMap_germ, functionFieldMap_germ, functionFieldMap_germ]
  rfl

/-- The pullback does not depend on the presentation of the morphism. -/
theorem pullbackDivisor_congr_hom {π π' : X ⟶ Y} [GenericPointPreserving π]
    [GenericPointPreserving π'] (h : π = π') (D : CartierDivisor Y)
    (hD : HasRegularCartierEquations Y D) :
    pullbackDivisor π D hD = pullbackDivisor π' D hD := by
  subst h
  rfl

/-- **Functoriality of the pullback of Cartier divisors**: `(f ≫ g)^*D = f^*(g^*D)`. -/
theorem pullbackDivisor_comp (D : CartierDivisor Z) (hD : HasRegularCartierEquations Z D) :
    pullbackDivisor (f ≫ g) D hD =
      pullbackDivisor f (pullbackDivisor g D hD) (pullbackDivisor_hasRegularEquations g D hD) := by
  apply cartierDivisor_eq_of_restrict_eq X
    (fun c : RegularCartierEquationChart Z D => f ⁻¹ᵁ g ⁻¹ᵁ c.chart.openSet)
    (pulled_cover (f ≫ g) D hD)
  intro c
  rw [pullbackDivisor_restrict_le (f ≫ g) D hD c (W := f ⁻¹ᵁ g ⁻¹ᵁ c.chart.openSet) le_rfl,
    pullbackDivisor_restrict_le f (pullbackDivisor g D hD)
      (pullbackDivisor_hasRegularEquations g D hD) (pullbackDivisor_regularChart g D hD c)
      (W := f ⁻¹ᵁ g ⁻¹ᵁ c.chart.openSet) le_rfl]
  refine congrArg (cartierEquationClassHom X _) (congrArg Additive.ofMul (Units.ext ?_))
  rw [pulledEquation_val, pulledEquation_val, functionFieldMap_comp, CommRingCat.comp_apply]
  rfl

end KltDP.Geometry.CartierDivisorPullbackComp
