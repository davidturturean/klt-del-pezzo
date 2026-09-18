import KltDP.Geometry.DominantCartierPullbackEquations
import KltDP.Geometry.CartierDivisorPullbackIdentity

/-!
Identity and composition for the original signed Cartier pullback. The
accepted generic-stalk function-field laws identify the actual local
equations on the original divisor's covering equation charts. Local
equality of Cartier sections then gives equality of the additive maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.DominantCartierPullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

/-- Actual rational units are unchanged by the identity field map. -/
theorem functionFieldUnitMap_id (a : X.functionFieldˣ) :
    Units.map (functionFieldMap (𝟙 X)).hom.toMonoidHom a = a := by
  apply Units.ext
  change functionFieldMap (𝟙 X) (a : X.functionField) = (a : X.functionField)
  rw [CartierDivisorPullbackIdentity.functionFieldMap_id]
  rfl

/-- The original generic-stalk field maps compose on rational units. -/
theorem functionFieldUnitMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [GenericPointPreserving f] [GenericPointPreserving g] (a : Z.functionFieldˣ) :
    Units.map (functionFieldMap (f ≫ g)).hom.toMonoidHom a =
      Units.map (functionFieldMap f).hom.toMonoidHom
        (Units.map (functionFieldMap g).hom.toMonoidHom a) := by
  apply Units.ext
  change functionFieldMap (f ≫ g) (a : Z.functionField) =
    functionFieldMap f (functionFieldMap g (a : Z.functionField))
  rw [CartierDivisorPullbackComp.functionFieldMap_comp]
  rfl

/-- Pullback by the original identity is the identity on all signed
Cartier divisors. -/
theorem pullbackHom_id :
    pullbackHom (𝟙 X) = AddMonoidHom.id (CartierDivisor X) := by
  apply AddMonoidHom.ext
  intro D
  change pullbackHom (𝟙 X) D = D
  refine cartierDivisor_eq_of_restrict_eq X
    (fun c : CartierEquationChart X D => c.openSet)
    (preimageEquationCharts_cover (𝟙 X) D) _ D (fun c => ?_)
  have h := pullbackHom_globalEquation_preimage (𝟙 X) D c.openSet c.equation c.represents
  rw [functionFieldUnitMap_id] at h
  exact h.symm.trans c.represents

/-- Signed Cartier pullback is contravariantly compatible with the
original composition of generic-point-preserving scheme morphisms. -/
theorem pullbackHom_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [GenericPointPreserving f] [GenericPointPreserving g] :
    pullbackHom (f ≫ g) = (pullbackHom f).comp (pullbackHom g) := by
  apply AddMonoidHom.ext
  intro D
  change pullbackHom (f ≫ g) D = pullbackHom f (pullbackHom g D)
  refine cartierDivisor_eq_of_restrict_eq X
    (fun c : CartierEquationChart Z D => f ⁻¹ᵁ g ⁻¹ᵁ c.openSet)
    (preimageEquationCharts_cover (f ≫ g) D) _ _ (fun c => ?_)
  have hg := pullbackHom_globalEquation_preimage g D c.openSet c.equation c.represents
  have hf := pullbackHom_globalEquation_preimage f (pullbackHom g D)
    (g ⁻¹ᵁ c.openSet) (Units.map (functionFieldMap g).hom.toMonoidHom c.equation) hg
  have hfg := pullbackHom_globalEquation_preimage (f ≫ g) D
    c.openSet c.equation c.represents
  rw [functionFieldUnitMap_comp] at hfg
  exact hfg.symm.trans hf

end KltDP.Geometry.DominantCartierPullback
