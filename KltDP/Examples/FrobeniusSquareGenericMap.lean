import KltDP.Examples.FrobeniusGraphPicardClassPowerCharts
import KltDP.Geometry.SpecFunctionFieldMap
import KltDP.Geometry.GenericPointPreservingTriangle
import KltDP.Geometry.CartierDivisorPullbackComp
import KltDP.Geometry.OpenImmersionFunctionField
import KltDP.Geometry.ProjectiveSpaceIntegral
import Mathlib.Algebra.Polynomial.Expand

/-!
# The original square morphism at the generic point

The literal polynomial-chart equation proves generic-point preservation
for the original projective power morphism. Functoriality of the actual
generic stalk maps then gives its original affine-chart square.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusSquareGenericMap

open KltDP.Geometry ProjectiveLineComparison FrobeniusProjectiveMorphism
  FrobeniusGlobalGraphCompatibility FrobeniusGraphPicardClassPowerCharts

variable (k : Type u) [Field k]

local instance genericLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

local instance chartGeneric (i : Fin 2) :
    GenericPointPreserving (polynomialChartMap k i) :=
  ⟨genericPoint_eq_of_isOpenImmersion _⟩

instance squareSpecGeneric :
    GenericPointPreserving (Spec.map (CommRingCat.ofHom (polynomialPowerHom (k := k) 2))) :=
  SpecFunctionFieldMap.genericPointPreserving _
    (Polynomial.expand_injective (R := k) (by decide : 0 < 2))

/-- The original global projective square map preserves the generic point. -/
instance projectiveSquareGeneric :
    GenericPointPreserving (projectivePowerMorphism (k := k) 2) :=
  GenericPointPreservingTriangle.right_of_comp_eq (polynomialChartMap k 0)
    (projectivePowerMorphism 2)
    (Spec.map (CommRingCat.ofHom (polynomialPowerHom 2)) ≫ polynomialChartMap k 0)
    (polynomialChartMap_power_both 2 0)

private theorem fieldMap_congr {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f g : X ⟶ Y) [GenericPointPreserving f] [GenericPointPreserving g]
    (h : f = g) : functionFieldMap f = functionFieldMap g := by
  subst g
  rfl

/-- The generic map square is for the same whole morphisms as the chart equation. -/
theorem functionFieldMap_chart (i : Fin 2) :
    functionFieldMap (projectivePowerMorphism (k := k) 2) ≫
        functionFieldMap (polynomialChartMap k i) =
      functionFieldMap (polynomialChartMap k i) ≫
        functionFieldMap (Spec.map (CommRingCat.ofHom (polynomialPowerHom 2))) := by
  calc
    _ = functionFieldMap (polynomialChartMap k i ≫ projectivePowerMorphism 2) :=
      (CartierDivisorPullbackComp.functionFieldMap_comp (polynomialChartMap k i)
        (projectivePowerMorphism 2)).symm
    _ = functionFieldMap
        (Spec.map (CommRingCat.ofHom (polynomialPowerHom 2)) ≫ polynomialChartMap k i) :=
      fieldMap_congr _ _ (polynomialChartMap_power_both 2 i)
    _ = _ := CartierDivisorPullbackComp.functionFieldMap_comp
      (Spec.map (CommRingCat.ofHom (polynomialPowerHom 2))) (polynomialChartMap k i)

end KltDP.Examples.FrobeniusSquareGenericMap
