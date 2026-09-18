import KltDP.Examples.FrobeniusGraphPicardClassRulingCoordinates
import KltDP.Geometry.CartierPullbackComparison

/-!
# The original product projections and their coordinate function-field maps

The actual diagonal is a section of each original ruling projection.
Specialization of the generic point along this section proves generic-point
preservation, supplying the hypothesis of the existing Cartier pullback.
The resulting function-field map agrees with the already defined ruling
coordinates through the original section germs and stalk maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusInitialCanonicalFiberMaps

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassRulingCoordinates

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance fiberMapsProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance fiberMapsLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

local instance fiberMapsChartNonempty (i : Fin 2) : Nonempty (chartOpen k i) :=
  ⟨⟨(rulingProjection (k := k) 0).base (genericPoint (projectiveProduct k)),
    rulingGeneric_mem 0 i⟩⟩

/-- Each original product projection preserves the original generic point. -/
theorem rulingProjection_genericPointPreserving (d : Fin 2) :
    GenericPointPreserving (rulingProjection (k := k) d) := by
  let s : projectiveSpace k 1 ⟶ projectiveProduct k :=
    pullback.lift (𝟙 _) (𝟙 _) (by simp only [Category.id_comp])
  have hs : s ≫ rulingProjection d = 𝟙 _ := by
    fin_cases d <;> simp [rulingProjection, s]
  refine ⟨?_⟩
  have h := (genericPoint_specializes (s.base (genericPoint (projectiveSpace k 1)))).map
    (rulingProjection d).continuous
  rw [← Scheme.comp_base_apply, hs] at h
  exact (h.antisymm (genericPoint_specializes _)).eq

local instance fiberMapsGeneric (d : Fin 2) :
    GenericPointPreserving (rulingProjection (k := k) d) :=
  rulingProjection_genericPointPreserving d

/-- Cartier's original function-field pullback sends the first chart coordinate
to the existing ruling coordinate. -/
theorem functionFieldMap_leftCoordinate (d : Fin 2) :
    functionFieldMap (rulingProjection (k := k) d)
        ((projectiveSpace k 1).germToFunctionField (chartOpen k 0) leftCoordinateSection) =
      rulingLeft d := by
  simp only [functionFieldMap, Scheme.germToFunctionField, CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes_apply, rulingLeft]

/-- The same original function-field map preserves the reciprocal coordinate. -/
theorem functionFieldMap_rightCoordinate (d : Fin 2) :
    functionFieldMap (rulingProjection (k := k) d)
        ((projectiveSpace k 1).germToFunctionField (chartOpen k 1) rightCoordinateSection) =
      rulingRight d := by
  simp only [functionFieldMap, Scheme.germToFunctionField, CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes_apply, rulingRight]

end KltDP.Examples.FrobeniusInitialCanonicalFiberMaps
