import KltDP.Geometry.QuadraticFrameUnitCoordinates
import KltDP.Geometry.QuadraticPulledMatchingCoordinates

/-!
# Original transition units through both affine refinements

Pullback of the original refined units, followed by the actual new
refinement, equals direct refinement of the original pulled units. Thus
the units supplied by the actual pulled frame obey the literal overlap
maps in the base-change atlas of the original quadratic cover.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.QuadraticRefinedPullbackUnits

open TransitionUnitGluing TransitionUnitExtraction RationalTreePicard
open QuadraticFrameUnitCoordinates QuadraticPulledMatchingCoordinates

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {I J K : Type u}
    (U : I → X.Opens) (g : ∀ i j, Γ(X, U i ⊓ U j)ˣ)
    (V : J → X.Opens) (σ : J → I) (hσ : ∀ j, V j ≤ U (σ j))
    (W : K → Y.Opens) (τ : K → J) (hτ : ∀ k, W k ≤ f ⁻¹ᵁ V (τ k))

/-- Refinement and pullback retain the same original section-ring unit. -/
theorem refined_pullback_refined (i j : K) :
    refinedUnits Y (fun j => f ⁻¹ᵁ V j)
      (pullbackUnits f V (refinedUnits X U g V σ hσ)) W τ hτ i j =
      refinedUnits Y (fun i => f ⁻¹ᵁ U i) (pullbackUnits f U g) W
        (fun k => σ (τ k))
        (fun k => (hτ k).trans ((Opens.map f.base).map (homOfLE (hσ (τ k)))).le) i j := by
  apply Units.ext
  simp only [refinedUnits_val, pullbackUnits_val, app_res, res_res]

variable (hc : IsCocycle X U g) (hU : (⨆ i, U i) = ⊤)
    (t : (schemeModulePullback f).obj (moduleSheaf X U g) ≅
      _root_.SheafOfModules.unit Y.ringCatSheaf) (b : Γ(Y, ⊤)ˣ)

/-- Actual ambient frame units satisfy the original twice-refined overlap equation. -/
theorem unitOn_original_overlap (i j : K) :
    res Y (inf_le_left : W i ⊓ W j ≤ W i)
      (unitOn Y ((schemeModulePullback f).obj (moduleSheaf X U g))
        (pulledAtlas U g hc f hU) t b (σ (τ i)) (W := W i)
        ((hτ i).trans ((Opens.map f.base).map (homOfLE (hσ (τ i)))).le) : Γ(Y, W i)) =
      (refinedUnits Y (fun j => f ⁻¹ᵁ V j)
        (pullbackUnits f V (refinedUnits X U g V σ hσ)) W τ hτ i j : Γ(Y, W i ⊓ W j)) *
        res Y inf_le_right
          (unitOn Y ((schemeModulePullback f).obj (moduleSheaf X U g))
            (pulledAtlas U g hc f hU) t b (σ (τ j)) (W := W j)
            ((hτ j).trans ((Opens.map f.base).map (homOfLE (hσ (τ j)))).le) : Γ(Y, W j)) := by
  have he : transitionUnits Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) = pullbackUnits f U g :=
    funext fun i => funext fun j => transitionUnits_pulled f U g hc hU i j
  have h := refined_overlap Y ((schemeModulePullback f).obj (moduleSheaf X U g))
    (pulledAtlas U g hc f hU) t b W (fun k => σ (τ k))
    (fun k => (hτ k).trans ((Opens.map f.base).map (homOfLE (hσ (τ k)))).le) i j
  rw [refined_pullback_refined]
  simpa only [he] using h

end KltDP.Geometry.QuadraticRefinedPullbackUnits

#print axioms KltDP.Geometry.QuadraticRefinedPullbackUnits.unitOn_original_overlap
