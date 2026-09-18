import KltDP.Geometry.RationalTreePicardPulledFrameCoordinate
import KltDP.Geometry.TransitionUnitRefinementCocycle

/-!
# Original matching coordinates after actual scheme pullback

The accepted pulled-frame normalization gives the literal coordinate
formula for every original matching section. Thus the actual pulled
frame records the original ambient coefficient through the original
structure-sheaf map. This strengthens the earlier Picard-class comparison
to the section formula needed by the quadratic ambient-cover comparison.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u

namespace KltDP.Geometry.QuadraticPulledMatchingCoordinates

attribute [local instance] Types.instFunLike Types.instConcreteCategory
open TransitionUnitGluing TransitionUnitExtraction RationalTreePicard

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (g : ∀ i j, Γ(X, U i ⊓ U j)ˣ) (hc : IsCocycle X U g)
    (hU : (⨆ i, U i) = ⊤)

/-- Every original local section is its actual coordinate times its original frame. -/
theorem section_eq_coordinate_smul_frame (i : ι) (s : sections X U g (U i)) :
    s = trivialization X U g hc i le_rfl s • chartFrame U g hc i := by
  apply (trivialization X U g hc i le_rfl).injective
  rw [map_smul, trivialization_chartFrame, smul_eq_mul, mul_one]

/-- The original pulled atlas sends the actual pulled section to its original
ambient chart coordinate through the actual structural section-ring map. -/
theorem chartEquiv_pulledSection (i : ι) (s : sections X U g (U i)) :
    chartEquiv Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) i (W := f ⁻¹ᵁ U i) le_rfl (pulledSection f (moduleSheaf X U g) (U i) s) =
      f.app (U i) (trivialization X U g hc i le_rfl s) := by
  have hs := section_eq_coordinate_smul_frame U g hc i s
  refine (congrArg (fun z : sections X U g (U i) =>
    chartEquiv Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) i (W := f ⁻¹ᵁ U i) le_rfl
        (pulledSection f (moduleSheaf X U g) (U i) z)) hs).trans ?_
  rw [pulledSection_smul, map_smul]
  change f.app (U i) (trivialization X U g hc i le_rfl s) •
    chartEquiv Y _ (pulledAtlas U g hc f hU) i (W := f ⁻¹ᵁ U i) le_rfl (pulledFrame U g hc f i) = _
  have hcoord : chartEquiv Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) i (W := f ⁻¹ᵁ U i) le_rfl (pulledFrame U g hc f i) =
      (1 : Γ(Y, f ⁻¹ᵁ U i)) := pulledFrameCoordinate f U g hc hU i
  let c : Γ(Y, f ⁻¹ᵁ U i) := f.app (U i) (trivialization X U g hc i le_rfl s)
  exact (congrArg (fun z : Γ(Y, f ⁻¹ᵁ U i) => c * z) hcoord).trans (mul_one c)

/-- On any actual smaller open, the coefficient is the original appLE value. -/
theorem chartEquiv_restricted_pulledSection (i : ι) (s : sections X U g (U i))
    (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U i) :
    chartEquiv Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) i hV
      (((schemeModulePullback f).obj (moduleSheaf X U g)).val.map (homOfLE hV).op
        (pulledSection f (moduleSheaf X U g) (U i) s)) =
      f.appLE (U i) V hV (trivialization X U g hc i le_rfl s) := by
  exact (chartEquiv_restrict Y ((schemeModulePullback f).obj (moduleSheaf X U g))
    (pulledAtlas U g hc f hU) i hV
    (show f ⁻¹ᵁ U i ≤ (pulledAtlas U g hc f hU).X i from le_rfl)
    (pulledSection f (moduleSheaf X U g) (U i) s)).trans
      (congrArg (res Y hV) (chartEquiv_pulledSection f U g hc hU i s))

/-- The original pulled atlas's extracted transitions equal the literal
pullback of the original ambient transitions. -/
theorem transitionUnits_pulled (i j : ι) :
    transitionUnits Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) i j = pullbackUnits f U g i j :=
  transitionUnits_pulledAtlas U g hc f hU (pulledFrameCoordinate f U g hc hU) i j

end KltDP.Geometry.QuadraticPulledMatchingCoordinates

#print axioms KltDP.Geometry.QuadraticPulledMatchingCoordinates.chartEquiv_restricted_pulledSection
