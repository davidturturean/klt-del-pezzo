import KltDP.Geometry.RationalTreePicardPulledFrameCoordinate
import KltDP.Geometry.TransitionUnitRecovery

/-!
# The actual pullback isomorphism for a transition-unit sheaf

The accepted pulled-frame coordinate theorem identifies the extracted
units of the actual pullback atlas. Composing its existing recovery
isomorphism with that equality gives the actual module-sheaf isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

open TransitionUnitExtraction RationalTreePicard

/-- The original pullback sheaf is the sheaf glued from the pulled-back original units. -/
def pullbackGluedIso {X Y : Scheme.{u}} (f : Y ⟶ X) {ι : Type u}
    (U : ι → X.Opens) (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)
    (hg : IsCocycle X U g) (hU : (⨆ i, U i) = ⊤) :
    (schemeModulePullback f).obj (moduleSheaf X U g) ≅
      moduleSheaf Y (fun i => f ⁻¹ᵁ U i) (pullbackUnits f U g) := by
  let t := pulledAtlas U g hg f hU
  have hunits : transitionUnits Y ((schemeModulePullback f).obj (moduleSheaf X U g)) t =
      pullbackUnits f U g := by
    funext i j
    exact transitionUnits_pulledAtlas U g hg f hU
      (fun a => pulledFrameCoordinate f U g hg hU a) i j
  exact recoveryIso Y ((schemeModulePullback f).obj (moduleSheaf X U g)) t ≪≫
    eqToIso (congrArg (moduleSheaf Y (fun i => f ⁻¹ᵁ U i)) hunits)

end KltDP.Geometry.TransitionUnitGluing
