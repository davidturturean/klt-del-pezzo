import KltDP.Geometry.DominantCartierPullbackTransitionUnits

/-!
# The actual module of an arbitrary signed Cartier pullback

Recover the original Cartier module from its actual equation atlas, pull
back that matching-coordinate sheaf, and identify the pulled units with
the actual signed pullback's equation atlas. All three comparisons are
the existing module-sheaf recovery and pullback-gluing isomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.DominantCartierPullback

open TransitionUnitGluing TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (π : X ⟶ Y) [GenericPointPreserving π]

/-- Pullback of the original module of any signed Cartier divisor is
the original module of its actual signed Cartier pullback. -/
def modulePullbackIso (D : CartierDivisor Y) :
    (schemeModulePullback π).obj (cartierDivisorModule Y D) ≅
      cartierDivisorModule X (pullbackHom π D) := by
  let t := cartierDivisorLocalTrivializations Y D
  let g := transitionUnits Y (cartierDivisorModule Y D) t
  let v := RationalTreePicard.pullbackUnits π t.X g
  let t' := pulledAtlas π D
  have hv : transitionUnits X (cartierDivisorModule X (pullbackHom π D)) t' = v := by
    funext c d
    exact pulledAtlas_transitionUnits π D c d
  let e₁ := (schemeModulePullback π).mapIso
    (recoveryIso Y (cartierDivisorModule Y D) t)
  let e₂ := pullbackGluedIso π t.X g
    (transitionUnits_isCocycle Y (cartierDivisorModule Y D) t)
    (chartOpens_cover Y (cartierDivisorModule Y D) t)
  let e₃ : moduleSheaf X (fun c => π ⁻¹ᵁ t.X c) v ≅
      moduleSheaf X t'.X
        (transitionUnits X (cartierDivisorModule X (pullbackHom π D)) t') :=
    eqToIso (congrArg (moduleSheaf X (fun c => π ⁻¹ᵁ t.X c)) hv.symm)
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫
    (recoveryIso X (cartierDivisorModule X (pullbackHom π D)) t').symm

end KltDP.Geometry.DominantCartierPullback
