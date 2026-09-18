import KltDP.Geometry.LinearSystemNormalizedFrames
import KltDP.Geometry.PullbackTransitionUnitGluing
import KltDP.Geometry.LinearSystemCoordinateEvaluation
import KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf
import KltDP.Geometry.TransitionUnitRefinement

/-!
# The original linear-system morphism pulls degree one back to the original sheaf

Pull the original projective coordinate cocycle back along the constructed
morphism, then restrict it to the original affine source charts. The
coordinate evaluation theorem identifies those units with the units of
the normalized original sheaf atlas. Existing actual pullback, refinement,
and recovery isomorphisms give the resulting original module-sheaf iso.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemPullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing TransitionUnitExtraction LinearSystemMorphism
  InvertibleSectionNonvanishingOpen ProjectiveCoordinateSectionBasicOpen
  ProjectiveSpaceDegreeOneSheaf RationalTreePicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections) (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

/-- On each original chart overlap, the pulled projective unit is the
actual transition unit of the normalized original sheaf frames. -/
theorem normalizedAtlas_transitionUnits_pullback (c d : Chart L s) :
    ((transitionUnits X L.obj (normalizedAtlas L s hcover) c d).val :
        Γ(X, c.affineOpen.1 ⊓ d.affineOpen.1)) =
      res X (le_inf
        (inf_le_left.trans (chart_le_preimage_standardOpen L s f hcover c))
        (inf_le_right.trans (chart_le_preimage_standardOpen L s f hcover d)))
        (pullbackUnits (morphism L s f hcover) (chart k n) (overlapUnit k n)
          (ULift.up c.index) (ULift.up d.index)) := by
  rw [normalizedAtlas_transitionUnits_val L s hcover c d]
  simp only [pullbackUnits_val, overlapUnit_val, RationalTreePicard.app_res, res_res]
  rw [← morphism_appLE_coordinateSection L s f hcover c
    (chart_le_preimage_standardOpen L s f hcover c) d.index]
  change res X inf_le_left
      (res X (chart_le_preimage_standardOpen L s f hcover c)
        ((morphism L s f hcover).app (standardOpen k n c.index)
          (coordinateSection k n c.index d.index))) = _
  exact res_res X _ _ _

/-- The actual linear-system morphism pulls the original degree-one
invertible sheaf back to the original invertible sheaf. -/
def pullbackDegreeOneIso :
    (pullbackInvertibleSheaf (morphism L s f hcover) (degreeOne k n)).obj ≅ L.obj := by
  let g := morphism L s f hcover
  let U := chart k n
  let v := overlapUnit k n
  let V := fun c : Chart L s => c.affineOpen.1
  let σ := fun c : Chart L s => (ULift.up c.index : ULift.{u} (Fin (n + 1)))
  let hσ : ∀ c : Chart L s, V c ≤ g ⁻¹ᵁ U (σ c) :=
    chart_le_preimage_standardOpen L s f hcover
  let p := pullbackUnits g U v
  let t := normalizedAtlas L s hcover
  let e₁ : (pullbackInvertibleSheaf g (degreeOne k n)).obj ≅
      moduleSheaf X (fun i => g ⁻¹ᵁ U i) p :=
    pullbackGluedIso g U v (overlapUnit_isCocycle k n) (chart_cover k n)
  let e₂ : moduleSheaf X (fun i => g ⁻¹ᵁ U i) p ≅
      moduleSheaf X V (transitionUnits X L.obj t) :=
    subordinationIso X (σ := σ) hσ
      (normalizedAtlas_transitionUnits_pullback L s f hcover)
      (pullbackUnits_isCocycle g U v (overlapUnit_isCocycle k n))
      (fun x => Opens.mem_iSup.mp (show x ∈ ⨆ c : Chart L s, V c from by
        change x ∈ ⨆ c : Chart L s, c.affineOpen.1
        rw [LinearSystemMorphism.chartOpens_cover L s hcover]
        trivial))
  exact e₁ ≪≫ e₂ ≪≫ (normalizedRecoveryIso L s hcover).symm

end KltDP.Geometry.LinearSystemPullback
