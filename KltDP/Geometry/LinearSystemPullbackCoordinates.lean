import KltDP.Geometry.LinearSystemNormalizedFrames
import KltDP.Geometry.InvertibleSectionNonvanishingPullback

/-!
# Original normalized coordinates under scheme pullback

The actual pulled sections cover by the proved intrinsic nonvanishing
pullback formula. Pulling the original normalized atlas gives the literal
structural pullback of its coordinate functions. Comparing this atlas
with the original normalized source atlas yields the projective scaling
identity on each common subopen. No frame compatibility is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemNaturality

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitExtraction TransitionUnitGluing
  InvertibleSectionNonvanishingOpen LinearSystemMorphism LinearSystemPullback

variable {X Y : Scheme.{u}} (h : Y ⟶ X) (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections)

/-- The original compatible sections pulled through the original module-sheaf functor. -/
abbrev pullbackSections : Fin (n + 1) → (pullbackInvertibleSheaf h L).obj.sections :=
  fun j => InvertibleSheafSectionPowersPullback.pullbackSection h L.obj (s j)

/-- The original pulled section opens cover the source of every scheme morphism. -/
theorem pullbackSections_cover (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤) :
    (⨆ j, nonvanishingOpen Y (pullbackInvertibleSheaf h L) (pullbackSections h L s j)) = ⊤ := by
  calc
    _ = ⨆ j, h ⁻¹ᵁ nonvanishingOpen X L (s j) :=
      iSup_congr (fun j =>
        InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback h L (s j))
    _ = h ⁻¹ᵁ (⨆ j, nonvanishingOpen X L (s j)) :=
      (h.preimage_iSup (fun j => nonvanishingOpen X L (s j))).symm
    _ = h ⁻¹ᵁ ⊤ := congrArg (fun U : X.Opens => h ⁻¹ᵁ U) hcover
    _ = ⊤ := rfl

variable (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

/-- The original target's normalized frames pulled to their actual inverse-image opens. -/
def pulledNormalizedAtlas :
    KltDP.SheafOfModules.LocalTrivializations (R := Y.ringCatSheaf)
      (pullbackInvertibleSheaf h L).obj :=
  InvertibleSectionNonvanishingPullback.pullbackAtlas h L.obj (normalizedAtlas L s hcover)

/-- In the pulled original frame, each original pulled coefficient is the actual section map. -/
theorem pulledNormalizedAtlas_chartCoefficient (d : Chart L s) (j : Fin (n + 1)) :
    chartCoefficient Y (pullbackInvertibleSheaf h L).obj
      (pulledNormalizedAtlas h L s hcover) (pullbackSections h L s j) d =
        h.app d.affineOpen.1
          (coordinates L s d.frame d.inFrame d.index d.nonvanishing j) := by
  have hc : chartCoefficient X L.obj (normalizedAtlas L s hcover) (s j) d =
      coordinates L s d.frame d.inFrame d.index d.nonvanishing j :=
    normalizedAtlas_chartEquiv_top L s hcover d j
  exact (InvertibleSectionNonvanishingPullback.chartCoefficient_pullback
    h L.obj (normalizedAtlas L s hcover) (s j) d).trans
      (congrArg (fun a : Γ(X, d.affineOpen.1) => h.app d.affineOpen.1 a) hc)

/-- The same formula on every original source subopen is the original appLE map. -/
theorem pulledNormalizedAtlas_chartEquiv_section (d : Chart L s)
    {W : Y.Opens} (hWd : W ≤ h ⁻¹ᵁ d.affineOpen.1) (j : Fin (n + 1)) :
    chartEquiv Y (pullbackInvertibleSheaf h L).obj
      (pulledNormalizedAtlas h L s hcover) d hWd
      ((pullbackSections h L s j).val (op W)) =
        h.appLE d.affineOpen.1 W hWd
          (coordinates L s d.frame d.inFrame d.index d.nonvanishing j) := by
  exact (chartCoefficient_restrict Y (pullbackInvertibleSheaf h L).obj
    (pulledNormalizedAtlas h L s hcover) (pullbackSections h L s j) d hWd).symm.trans
      ((congrArg (res Y hWd) (pulledNormalizedAtlas_chartCoefficient h L s hcover d j)).trans
        (by rfl))

private theorem sourceNormalizedAtlas_chartEquiv_section
    (c : Chart (pullbackInvertibleSheaf h L) (pullbackSections h L s))
    {W : Y.Opens} (hWc : W ≤ c.affineOpen.1) (j : Fin (n + 1)) :
    chartEquiv Y (pullbackInvertibleSheaf h L).obj
      (normalizedAtlas (pullbackInvertibleSheaf h L) (pullbackSections h L s)
        (pullbackSections_cover h L s hcover)) c hWc
      ((pullbackSections h L s j).val (op W)) =
        res Y hWc (coordinates (pullbackInvertibleSheaf h L) (pullbackSections h L s)
          c.frame c.inFrame c.index c.nonvanishing j) :=
  (normalizedAtlas_chartEquiv_section (pullbackInvertibleSheaf h L)
    (pullbackSections h L s) (pullbackSections_cover h L s hcover) c hWc j).trans
      (coordinates_restrict (pullbackInvertibleSheaf h L) (pullbackSections h L s)
        c.frame hWc c.inFrame c.index c.nonvanishing j).symm

include hcover in
/-- The actual source coordinates and original pulled target coordinates satisfy scaling. -/
theorem coordinates_pullback_scale
    (c : Chart (pullbackInvertibleSheaf h L) (pullbackSections h L s)) (d : Chart L s)
    {W : Y.Opens} (hWc : W ≤ c.affineOpen.1) (hWd : W ≤ h ⁻¹ᵁ d.affineOpen.1)
    (j : Fin (n + 1)) :
    res Y hWc (coordinates (pullbackInvertibleSheaf h L) (pullbackSections h L s)
      c.frame c.inFrame c.index c.nonvanishing j) =
    res Y hWc (coordinates (pullbackInvertibleSheaf h L) (pullbackSections h L s)
      c.frame c.inFrame c.index c.nonvanishing d.index) *
        h.appLE d.affineOpen.1 W hWd
          (coordinates L s d.frame d.inFrame d.index d.nonvanishing j) := by
  let a := chartEquiv Y (pullbackInvertibleSheaf h L).obj
    (normalizedAtlas (pullbackInvertibleSheaf h L) (pullbackSections h L s)
      (pullbackSections_cover h L s hcover)) c hWc
  let b := chartEquiv Y (pullbackInvertibleSheaf h L).obj
    (pulledNormalizedAtlas h L s hcover) d hWd
  let u := KltDP.Module.transitionUnit b a
  have hr (r : Fin (n + 1)) :
      res Y hWc (coordinates (pullbackInvertibleSheaf h L) (pullbackSections h L s)
        c.frame c.inFrame c.index c.nonvanishing r) =
      (u : Γ(Y, W)) * h.appLE d.affineOpen.1 W hWd
        (coordinates L s d.frame d.inFrame d.index d.nonvanishing r) :=
    (sourceNormalizedAtlas_chartEquiv_section h L s hcover c hWc r).symm.trans
      ((KltDP.Module.transitionUnit_mul_apply b a
        ((pullbackSections h L s r).val (op W))).symm.trans
          (congrArg (fun v : Γ(Y, W) => (u : Γ(Y, W)) * v)
            (pulledNormalizedAtlas_chartEquiv_section h L s hcover d hWd r)))
  have hd : h.appLE d.affineOpen.1 W hWd
      (coordinates L s d.frame d.inFrame d.index d.nonvanishing d.index) = 1 :=
    (congrArg (fun v : Γ(X, d.affineOpen.1) => h.appLE d.affineOpen.1 W hWd v)
      (coordinates_self L s d.frame d.inFrame d.index d.nonvanishing)).trans
        (map_one (h.appLE d.affineOpen.1 W hWd).hom)
  have hu : res Y hWc
      (coordinates (pullbackInvertibleSheaf h L) (pullbackSections h L s)
        c.frame c.inFrame c.index c.nonvanishing d.index) = (u : Γ(Y, W)) :=
    (hr d.index).trans
      ((congrArg (fun v : Γ(Y, W) => (u : Γ(Y, W)) * v) hd).trans (mul_one _))
  exact (hr j).trans (congrArg (fun v : Γ(Y, W) => v *
    h.appLE d.affineOpen.1 W hWd
      (coordinates L s d.frame d.inFrame d.index d.nonvanishing j)) hu.symm)

end KltDP.Geometry.LinearSystemNaturality
