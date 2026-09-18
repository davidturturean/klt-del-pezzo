import KltDP.Geometry.GluedAdjunctionCommonRefinementMaps

/-!
# Cached one-sided expansions of the original common-refinement maps

Both equalities start with Eq.refl of the original named map and unfold only
the listed map definitions on the left. Their native Hom carriers and literal
original maps on the right are retained. No expected concrete equation is
reconstructed, and no scheme or module dictionary is unfolded.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionCommonRefinementOriginalMaps
open GluedAdjunctionChartBasis

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
  (hI : IdealLocallyPrincipalRegular I)

/-- The exact original chart hom with only its chart-record wrapper expanded. -/
def iso_hom_expansion (c : Chart f I) := by
  have h := Eq.refl ((GluedAdjunctionCommonRefinement.iso f I hI c).hom)
  conv at h =>
    lhs
    unfold GluedAdjunctionCommonRefinement.iso
  exact h

/-- The exact original restricted hom with only its named map definitions expanded. -/
def refinedHom_expansion (c : Chart f I) (r : Γ(X, c.U.1)) := by
  have h := Eq.refl (GluedAdjunctionCommonRefinement.refinedHom f I hI c r)
  conv at h =>
    lhs
    unfold GluedAdjunctionCommonRefinement.refinedHom
      GluedAdjunctionCommonRefinement.refinementIso GluedAdjunctionCommonRefinement.iso
  exact h

end KltDP.Geometry.GluedAdjunctionCommonRefinementOriginalMaps
