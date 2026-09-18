import KltDP.Geometry.QuadraticCoverBaseChangeChartInclusion

/-!
# Actual coverage of the original global quadratic pullback

The local pullback squares identify each chart image with the inverse image
of its original affine base open. The affine refinement covers the actual
base, hence these exact chart maps cover the actual global pullback.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

variable {X Y : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)
  (f : Y ⟶ X) [Y.IsSeparated]

/-- The literal base-change chart has exactly the prescribed inverse-image range. -/
theorem range_baseChangeChartInclusion (i : D.BaseChangeIndex f) :
    Set.range (D.baseChangeChartInclusion f i).base =
      (pullback.snd D.morphism f).base ⁻¹' (D.baseChangeOpens f i : Set Y) := by
  let H := D.baseChangeChartInclusionIsPullback f i
  have hr : Set.range (D.baseChangeChartInclusion f i).base =
      Set.range (pullback.fst (pullback.snd D.morphism f)
        ((D.baseChangeAtlas f).affine i).fromSpec).base := by
    rw [← H.isoPullback_hom_fst, Scheme.comp_base, TopCat.coe_comp]
    exact Function.Surjective.range_comp
      (f := H.isoPullback.hom.base)
      (ConcreteCategory.bijective_of_isIso (C := TopCat) H.isoPullback.hom.base).surjective _
  rw [hr, IsOpenImmersion.range_pullback_fst_of_right]
  change _ ⁻¹' Set.range ((D.baseChangeAtlas f).affine i).fromSpec.base = _
  rw [IsAffineOpen.range_fromSpec]
  rfl

/-- Actual coverage follows from the actual affine base cover. -/
theorem baseChangeCharts_cover (z : (pullback D.morphism f : Scheme.{u})) :
    ∃ i x, (D.baseChangeChartInclusion f i).base x = z := by
  have hz : (pullback.snd D.morphism f).base z ∈
      ⨆ i, (D.baseChangeAtlas f).opens i := by
    rw [(D.baseChangeAtlas f).covers]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hz
  have hr : z ∈ Set.range (D.baseChangeChartInclusion f i).base := by
    rw [range_baseChangeChartInclusion]
    exact hi
  obtain ⟨x, hx⟩ := hr
  exact ⟨i, x, hx⟩

/-- The actual pulled atlas is an open cover of the actual original pullback. -/
def baseChangeCover : (pullback D.morphism f).OpenCover :=
  Scheme.Cover.mkOfCovers (D.BaseChangeIndex f) ((D.baseChangeAtlas f).chart)
    (D.baseChangeChartInclusion f) (D.baseChangeCharts_cover f)

#print axioms baseChangeCharts_cover

end KltDP.Geometry.QuadraticCoverAtlas.Data
