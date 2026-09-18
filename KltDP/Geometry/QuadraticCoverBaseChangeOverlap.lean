import KltDP.Geometry.QuadraticCoverBaseChangeChartInclusion
import KltDP.Geometry.QuadraticCoverAppLE

/-!
# Actual original overlap maps for the pulled quadratic atlas

The pair-chart map uses the original `appLE` on the actual old and new
intersections. Both paths to the original charts are computed by the
already proved composition rule for the literal quadratic quotient maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover QuadraticTransitionCocycle QuadraticCoverAppLE

variable {X Y : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)
  (f : Y ⟶ X) [Y.IsSeparated]

/-- Literal old and new pair intersections are connected by their original section map. -/
def baseChangeOverlapMap (i j : D.BaseChangeIndex f) :
    (D.baseChangeAtlas f).overlap i j ⟶
      D.overlap (D.baseChangeOriginal f i) (D.baseChangeOriginal f j) :=
  mappedRescaleMap
    (f.appLE (D.opens (D.baseChangeOriginal f i) ⊓ D.opens (D.baseChangeOriginal f j))
      (D.baseChangeOpens f i ⊓ D.baseChangeOpens f j)
      (D.baseChangePairSubordinate f i j)).hom
    (res X inf_le_left (D.sections (D.baseChangeOriginal f i)))
    (res Y inf_le_left ((D.baseChangeAtlas f).sections i)) 1
    (by simp only [Units.val_one, one_pow, one_mul, baseChangeAtlas, baseChangeSections,
      appLE_res, res_appLE])

/-- The left restriction square preserves the original quadratic chart map. -/
theorem baseChangeOverlapMap_left (i j : D.BaseChangeIndex f) :
    (D.baseChangeAtlas f).overlapToChart i j ≫ D.baseChangeChartMap f i =
      D.baseChangeOverlapMap f i j ≫
        D.overlapToChart (D.baseChangeOriginal f i) (D.baseChangeOriginal f j) := by
  simp only [overlapToChart, map, localMap, baseChangeChartMap, baseChangeOverlapMap,
    restrictedUnit_self _ _ _ (D.baseChangeAtlas f).cocycle,
    restrictedUnit_self _ _ _ D.cocycle]
  erw [mappedRescaleMap_comp, mappedRescaleMap_comp]
  simp only [map_one, one_mul, mul_one]
  congr 1
  exact (restriction_square f inf_le_left (D.baseChangePairSubordinate f i j)
    (D.baseChangeSubordinate f i) inf_le_left).symm

/-- Any refined transition is the original transition mapped to that same actual open. -/
theorem baseChangeRestrictedUnit_val {i j : D.BaseChangeIndex f} {W : Y.Opens}
    (hi : W ≤ D.baseChangeOpens f i) (hj : W ≤ D.baseChangeOpens f j) :
    (restrictedUnit Y (D.baseChangeAtlas f).opens (D.baseChangeAtlas f).units hi hj : Γ(Y, W)) =
      f.appLE (D.opens (D.baseChangeOriginal f i) ⊓ D.opens (D.baseChangeOriginal f j)) W
        ((le_inf hi hj).trans (D.baseChangePairSubordinate f i j))
        (D.units (D.baseChangeOriginal f i) (D.baseChangeOriginal f j)) := by
  change res Y (le_inf hi hj) (D.baseChangeUnits f i j : Γ(Y, _)) = _
  rw [baseChangeUnits_val, res_appLE]

/-- The reverse transition unit follows the same original section map. -/
theorem baseChangeReverseUnit (i j : D.BaseChangeIndex f) :
    restrictedUnit Y (D.baseChangeAtlas f).opens (D.baseChangeAtlas f).units
      (inf_le_right : D.baseChangeOpens f i ⊓ D.baseChangeOpens f j ≤ D.baseChangeOpens f j)
      inf_le_left =
    Units.map
      (f.appLE (D.opens (D.baseChangeOriginal f i) ⊓ D.opens (D.baseChangeOriginal f j))
        (D.baseChangeOpens f i ⊓ D.baseChangeOpens f j)
        (D.baseChangePairSubordinate f i j)).hom.toMonoidHom
      (restrictedUnit X D.opens D.units
        (inf_le_right : D.opens (D.baseChangeOriginal f i) ⊓
          D.opens (D.baseChangeOriginal f j) ≤ D.opens (D.baseChangeOriginal f j))
        inf_le_left) := by
  apply Units.ext
  rw [baseChangeRestrictedUnit_val]
  simpa only [Units.coe_map, restrictedUnit_val] using
    (appLE_res f
      (le_inf inf_le_right inf_le_left :
        D.opens (D.baseChangeOriginal f i) ⊓ D.opens (D.baseChangeOriginal f j) ≤
          D.opens (D.baseChangeOriginal f j) ⊓ D.opens (D.baseChangeOriginal f i))
      (D.baseChangePairSubordinate f i j)
      (D.units (D.baseChangeOriginal f j) (D.baseChangeOriginal f i) :
        Γ(X, D.opens (D.baseChangeOriginal f j) ⊓ D.opens (D.baseChangeOriginal f i)))).symm

/-- The right restriction and generator change preserve the original quadratic chart map. -/
theorem baseChangeOverlapMap_right (i j : D.BaseChangeIndex f) :
    (D.baseChangeAtlas f).map (le_refl ((D.baseChangeAtlas f).opens j))
      (inf_le_left : (D.baseChangeAtlas f).opens i ⊓ (D.baseChangeAtlas f).opens j ≤
        (D.baseChangeAtlas f).opens i) inf_le_right ≫ D.baseChangeChartMap f j =
      D.baseChangeOverlapMap f i j ≫
        D.map (le_refl (D.opens (D.baseChangeOriginal f j)))
          (inf_le_left : D.opens (D.baseChangeOriginal f i) ⊓
            D.opens (D.baseChangeOriginal f j) ≤ D.opens (D.baseChangeOriginal f i))
          inf_le_right := by
  simp only [map, localMap, baseChangeChartMap, baseChangeOverlapMap]
  erw [mappedRescaleMap_comp, mappedRescaleMap_comp]
  simp only [map_one, one_mul, mul_one]
  have hφ := restriction_square f
    (inf_le_right : D.opens (D.baseChangeOriginal f i) ⊓
      D.opens (D.baseChangeOriginal f j) ≤ D.opens (D.baseChangeOriginal f j))
    (D.baseChangePairSubordinate f i j) (D.baseChangeSubordinate f j) inf_le_right
  congr 1
  · exact hφ.symm
  · exact D.baseChangeReverseUnit f i j

/-- Both new overlap paths have the same image in the actual original glued scheme. -/
theorem baseChangeChartMap_overlap (i j : D.BaseChangeIndex f) :
    (D.baseChangeAtlas f).overlapToChart i j ≫
        D.baseChangeChartMap f i ≫ D.chartι (D.baseChangeOriginal f i) =
      ((D.baseChangeAtlas f).transition i j ≫ (D.baseChangeAtlas f).overlapToChart j i) ≫
        D.baseChangeChartMap f j ≫ D.chartι (D.baseChangeOriginal f j) := by
  have h :
      (D.baseChangeAtlas f).map (le_refl ((D.baseChangeAtlas f).opens j))
        (inf_le_left : (D.baseChangeAtlas f).opens i ⊓ (D.baseChangeAtlas f).opens j ≤
          (D.baseChangeAtlas f).opens i) inf_le_right ≫
        D.baseChangeChartMap f j ≫ D.chartι (D.baseChangeOriginal f j) =
      (D.baseChangeAtlas f).overlapToChart i j ≫
        D.baseChangeChartMap f i ≫ D.chartι (D.baseChangeOriginal f i) := by
    rw [← Category.assoc, baseChangeOverlapMap_right, Category.assoc,
      direct_overlap_chart, ← Category.assoc, ← baseChangeOverlapMap_left, Category.assoc]
  simpa only [transition, overlapToChart, map_comp, Category.assoc] using h.symm

/-- The literal chart maps agree on overlaps in the actual original global pullback. -/
theorem baseChangeChartInclusion_overlap (i j : D.BaseChangeIndex f) :
    (D.baseChangeAtlas f).overlapToChart i j ≫ D.baseChangeChartInclusion f i =
      ((D.baseChangeAtlas f).transition i j ≫ (D.baseChangeAtlas f).overlapToChart j i) ≫
        D.baseChangeChartInclusion f j := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeChartInclusion_fst]
    exact D.baseChangeChartMap_overlap f i j
  · simp only [Category.assoc, baseChangeChartInclusion_snd,
      overlapToChart_toBase, transition_toBase]

#print axioms baseChangeChartInclusion_overlap

end KltDP.Geometry.QuadraticCoverAtlas.Data
