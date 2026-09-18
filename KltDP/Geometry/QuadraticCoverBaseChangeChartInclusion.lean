import KltDP.Geometry.QuadraticCoverAffineBaseChangeAtlas
import KltDP.Geometry.QuadraticCoverMappedBaseChangeSquare
import KltDP.Geometry.PullbackChartLift

/-!
# The literal pulled atlas charts inside the original global pullback

The maps use the original `appLE` on the original branch atlas and the unit
one. The derived pullback square proves that these literal quadratic charts
are open subschemes of `pullback D.morphism f`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X Y : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)
  (f : Y ⟶ X) [Y.IsSeparated]

/-- The actual original coefficient map from one literal new chart to its old chart. -/
def baseChangeChartMap (i : D.BaseChangeIndex f) :
    (D.baseChangeAtlas f).chart i ⟶ D.chart (D.baseChangeOriginal f i) :=
  mappedRescaleMap
    (f.appLE (D.opens (D.baseChangeOriginal f i)) (D.baseChangeOpens f i)
      (D.baseChangeSubordinate f i)).hom
    (res X le_rfl (D.sections (D.baseChangeOriginal f i)))
    (res Y le_rfl ((D.baseChangeAtlas f).sections i)) 1
    (by simp only [Units.val_one, one_pow, one_mul, res_self,
      baseChangeAtlas, baseChangeSections])

/-- The literal new chart is the pullback along its actual affine base immersion. -/
theorem baseChangeChartMapIsPullback (i : D.BaseChangeIndex f) :
    IsPullback (D.baseChangeChartMap f i ≫ D.chartι (D.baseChangeOriginal f i))
      (toBase (res Y le_rfl ((D.baseChangeAtlas f).sections i))) D.morphism
      (((D.baseChangeAtlas f).affine i).fromSpec ≫ f) := by
  rw [← IsAffineOpen.Spec_map_appLE_fromSpec f (D.affine (D.baseChangeOriginal f i))
    ((D.baseChangeAtlas f).affine i) (D.baseChangeSubordinate f i)]
  exact (mappedRescaleIsPullback _ _ _ _ _).paste_horiz
    (D.chartIsPullback (D.baseChangeOriginal f i))

/-- The original universal map embeds this chart into the original global pullback. -/
def baseChangeChartInclusion (i : D.BaseChangeIndex f) :
    (D.baseChangeAtlas f).chart i ⟶ pullback D.morphism f :=
  PullbackChartLift.lift (D.baseChangeChartMapIsPullback f i)

@[simp, reassoc]
theorem baseChangeChartInclusion_fst (i : D.BaseChangeIndex f) :
    D.baseChangeChartInclusion f i ≫ pullback.fst D.morphism f =
      D.baseChangeChartMap f i ≫ D.chartι (D.baseChangeOriginal f i) :=
  PullbackChartLift.lift_fst (D.baseChangeChartMapIsPullback f i)

@[simp, reassoc]
theorem baseChangeChartInclusion_snd (i : D.BaseChangeIndex f) :
    D.baseChangeChartInclusion f i ≫ pullback.snd D.morphism f =
      (D.baseChangeAtlas f).chartToBase i :=
  PullbackChartLift.lift_snd (D.baseChangeChartMapIsPullback f i)

theorem baseChangeChartInclusionIsPullback (i : D.BaseChangeIndex f) :
    IsPullback (D.baseChangeChartInclusion f i)
      (toBase (res Y le_rfl ((D.baseChangeAtlas f).sections i)))
      (pullback.snd D.morphism f) ((D.baseChangeAtlas f).affine i).fromSpec :=
  PullbackChartLift.isPullback (D.baseChangeChartMapIsPullback f i)

instance baseChangeChartInclusion_isOpenImmersion (i : D.BaseChangeIndex f) :
    IsOpenImmersion (D.baseChangeChartInclusion f i) :=
  PullbackChartLift.isOpenImmersion (D.baseChangeChartMapIsPullback f i)

#print axioms baseChangeChartMapIsPullback
#print axioms baseChangeChartInclusion_isOpenImmersion

end KltDP.Geometry.QuadraticCoverAtlas.Data
