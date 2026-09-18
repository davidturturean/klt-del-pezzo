import KltDP.Examples.FrobeniusBlowupCanonicalFactorCharts
import KltDP.Geometry.SchemeModuleMonicFactorOnCover

/-!
# The original global canonical factor on the point blowup

The actual affine-chart factors are transported through the original Proj
chart isomorphisms to the two original covering opens. Their already proved
whole-map equations give the inputs to the accepted monic-factor theorem.
The resulting global isomorphism retains the original blowdown differential.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusBlowupCanonicalGlobalFactor

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth
open FrobeniusBlowupGlobalDifferentialCharts FrobeniusBlowupGlobalCanonicalTarget
open FrobeniusBlowupCanonicalFactorCharts

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private def transportFactor {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (P : D ⥤ E) (G : C ⥤ E) (c : F ⋙ P ≅ G)
    {M N : C} (e : F.obj M ≅ F.obj N) : G.obj M ≅ G.obj N :=
  (c.app M).symm ≪≫ P.mapIso e ≪≫ c.app N

private theorem transportFactor_comp {C D E : Type*}
    [Category C] [Category D] [Category E]
    (F : C ⥤ D) (P : D ⥤ E) (G : C ⥤ E) (c : F ⋙ P ≅ G)
    {M N Q : C} (e : F.obj M ≅ F.obj N) (b : N ⟶ Q) (a : M ⟶ Q)
    (he : e.hom ≫ F.map b = F.map a) :
    (transportFactor F P G c e).hom ≫ G.map b = G.map a := by
  simp only [transportFactor, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [← c.hom.naturality b]
  change c.inv.app M ≫ P.map e.hom ≫ P.map (F.map b) ≫ c.hom.app Q = _
  rw [← Functor.map_comp_assoc, he]
  change c.inv.app M ≫ (F ⋙ P).map a ≫ c.hom.app Q = _
  rw [c.hom.naturality a, Iso.inv_hom_id_app_assoc]

variable {k : Type u} [Field k]

/-- The original Proj affine-chart isomorphism recovers its original open inclusion. -/
theorem chartIso_hom_chartι (a : centerIdeal (k := k)) :
    (chartIso centerIdeal a).hom ≫ chartι centerIdeal a = (chartOpen centerIdeal a).ι := by
  change (chartIso centerIdeal a).hom ≫
    ((chartIso centerIdeal a).inv ≫ (chartOpen centerIdeal a).ι) = _
  rw [Iso.hom_inv_id_assoc]

/-- The original pullback composition along that same geometric equality. -/
def chartOpenPullbackIso (a : centerIdeal (k := k)) :
    schemeModulePullback (chartι centerIdeal a) ⋙
        schemeModulePullback (chartIso centerIdeal a).hom ≅
      schemeModulePullback (chartOpen centerIdeal a).ι :=
  schemeModulePullbackCompIso (chartIso centerIdeal a).hom (chartι centerIdeal a) ≪≫
    eqToIso (congrArg schemeModulePullback (chartIso_hom_chartι a))

/-- The actual factor on an original covering open, transported from its original affine chart. -/
def openCanonicalFactorIso (i : Bool) :
    (schemeModulePullback (originalChartOpen (k := k) i).ι).obj
        ((schemeModulePullback (toSpec centerIdeal)).obj (planeTop (k := k))) ≅
      (schemeModulePullback (originalChartOpen (k := k) i).ι).obj
        (exceptionalCanonicalTensor (k := k)) :=
  transportFactor (schemeModulePullback (chartι centerIdeal (centerGenerator i)))
    (schemeModulePullback (chartIso centerIdeal (centerGenerator i)).hom)
    (schemeModulePullback (originalChartOpen (k := k) i).ι)
    (chartOpenPullbackIso (centerGenerator i)) (chartCanonicalFactorIso i)

/-- The original open factors retain the same original global inclusion and differential. -/
theorem openCanonicalFactorIso_comp (i : Bool) :
    (openCanonicalFactorIso (k := k) i).hom ≫
        (schemeModulePullback (originalChartOpen (k := k) i).ι).map
          (exceptionalCanonicalInclusion (k := k)) =
      (schemeModulePullback (originalChartOpen (k := k) i).ι).map
        (blowdownMap (k := k)) :=
  transportFactor_comp (schemeModulePullback (chartι centerIdeal (centerGenerator i)))
    (schemeModulePullback (chartIso centerIdeal (centerGenerator i)).hom)
    (schemeModulePullback (originalChartOpen (k := k) i).ι)
    (chartOpenPullbackIso (centerGenerator i)) (chartCanonicalFactorIso i)
    (exceptionalCanonicalInclusion (k := k)) (blowdownMap (k := k))
    (chartCanonicalFactorIso_factor i)

/-- The actual global isomorphism is the accepted monic factor of the original differential. -/
def canonicalBlowupIso :
    (schemeModulePullback (toSpec centerIdeal)).obj (planeTop (k := k)) ≅
      exceptionalCanonicalTensor (k := k) := by
  letI := exceptionalCanonicalInclusion_mono (k := k)
  exact schemeModuleMonicFactorIsoOnOpenCover (originalChartOpen (k := k))
    (mem_originalChartOpen (k := k)) (exceptionalCanonicalInclusion (k := k))
    (blowdownMap (k := k)) (openCanonicalFactorIso (k := k))
    (openCanonicalFactorIso_comp (k := k))

/-- The actual global isomorphism factors precisely the original blowdown differential. -/
theorem canonicalBlowupIso_comp :
    (canonicalBlowupIso (k := k)).hom ≫ exceptionalCanonicalInclusion (k := k) =
      blowdownMap (k := k) := by
  letI := exceptionalCanonicalInclusion_mono (k := k)
  exact schemeModuleMonicFactorIsoOnOpenCover_comp (originalChartOpen (k := k))
    (mem_originalChartOpen (k := k)) (exceptionalCanonicalInclusion (k := k))
    (blowdownMap (k := k)) (openCanonicalFactorIso (k := k))
    (openCanonicalFactorIso_comp (k := k))

end KltDP.Examples.FrobeniusBlowupCanonicalGlobalFactor
