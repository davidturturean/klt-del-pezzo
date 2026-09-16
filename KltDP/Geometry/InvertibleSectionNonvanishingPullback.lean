import KltDP.Geometry.InvertibleSectionNonvanishingOpen
import KltDP.Geometry.InvertibleSheafSectionPowersPullback
import KltDP.Geometry.SheafSectionPullbackCoefficient

/-!
# Nonvanishing opens under actual scheme pullback

Pull back the original local frames and evaluate the original adjunction-unit
section in them. The accepted double-pullback coefficient formula and inverse
open-section map give the literal pulled coefficient. The actual nonvanishing
open therefore pulls back along every original scheme morphism.

Neither a chosen compatibility of frames, flatness, coherence nor a hypothesis
about the nonvanishing opens is needed. This supplies the common open for local
twisted extensions; it makes no global gluing or ampleness assertion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSectionNonvanishingPullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitExtraction RationalTreePicard
open InvertibleSectionNonvanishingOpen InvertibleSheafSectionPowersPullback

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
  (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)

private theorem preimage_chart_cover (y : Y) : ∃ i : t.I, y ∈ f ⁻¹ᵁ t.X i := by
  have h : f.base y ∈ (⨆ i, t.X i) := by
    rw [chartOpens_cover X M t]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp h
  exact ⟨i, hi⟩

/-- The actual pulled local frames, on the original preimages of the
original chart opens, give an atlas of the actual pulled sheaf. -/
def pullbackAtlas :
    KltDP.SheafOfModules.LocalTrivializations (R := Y.ringCatSheaf)
      ((schemeModulePullback f).obj M) :=
  localTrivializationsOfOpenCharts ((schemeModulePullback f).obj M)
    (fun i : t.I => f ⁻¹ᵁ t.X i) (preimage_chart_cover f M t)
    (fun i => openChartOfPullback ((schemeModulePullback f).obj M) (f ⁻¹ᵁ t.X i)
      (pulledChartIso f M (t.X i)
        (chartPullbackUnitIsoOf (t.X i) M (t.unitIso i).symm)))

set_option maxHeartbeats 800000 in
/-- The coefficient of the actual pulled compatible section is the
original chart coefficient through the actual structural section map. -/
theorem chartCoefficient_pullback (s : M.sections) (i : t.I) :
    chartCoefficient Y ((schemeModulePullback f).obj M) (pullbackAtlas f M t)
        (InvertibleSheafSectionPowersPullback.pullbackSection f M s) i =
      f.app (t.X i) (chartCoefficient X M t s i) := by
  let U := t.X i
  let Q := f ⁻¹ᵁ U
  let N := (schemeModulePullback f).obj M
  let τ (j : t.I) := pulledChartIso f M (t.X j)
    (chartPullbackUnitIsoOf (t.X j) M (t.unitIso j).symm)
  have h := chartEquiv_ofPullbackCharts_apply N
    (fun j : t.I => f ⁻¹ᵁ t.X j) (preimage_chart_cover f M t) τ i
    (pulledSection f M U (s.val (op U)))
  have hc := SheafSectionPullbackCoefficient.doublePulled_frame_coefficient
    f M U (t.unitIso i) (s.val (op U))
  exact (congrArg (chartEquiv Y N (pullbackAtlas f M t) i le_rfl)
    (pullbackSection_val f M s U)).trans
    (h.trans ((congrArg (fun a => openSectionsInv Q le_rfl a) hc).trans
      (openSectionsInv_app Q le_rfl
        (f.app U (chartCoefficient X M t s i)))))

/-- The nonvanishing open of the original pulled section is precisely
the inverse image of the original section's nonvanishing open. -/
theorem nonvanishingOpen_pullback (L : InvertibleSheaf X) (s : L.obj.sections) :
    nonvanishingOpen Y (pullbackInvertibleSheaf f L) (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) =
      f ⁻¹ᵁ nonvanishingOpen X L s := by
  let d := pullbackAtlas f L.obj L.localTrivializations
  have hd : nonvanishingOpen Y (pullbackInvertibleSheaf f L) (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) =
      nonvanishingOpenOfAtlas Y ((schemeModulePullback f).obj L.obj) d
        (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) :=
    nonvanishingOpenOfAtlas_eq Y ((schemeModulePullback f).obj L.obj)
      (pullbackInvertibleSheaf f L).localTrivializations d (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s)
  rw [hd]
  apply le_antisymm
  · intro y hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    change y ∈ Y.basicOpen (chartCoefficient Y ((schemeModulePullback f).obj L.obj)
      (pullbackAtlas f L.obj L.localTrivializations) (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) i) at hi
    rw [chartCoefficient_pullback, ← Scheme.preimage_basicOpen] at hi
    change f.base y ∈ (⨆ i, X.basicOpen
      (chartCoefficient X L.obj L.localTrivializations s i))
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro y hy
    change f.base y ∈ (⨆ i, X.basicOpen
      (chartCoefficient X L.obj L.localTrivializations s i)) at hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    apply Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    change y ∈ Y.basicOpen (chartCoefficient Y ((schemeModulePullback f).obj L.obj)
      (pullbackAtlas f L.obj L.localTrivializations) (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) i)
    rw [chartCoefficient_pullback, ← Scheme.preimage_basicOpen]
    exact hi

end KltDP.Geometry.InvertibleSectionNonvanishingPullback
