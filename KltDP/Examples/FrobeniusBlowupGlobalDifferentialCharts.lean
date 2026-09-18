import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportSource
import KltDP.Examples.FrobeniusBlowupIntrinsicDifferentialPullback
import KltDP.Examples.FrobeniusBlowupIntrinsicDifferentialRightPullback

/-!
# The global point-blowup differential on the original Rees charts

The actual global blowdown has its original intrinsic top-differential map.
Its pullback to each actual Rees chart is the already normalized original
chart map, through the original pullback-composition comparison and proved
scheme-map equalities. The two selected original charts cover the blowup.
No local compatibility or canonical formula is supplied as a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusBlowupGlobalDifferentialCharts

open KltDP.Geometry KltDP.Geometry.AffineBlowup KltDP.Geometry.SchemeKaehlerSheaf
open FrobeniusBlowupContact FrobeniusBlowupSmooth

private theorem square_of_map_eq {C : Type*} [Category C] {A B D E : C}
    {a a' : A ⟶ B} {b b' : B ⟶ E} {c c' : A ⟶ D} {d d' : D ⟶ E}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d')
    (h : a' ≫ b' = c' ≫ d') : a ≫ b = c ≫ d := by
  cases ha
  cases hb
  cases hc
  cases hd
  exact h

variable {k : Type u} [Field k]

abbrev planeTop : (Spec (CommRingCat.of (planeRing k))).Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf (planeStructure (k := k))) 2

abbrev blowupTop : (scheme (centerIdeal (k := k))).Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf (blowupStructure (k := k))) 2

abbrev chartTop (a : centerIdeal (k := k)) :
    (Spec (CommRingCat.of (chartRing centerIdeal a))).Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf (chartStructure a)) 2

/-- The original global blowdown induces the original top-differential map. -/
def blowdownMap :
    (schemeModulePullback (toSpec (centerIdeal (k := k)))).obj (planeTop (k := k)) ⟶
      blowupTop (k := k) :=
  SchemeKaehlerExteriorPullbackTransport.map (planeStructure (k := k))
    (toSpec centerIdeal) blowupStructure rfl 2

/-- This is the actual chart-to-global differential map. -/
def chartGlobalMap (a : centerIdeal (k := k)) :
    (schemeModulePullback (chartι centerIdeal a)).obj (blowupTop (k := k)) ⟶
      chartTop a :=
  SchemeKaehlerExteriorPullbackTransport.map (blowupStructure (k := k))
    (chartι centerIdeal a) (chartStructure a) (chartι_blowupStructure a) 2

/-- The original chart ring map commutes with the original field structure. -/
theorem chartBase_structure (a : centerIdeal (k := k)) :
    Spec.map (CommRingCat.ofHom (chartBaseMap centerIdeal a)) ≫
        planeStructure (k := k) = chartStructure a := by
  rw [planeStructure, chartStructure, ← Spec.map_comp]
  rfl

/-- The intrinsic differential map along the original plane-to-chart ring map. -/
def chartBlowdownMap (a : centerIdeal (k := k)) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom
      (chartBaseMap centerIdeal a)))).obj (planeTop (k := k)) ⟶ chartTop a :=
  SchemeKaehlerExteriorPullbackTransport.map (planeStructure (k := k))
    (Spec.map (CommRingCat.ofHom (chartBaseMap centerIdeal a)))
    (chartStructure a) (chartBase_structure a) 2

/-- The original pullback composition identifies the two actual plane sources. -/
def chartSourceIso (a : centerIdeal (k := k)) :
    (schemeModulePullback (chartι centerIdeal a)).obj
        ((schemeModulePullback (toSpec centerIdeal)).obj (planeTop (k := k))) ≅
      (schemeModulePullback (Spec.map (CommRingCat.ofHom
        (chartBaseMap centerIdeal a)))).obj (planeTop (k := k)) :=
  SchemeKaehlerExteriorPullbackTransport.sourceIso (planeStructure (k := k))
    (toSpec centerIdeal) (chartι centerIdeal a)
    (Spec.map (CommRingCat.ofHom (chartBaseMap centerIdeal a))) (chartι_toSpec centerIdeal a) 2

private def blowdownMap_chart_proof (k : Type u) [Field k] (a : centerIdeal (k := k)) :=
  SchemeKaehlerExteriorPullbackTransport.map_comp_sourceIso (planeStructure (k := k))
    (toSpec centerIdeal) (chartι centerIdeal a) blowupStructure rfl
    (Spec.map (CommRingCat.ofHom (chartBaseMap centerIdeal a)))
    (chartι_toSpec centerIdeal a) (chartStructure a)
    (chartι_blowupStructure a) (chartBase_structure a) 2

private theorem blowdownMap_chart_eq (a : centerIdeal (k := k)) :
    (schemeModulePullback (chartι centerIdeal a)).map (blowdownMap (k := k)) =
      (schemeModulePullback (chartι centerIdeal a)).map
        (SchemeKaehlerExteriorPullbackTransport.map (planeStructure (k := k))
          (toSpec centerIdeal) blowupStructure rfl 2) := rfl

private theorem chartGlobalMap_eq (a : centerIdeal (k := k)) :
    chartGlobalMap a =
      SchemeKaehlerExteriorPullbackTransport.map (blowupStructure (k := k))
        (chartι centerIdeal a) (chartStructure a) (chartι_blowupStructure a) 2 := rfl

private theorem chartSourceIso_hom_eq (a : centerIdeal (k := k)) :
    (chartSourceIso a).hom =
      (SchemeKaehlerExteriorPullbackTransport.sourceIso (planeStructure (k := k))
        (toSpec centerIdeal) (chartι centerIdeal a)
        (Spec.map (CommRingCat.ofHom (chartBaseMap centerIdeal a)))
        (chartι_toSpec centerIdeal a) 2).hom := rfl

private theorem chartBlowdownMap_eq (a : centerIdeal (k := k)) :
    chartBlowdownMap a =
      SchemeKaehlerExteriorPullbackTransport.map (planeStructure (k := k))
        (Spec.map (CommRingCat.ofHom (chartBaseMap centerIdeal a)))
        (chartStructure a) (chartBase_structure a) 2 := rfl

/-- The whole global map restricts to the whole original chart map. -/
theorem blowdownMap_chart (a : centerIdeal (k := k)) :
    (schemeModulePullback (chartι centerIdeal a)).map (blowdownMap (k := k)) ≫
        chartGlobalMap a = (chartSourceIso a).hom ≫ chartBlowdownMap a :=
  square_of_map_eq (blowdownMap_chart_eq a) (chartGlobalMap_eq a)
    (chartSourceIso_hom_eq a) (chartBlowdownMap_eq a) (blowdownMap_chart_proof k a)

/-- The first map is exactly the already normalized original left-chart map. -/
theorem chartBlowdownMap_centerU :
    chartBlowdownMap (centerU (k := k)) =
      FrobeniusBlowupIntrinsicDifferentialPullback.leftMap (k := k) := rfl

/-- The second map is exactly the already normalized original right-chart map. -/
theorem chartBlowdownMap_centerV :
    chartBlowdownMap (centerV (k := k)) =
      FrobeniusBlowupIntrinsicDifferentialRightPullback.rightMap (k := k) := rfl

/-- The original two chart opens, ready for the accepted monic-factor cover theorem. -/
abbrev originalChartOpen (i : Bool) : (scheme (centerIdeal (k := k))).Opens :=
  chartOpen centerIdeal (centerGenerator i)

theorem originalChartOpen_cover : (⨆ i, originalChartOpen (k := k) i) = ⊤ :=
  iSup_chartOpen_generators centerIdeal centerGenerator span_centerGenerator

theorem mem_originalChartOpen (x : scheme (centerIdeal (k := k))) :
    ∃ i, x ∈ originalChartOpen (k := k) i := by
  have hx : x ∈ (⨆ i, originalChartOpen (k := k) i) := by
    rw [originalChartOpen_cover]
    trivial
  simpa only [Opens.mem_iSup] using hx

end KltDP.Examples.FrobeniusBlowupGlobalDifferentialCharts
