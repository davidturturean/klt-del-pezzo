import KltDP.Examples.FrobeniusBlowupGlobalDifferentialCharts
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso

/-!
# The original global top sheaf on the actual Rees affine charts

Open immersion of each original Rees chart makes its original differential
map invertible. The comparison retains exactly the map used in the global
blowdown composition diagram, through the original structure-map equality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusBlowupGlobalExteriorCharts

open KltDP.Geometry KltDP.Geometry.AffineBlowup KltDP.Geometry.SchemeKaehlerSheaf
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupGlobalDifferentialCharts

variable {k : Type u} [Field k]

/-- The actual differential comparison, made invertible by the original chart open immersion. -/
def chartGlobalIso (a : centerIdeal (k := k)) :
    (schemeModulePullback (chartι centerIdeal a)).obj (blowupTop (k := k)) ≅ chartTop a := by
  letI : IsIso (chartGlobalMap a) :=
    SchemeKaehlerExteriorPullbackTransport.map_isIso (blowupStructure (k := k))
      (chartι centerIdeal a) (chartStructure a) (chartι_blowupStructure a) 2
  exact asIso (chartGlobalMap a)

/-- Its forward map is the whole original chart map, with no new frame choice. -/
theorem chartGlobalIso_hom (a : centerIdeal (k := k)) :
    (chartGlobalIso a).hom = chartGlobalMap a := rfl

/-- The original global blowdown diagram holds through this actual chart isomorphism. -/
theorem blowdownMap_chartIso (a : centerIdeal (k := k)) :
    (schemeModulePullback (chartι centerIdeal a)).map (blowdownMap (k := k)) ≫
        (chartGlobalIso a).hom = (chartSourceIso a).hom ≫ chartBlowdownMap a := by
  rw [chartGlobalIso_hom]
  exact blowdownMap_chart a

end KltDP.Examples.FrobeniusBlowupGlobalExteriorCharts
