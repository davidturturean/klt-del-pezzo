import KltDP.Geometry.AffineChartRingSquare
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso

/-!
# The original differential on an actual affine chart

These are the unchanged original chart differential and its invertibility.
Their use on actual sections does not require the separate whole-map square.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineChartDifferentialSquare

open SchemeKaehlerSheaf

section Chart

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} (hU : IsAffineOpen U) (n : ℕ)

/-- The original differential along the actual affine open-chart inclusion. -/
def chartMap :
    (schemeModulePullback hU.fromSpec).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n) ⟶
      SchemeExteriorPower.sheaf
        (baseRingSheaf (Spec.map (baseToAffineSectionsMap f hU))) n :=
  SchemeKaehlerExteriorPullbackTransport.map f hU.fromSpec
    (Spec.map (baseToAffineSectionsMap f hU))
    (Spec_map_baseToAffineSectionsMap f hU).symm n

theorem chartMap_isIso : IsIso (chartMap f hU n) :=
  SchemeKaehlerExteriorPullbackTransport.map_isIso f hU.fromSpec
    (Spec.map (baseToAffineSectionsMap f hU))
    (Spec_map_baseToAffineSectionsMap f hU).symm n

end Chart


end KltDP.Geometry.AffineChartDifferentialSquare
