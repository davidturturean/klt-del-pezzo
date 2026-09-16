import KltDP.Geometry.ExteriorPowerFrameChart
import KltDP.Geometry.ModuleOpenOverEquivalence

/-!
# Exterior frames on the actual open subscheme

The proved equivalence between the open-subscheme module category and
its Over-site presentation transports the original exterior chart
isomorphism. The displayed comparison retains the actual restriction
functor and original unit, and records its image under that equivalence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ExteriorPowerFrameComparison

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
  (U : ι → X.Opens) {n : ℕ}
  (frame : ∀ (i : ι) (W : X.Opens), W ≤ U i →
    Basis (Fin n) Γ(X, W) (moduleSections M W))
  (hframe : ∀ (i : ι) {V W : X.Opens} (hVW : V ≤ W) (hW : W ≤ U i) (t : Fin n),
    moduleRestr M hVW (frame i W hW t) = frame i V (hVW.trans hW) t)
  (hU : (⨆ i, U i) = ⊤)

/-- The independent exterior sheaf has its original frame on the actual
open subscheme, through the accepted original restriction functor. -/
def exteriorOpenChartIsoOn (j : ι) {W : X.Opens} (hW : W ≤ U j) :
    (SchemeModuleRestriction.restriction W.ι).obj (SchemeExteriorPower.sheaf M n) ≅
      _root_.SheafOfModules.unit W.toScheme.ringCatSheaf :=
  (openToOverFunctor W).preimageIso
    (openToOverRestrictionIso W (SchemeExteriorPower.sheaf M n) ≪≫
      exteriorChartIsoOn M U frame hframe hU j hW ≪≫ openToOverUnitIso W)

/-- This transported frame is exactly the existing Over-site frame
with the two original restriction/unit comparisons. -/
theorem exteriorOpenChartIsoOn_hom_map (j : ι) {W : X.Opens} (hW : W ≤ U j) :
    (openToOverFunctor W).map (exteriorOpenChartIsoOn M U frame hframe hU j hW).hom =
      (openToOverRestrictionIso W (SchemeExteriorPower.sheaf M n)).hom ≫
        (exteriorChartIsoOn M U frame hframe hU j hW).hom ≫
          (openToOverUnitIso W).hom := by
  exact (openToOverFunctor W).map_preimage _

end KltDP.Geometry.ExteriorPowerFrameComparison
