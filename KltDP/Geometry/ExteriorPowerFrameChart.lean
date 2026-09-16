import KltDP.Geometry.ExteriorPowerFrameComparisonUnit

/-!
# Actual chart trivializations of the independent exterior sheaf

The original exterior/frame comparison and the existing transition-line
chart isomorphism give an actual isomorphism on the Over site of every
frame subopen. Its value on each original wedge is its determinant.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.ChartFrameAtlasSheaf
open KltDP.Geometry.TransitionUnitGluing

universe u

namespace KltDP.Geometry.ExteriorPowerFrameComparison

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
  (U : ι → X.Opens) {n : ℕ}
  (frame : ∀ (i : ι) (W : X.Opens), W ≤ U i →
    Basis (Fin n) Γ(X, W) (moduleSections M W))
  (hframe : ∀ (i : ι) {V W : X.Opens} (hVW : V ≤ W) (hW : W ≤ U i) (t : Fin n),
    moduleRestr M hVW (frame i W hW t) = frame i V (hVW.trans hW) t)
  (hU : (⨆ i, U i) = ⊤)

/-- The original exterior sheaf, restricted to an actual frame subopen,
is isomorphic to the original structure module on that Over site. -/
def exteriorChartIsoOn (j : ι) {W : X.Opens} (hW : W ≤ U j) :
    (SchemeExteriorPower.sheaf M n).over W ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over W) :=
  (_root_.SheafOfModules.overFunctor X.ringCatSheaf W).mapIso
      (sheafIso M U frame hframe hU) ≪≫
    chartIsoOn X U (transitionUnit U (moduleSections M) frame)
      (transitionUnit_isCocycle (U := U) (L := moduleSections M)
        (restr := moduleRestr M) (frame := frame) (hframe := hframe)) j hW

/-- This actual sheaf isomorphism sends every original local wedge to
its determinant in the original restricted frame. -/
theorem exteriorChartIsoOn_hom_wedge (j : ι) {W : X.Opens} (hW : W ≤ U j)
    (V : (Over W)ᵒᵖ) (v : Fin n → moduleSections M V.unop.left) :
    (exteriorChartIsoOn M U frame hframe hU j hW).hom.val.app V
        (SchemeExteriorPower.wedge M n V.unop.left v) =
      (frame j V.unop.left (V.unop.hom.le.trans hW)).det v := by
  change trivialization X U (transitionUnit U (moduleSections M) frame)
      (transitionUnit_isCocycle (U := U) (L := moduleSections M)
        (restr := moduleRestr M) (frame := frame) (hframe := hframe)) j
      (V.unop.hom.le.trans hW)
      ((sheafIso M U frame hframe hU).hom.val.app (op V.unop.left)
        (SchemeExteriorPower.wedge M n V.unop.left v)) = _
  exact trivialization_sheafIso_wedge M U frame hframe hU j
    (V.unop.hom.le.trans hW) v

/-- The wedge of the chosen actual frame is the unit section in this
same sheaf trivialization. -/
theorem exteriorChartIsoOn_hom_frame (j : ι) {W : X.Opens} (hW : W ≤ U j)
    (V : (Over W)ᵒᵖ) :
    (exteriorChartIsoOn M U frame hframe hU j hW).hom.val.app V
        (SchemeExteriorPower.wedge M n V.unop.left
          (frame j V.unop.left (V.unop.hom.le.trans hW))) =
      (1 : Γ(X, V.unop.left)) := by
  rw [exteriorChartIsoOn_hom_wedge, Basis.det_self]

end KltDP.Geometry.ExteriorPowerFrameComparison
